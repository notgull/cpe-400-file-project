# John Nunley
# CPE 400
# Course Project
# Arslan

"""
This application is the both a client and server for the CPE 400 course project, where we
implement an application that sends a folder's worth of files over the network to the server.

Two types of ports are opened:

- The directive port (only one), which is used to send instructions to the server and receive replies
  to those instructions.
- The data ports (several), which are used to send files to the server.

Things that need to happen:
- Client sends server the files that need to be sent.
- Server sends client the ports that the client uses.
- Client indicates that it is sending a file, alongside the file's name and size, and the data port that
  it is using.
- Once the client has sent all of the packets (of size BLOCK_SIZE) over the data port, it sends a "file done"
  message to the server.
- In response, the server sends one of the following:
  - An "all is well" message, indicating that the file was received successfully.
  - A request for some packets that were not received earlier. In response, the client sends more packets,
    and sends another "file done" message, rinse and repeat.
- Connection is implicitly closed when the server has confirmed reception of all files.

General Guide to this file:

- Directives are sent by first converting them into a map, then converting them to JSON. They are sent over
  the directive port as text. All directives and replies derive the WireRepr class.
- Files are converted into FilePackets to be used used in FilePacketSender/FilePacketReceiver.
- The BufferedSocket is used to send/read WireRepr types.
"""

from abc import ABC, abstractmethod, abstractclassmethod
from typing import Any, BinaryIO, Callable, Container, Iterable, Mapping, Optional, Sequence, Tuple, TypeVar

import array
import json
import random
import select
import socket
import struct

# constants

BLOCK_SIZE = 2**14
COUNT_AT_A_TIME = 2**10
TIMEOUT = 30

# request types

class WireRepr(ABC):
    """
    Base class for objects that can be serialized and sent over
    "the wire". These objects serialize themselves into a map,
    which is then converted into JSON.
    """

    @abstractmethod
    def to_wire(self) -> Mapping[str, Any]:
        """
        Serialize the object into a map.
        """
        pass

    @abstractclassmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'WireRepr':
        """
        Deserialize the object from a map.
        """
        pass

class OpenRequest(WireRepr):
    """
    The initial request sent from the client to the server before
    file transfers take place.

    Contains the number of files, the names of the files, and the
    number of concurrent transfers we want to do. Also contains
    computed checksums for the files.
    """

    filenames: Sequence[str]
    num_concurrent: int
    checksums: Mapping[str, Sequence[int]]

    def __init__(self, filenames: Sequence[str], num_concurrent: int, checksums: Mapping[str, Sequence[int]]) -> None:
        self.filenames = filenames
        self.num_concurrent = num_concurrent
        self.checksums = checksums

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'open_request',
            'filenames': self.filenames,
            'num_concurrent': self.num_concurrent,
            'checksums': self.checksums
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'OpenRequest':
        if wire['type'] != 'open_request':
            raise ValueError('Expected open_request, got {}'.format(wire['type']))

        return OpenRequest(
            wire['filenames'],
            wire['num_concurrent'],
            wire['checksums']
        )

class OpenReply(WireRepr):
    """
    The reply from the server to an OpenRequest.

    Contains the ports that the server opened for file transfer and
    the real number of concurrent accesses.
    """

    ports: Sequence[int]
    num_concurrent: int

    def __init__(self, ports: Sequence[int], num_concurrent: int) -> None:
        self.ports = ports
        self.num_concurrent = num_concurrent

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'open_reply',
            'ports': self.ports,
            'num_concurrent': self.num_concurrent
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'OpenReply':
        if wire['type'] != 'open_reply':
            raise ValueError('Expected open_reply, got {}'.format(wire['type']))

        return OpenReply(
            wire['ports'],
            wire['num_concurrent']
        )

class SendFileRequest(WireRepr):
    """
    Tell the server that we are now sending a file.

    Contains the name of the file, the size (in bytes) of
    the file, and the port we're sending it over.
    """

    filename: str
    size: int
    port: int

    def __init__(self, filename: str, size: int, port: int) -> None:
        self.filename = filename
        self.size = size
        self.port = port

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'begin_send_file',
            'filename': self.filename,
            'size': self.size,
            'port': self.port
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'SendFileRequest':
        if wire['type'] != 'begin_send_file':
            raise ValueError('Expected begin_send_file, got {}'.format(wire['type']))

        return cls(
            wire['filename'],
            wire['size'],
            wire['port']
        )

class FinishedFileRequest(WireRepr):
    """
    Tell the server that we've finished sending the specified file.

    Contains the filename we just finished sending.
    """

    filename: str

    def __init__(self, filename: str) -> None:
        self.filename = filename

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'finished_send_file',
            'filename': self.filename
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'FinishedFileRequest':
        if wire['type'] != 'finished_send_file':
            raise ValueError('Expected finished_send_file, got {}'.format(wire['type']))

        return cls(
            wire['filename']
        )

class SendFileReply(WireRepr):
    """
    Tell the client that we've received the entire file.
    """

    filename: str

    def __init__(self, filename: str) -> None:
        self.filename = filename

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'end_send_file',
            'filename': self.filename
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'SendFileReply':
        if wire['type'] != 'end_send_file':
            raise ValueError('Expected end_send_file, got {}'.format(wire['type']))

        return cls(
            wire['filename']
        )

class ResendPacketsReply(WireRepr):
    """
    Tell the client that they need to resend the given file packets.

    Includes the name of the file and the list of packets we did not
    receive.
    """

    filename: str
    packets: Sequence[int]

    def __init__(self, filename: str, packets: Sequence[int]) -> None:
        self.filename = filename
        self.packets = packets

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'resend_packets',
            'filename': self.filename,
            'packets': self.packets
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'ResendPacketsReply':
        if wire['type'] != 'resend_packets':
            raise ValueError('Expected resend_packets, got {}'.format(wire['type']))

        return cls(
            wire['filename'],
            wire['packets']
        )

general_flow = """

Here is my idea for the general flow of the program:

- Over the TCP socket, the client sends an OpenRequest to the server.
- The server replies with an OpenReply.
- The client sends a SendFileRequest for each file it wants to send.
- The client then sends files over the UDP sockets.
- The server receives the files and sends back a SendFileReply
- If a packet was missed, the server sends back a ResendPacketsReply
- Connection is implicitly over once the last file is sent

"""

# file packet
class FilePacketHeader:
    """
    The header of a file packet, that contains:

    a). A unique sequence number.
    b). The size of the file packet.
    """

    seq_num: int
    size: int

    def __init__(self, seq_num: int, size: int) -> None:
        self.seq_num = seq_num
        self.size = size

    def to_bytes(self) -> bytes:
        return struct.pack('<II', self.seq_num, self.size)

    @classmethod
    def from_bytes(cls, data: bytes) -> 'FilePacketHeader':
        seq_num, size = struct.unpack('<II', data)
        return cls(seq_num, size)

    @classmethod
    def size(cls) -> int:
        return struct.calcsize('<II')

class FilePacket:
    """
    The total file packet. 
    """

    header: FilePacketHeader
    data: bytes

    def __init__(self, header: FilePacketHeader, data: bytes) -> None:
        self.header = header
        self.data = data

    def to_bytes(self) -> bytes:
        return self.header.to_bytes() + self.data

    @classmethod
    def from_bytes(cls, data: bytes) -> 'FilePacket':
        header = FilePacketHeader.from_bytes(data[:8])
        data = data[8:]
        return cls(header, data)

# socket functions

WireType = TypeVar("WireType")

class BufferedSocket:
    """
    A wrapper around a (TCP?) socket with an attached read buffer.
    """

    sock: socket.socket
    buf: bytes
    count_at_a_time: int

    def __init__(self, sock: socket.socket) -> None:
        self.sock = sock
        self.buf = b''
        self.count_at_a_time = COUNT_AT_A_TIME

        # set our socket to be nonblocking
        self.sock.setblocking(False)

    def send_data(self, data: bytes) -> None:
        """
        Send data to the socket.
        """

        # send as much as we can until we get a BlockingIOError,
        # then use select.select() to poll until it's ready again
        while True:
            try:
                bytes_sent = self.sock.send(data)
                
                # remove bytes_sent bytes from the start of data
                data = data[bytes_sent:]

                # if we've sent all the data, we're done
                if len(data) == 0:
                    return
            except BlockingIOError:
                pass

            # wait for the socket to be ready
            ready = select.select([], [self.sock], [], TIMEOUT)
            if not ready[1]:
                raise TimeoutError('Socket not ready')

    def recv_data_until(self, until: Callable[[bytes], Optional[Tuple[int, int]]]) -> bytes:
        """
        Receive bytes into our buffer until the callback is able to extract a specific
        set of bytes.
        """

        # keep receiving until we get the bytes we want
        while True:
            # receive some data
            try:
                data = self.sock.recv(self.count_at_a_time)
            except BlockingIOError:
                data = b''

            # if we received no data, the socket is closed
            if len(data) == 0:
                raise ConnectionResetError('Socket closed')

            # add the data to our buffer
            self.buf += data

            # try to extract the bytes we want
            extracted = until(self.buf)
            if extracted is not None:
                # remove the bytes we extracted from the buffer
                self.buf = self.buf[extracted[1]:]
                return self.buf[:extracted[0]]

            # wait for the socket to be ready
            ready = select.select([self.sock], [], [], TIMEOUT)
            if not ready[0]:
                raise TimeoutError('Socket not ready')

    def recv_json(self) -> Mapping[str, Any]:
        """
        Receive a JSON object from the socket.
        """

        def decoder(packet: bytes) -> Optional[Tuple[int, int]]:
            """
            Count the opening and closing braces until we reach the final
            closing brace
            """

            # count the opening and closing braces
            opening_braces = 0
            closing_braces = 0
            for i, byte in enumerate(packet):
                if byte == b'{':
                    opening_braces += 1
                elif byte == b'}':
                    closing_braces += 1

                # if we've reached the final closing brace, we're done
                if opening_braces == closing_braces and opening_braces != 0:
                    return (0, i)

            # we didn't reach the final closing brace
            return None

        # receive the JSON object
        data = self.recv_data_until(decoder)

        # return the JSON object
        return json.loads(data.decode('utf-8'))

    def recv_wiretype(self, ty) -> WireRepr:
        """
        Receive a wire-encoded object from the buffer.
        """

        map = self.recv_json()
        return ty.from_wire(map)
    
    def send_wiretype(self, obj: WireRepr) -> None:
        """
        Send a wire-encoded object across the buffer.
        """

        self.send_data(json.dumps(obj.to_wire()).encode('utf-8'))

    def recv_many_wiretype(self, *args) -> Any:
        """
        Receive one of many wire-encoded types.
        """

        map = self.recv_json()

        # try all of the args as constructors until we find one that
        # doesn't die
        for ty in args:
            try:
                return ty.from_wire(map)
            except:
                pass

class FilePacketSender:
    """
    A wrapper around a (UDP?) socket that sends file packets as
    datagrams.
    """

    sock: socket.socket
    seq_num: int
    file_reader: BinaryIO
    host: str
    port: int

    def __init__(self, sock: socket.socket, file_reader: BinaryIO, host: str, port: int) -> None:
        self.sock = sock
        self.seq_num = 0
        self.file_reader = file_reader
        self.host = host
        self.port = port

    def send(self, sequences: Optional[Container[int]]) -> None:
        """
        Send this file across the UDP socket.

        If `sequences` is not `None`, only send those specific sequence numbers.
        """

        # keep sending packets until we've sent all the data
        while True:
            # read the next packet
            packet = self.read_packet()

            # if we've reached the end of the file, we're done
            if packet is None:
                # reset sequence number and reutrn
                self.seq_num = 0
                return

            # check the sequence number
            if sequences is not None and packet.header.seq_num not in sequences:
                continue

            # send the packet
            self.send_packet(packet)

    def read_packet(self) -> Optional[FilePacket]:
        """
        Read BLOCK_SIZE bytes from the file (or less), add the packet header,
        and return.
        """

        # read the next block of data
        data = self.file_reader.read(BLOCK_SIZE)

        # if we've reached the end of the file, we're done
        if len(data) == 0:
            return None

        # create the packet
        packet = FilePacket(FilePacketHeader(self.seq_num, len(data)), data)

        # increment the sequence number
        self.seq_num += 1

        return packet

    def send_packet(self, packet: FilePacket) -> None:
        """
        Send a packet across the UDP socket.
        """

        # send the packet
        self.sock.sendto(packet.to_bytes(), (self.host, self.port))

class FilePacketReader:
    """
    A wrapper around a UDP socket that reads in packets and writes them
    to a file.
    """

    sock: socket.socket
    file_writer: BinaryIO

    def __init__(self, sock: socket.socket, file_writer: BinaryIO) -> None:
        self.sock = sock
        self.file_writer = file_writer

    def read_packet(self) -> Optional[FilePacket]:
        """
        Read a packet from the socket.
        """
        # receive the packet
        data, addr = self.sock.recvfrom(BLOCK_SIZE + FilePacketHeader.size())

        # parse the packet
        packet = FilePacket.from_bytes(data)

        # write the packet to the file
        self.file_writer.write(packet.data)

        return packet

    def write_packet(self, packet: FilePacket) -> None:
        """
        Write a file packet that we received.
        """

        # move the file writer to the right position
        self.file_writer.seek(packet.header.seq_num * BLOCK_SIZE)

        # write the packet to the file
        self.file_writer.write(packet.data)

    def read(self) -> Iterable[int]:
        """
        Read in packets from the UDP socket. Returns the sequence numbers
        that we receive.
        """

        # keep reading packets until we've received all the data
        while True:
            # read the next packet
            packet = self.read_packet()

            # if we've reached the end of the file, we're done
            if packet is None:
                return

            # yield the sequence number
            yield packet.header.seq_num

            # write the packet to the file
            self.write_packet(packet)

# client operations

class FileInfo:
    """
    Information about a file
    """
    pass

class Client:
    """
    The client state for the file transfer mechanism.
    """

    files: Mapping[str, FileInfo]

def main():
    # TODO
    pass

if __name__ == "__main__":
    main()