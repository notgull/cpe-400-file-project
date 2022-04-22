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
import multiprocessing
from pathlib import Path
from typing import Any, BinaryIO, Callable, Container, Iterable, Mapping, Optional, Sequence, Tuple, TypeVar

import array
import hashlib
import json
import os
import random
import select
import socket
import struct
import sys

# constants

BLOCK_SIZE = 2**14
COUNT_AT_A_TIME = 2**10
DEFAULT_PORT = 27850
DEFAULT_FILE_PORT = 27851
TIMEOUT = 30

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

# argument parsing

def find_argument(arg: str) -> Optional[str]:
    """
    Gets the value of an argument from the command line.
    """

    for i in range(1, len(sys.argv)):
        if sys.argv[i] == arg:
            if i + 1 < len(sys.argv):
                return sys.argv[i + 1]
            else:
                return None
    return None

T = TypeVar("T")

def unwrap_or(val: Optional[T], default: T) -> T:
    """
    Take an optional value and return it, or return a default value.
    """

    if val is None:
        return default
    else:
        return val

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
    checksums: Mapping[str, bytes]

    def __init__(self, filenames: Sequence[str], num_concurrent: int, checksums: Mapping[str, bytes]) -> None:
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
    last_sequence: int

    def __init__(self, filename: str, last_sequence: int) -> None:
        self.filename = filename
        self.last_sequence = last_sequence

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'finished_send_file',
            'filename': self.filename,
            'last_sequence': self.last_sequence
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'FinishedFileRequest':
        if wire['type'] != 'finished_send_file':
            raise ValueError('Expected finished_send_file, got {}'.format(wire['type']))

        return cls(
            wire['filename'],
            wire['last_sequence']
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
    used_seq_num: int
    file_reader: BinaryIO
    host: str
    port: int

    def __init__(self, sock: socket.socket, file_reader: BinaryIO, host: str, port: int) -> None:
        self.sock = sock
        self.seq_num = 0
        self.used_seq_num = 0
        self.file_reader = file_reader
        self.host = host
        self.port = port

    def send(self, sequences: Optional[Container[int]]) -> int:
        """
        Send this file across the UDP socket.

        If `sequences` is not `None`, only send those specific sequence numbers.
        Returns the last sequence number we sent.
        """

        # keep sending packets until we've sent all the data
        while True:
            # read the next packet
            packet = self.read_packet()

            # if we've reached the end of the file, we're done
            if packet is None:
                # reset sequence number and reutrn 
                self.seq_num = 0
                return self.used_seq_num

            # check the sequence number
            if sequences is not None and packet.header.seq_num not in sequences:
                continue

            # send the packet
            self.used_seq_num = self.seq_num
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

    def __enter__(self):
        return self

    def __exit__(self):
        self.file_reader.close()
        self.sock.close()

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

# checksum
def get_checksum(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

# client operations

class FileInfo:
    """
    Information about a file
    """
    
    filename: str
    checksum: bytes
    size: int

    def __init__(self, filename: str, checksum: bytes) -> None:
        self.filename = filename
        self.checksum = checksum
        
        # calculate file size in bytes
        self.size = os.path.getsize(self.filename)

class Client:
    """
    The client state for the file transfer mechanism.
    """

    files: Mapping[str, FileInfo]
    folder: str
    sock: BufferedSocket
    num_concurrent: int
    ports: Sequence[int]

    current_ports: Mapping[str, int]

    def __init__(self):
        self.files = {}
        self.current_ports = {}

    def run(self):
        # read in all files (recursively) from the folder specified in the second
        # argument
        folder = sys.argv[2]
        self.folder = folder
        
        for root, dirs, files in os.walk(folder):
            for filename in files:
                # get the checksums for the file
                with open(os.path.join(root, filename), 'rb') as f:
                    checksum = get_checksum(f.read())

                # add the file to the list of files
                self.files[filename] = FileInfo(filename, checksum)

        # create the socket
        hostname = sys.argv[3]
        port = unwrap_or(find_argument("--port"), DEFAULT_PORT)

        # start up a TCP socket connected to the given hostname and port
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((hostname, port))
        self.sock = BufferedSocket(sock)

        # send the Open request to indicate that we're open for business
        num_concurrent = 16
        filenames = [info.filename for info in self.files.values()]
        checksums = {info.filename: info.checksum for info in self.files.values()}

        self.sock.send_wiretype(OpenRequest(filenames, num_concurrent, checksums))

        # wait for an Open reply in response
        open_reply = self.sock.recv_wiretype(OpenReply)

        self.num_concurrent = open_reply.num_concurrent
        self.ports = open_reply.ports

        # begin sending files
        # TODO: parallelize

        # create pool object with given number of processes 
        pool_obj = multiprocessing.Pool(processes = self.num_concurrent)

        # submits individual elements of the iterable "self.files.values()" 
        # as tasks to be processed by the pool
        pool_obj.map(send_file, self.files.values())

        # process to handle a single iterable at a time 
        def send_file(file):
            # choose a port that is not currently in use
            for port in self.ports:
                if port in self.current_ports.values():
                    continue
                self.current_ports[file.filename] = port 
                break

            current_port = self.current_ports[file.filename]

            self.sock.send_wiretype(SendFileRequest(
                file.filename,
                file.size,
                current_port
            ))

            sequences = None

            # open a UDP socket to send files over
            while True:
                file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                with FilePacketSender(file_sock, open(file.filename, "rb"), hostname, current_port) as sender:
                    last_seq = sender.send()

                # indicate that we've sent the file
                self.sock.send_wiretype(
                    FinishedFileRequest(file.filename, last_seq)
                )

                # wait for the response from the server
                response = self.sock.recv_many_wiretype(
                    SendFileReply, ResendPacketsReply
                )

                # if we received a SendFileReply, we're done
                if isinstance(response, SendFileReply):
                    break
                else:
                    sequences = response.packets

"""         for file in self.files.values():
            # choose a port that is not currently in use
            for port in self.ports:
                if port in self.current_ports.values():
                    continue
                self.current_ports[file.filename] = port 
                break

            current_port = self.current_ports[file.filename]

            self.sock.send_wiretype(SendFileRequest(
                file.filename,
                file.size,
                current_port
            ))

            sequences = None

            # open a UDP socket to send files over
            while True:
                file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                with FilePacketSender(file_sock, open(file.filename, "rb"), hostname, current_port) as sender:
                    last_seq = sender.send()

                # indicate that we've sent the file
                self.sock.send_wiretype(
                    FinishedFileRequest(file.filename, last_seq)
                )

                # wait for the response from the server
                response = self.sock.recv_many_wiretype(
                    SendFileReply, ResendPacketsReply
                )

                # if we received a SendFileReply, we're done
                if isinstance(response, SendFileReply):
                    break
                else:
                    sequences = response.packets """

        # connection is now implicitly closed

# server operations

class ServerFileInfo:
    """
    Information about a file
    """

    filename: str
    checksum: bytes
    size: Optional[int]

    def __init__(self, filename: str, checksum: bytes) -> None:
        self.filename = filename
        self.checksum = checksum
        
        # calculate file size in bytes
        self.size = None 

class Server:
    """
    The server state for the file transfer mechanism.
    """

    files: Mapping[str, FileInfo]
    working_ports: Sequence[int]
    file_root: Path

    def __init__(self):
        self.files = {}
        self.working_ports = []
        self.file_root = Path(sys.argv[2])

    def run(self):
        # open a listener on the default port
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.bind(('', unwrap_or(find_argument("--port"), DEFAULT_PORT)))

        # wait for a connection
        listener.listen(1)
        sock, addr = listener.accept()
        sock = BufferedSocket(sock)

        # wait for an Open request that contains information
        # about the files we're going to receive
        open_request = sock.recv_wiretype(OpenRequest)

        # register the file info
        for filename in open_request.filenames:
            checksum = open_request.checksums[filename]
            self.files[filename] = ServerFileInfo(filename, checksum)

        # decide how many working ports we want
        self.working_ports = list(range(DEFAULT_FILE_PORT, DEFAULT_FILE_PORT + open_request.num_concurrent))

        # send an Open reply with this information
        sock.send_wiretype(OpenReply(self.working_ports, open_request.num_concurrent))

        # wait for a SendFileRequest
        while len(self.files) > 0:
            # wait for the send file request
            send_file_request = sock.recv_wiretype(SendFileRequest)

            # this indicates the size of the file, as well as the server port
            # it's being sent over
            fileinfo = self.files[send_file_request.filename]
            filesize = send_file_request.filesize

            while True:
                # begin receiving files over the designated port
                # open a UDP listening socket
                file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                file_sock.bind(('', send_file_request.port))
                f = open(os.path.join(self.file_root, fileinfo.filename), "wb")
                with FilePacketReader(file_sock, f, filesize) as receiver:
                    # receive the file
                    received_sequences = list(receiver.read())

                # wait for the FinishedFileRequest
                finished_file_request = sock.recv_wiretype(FinishedFileRequest)

                # if we've received every sequence number up to the one indicated
                # in the request, we're done
                full_packets = list(range(finished_file_request.last_seq + 1))
                if received_sequences == full_packets:
                    # remove the filename from self.files
                    del self.files[send_file_request.filename]
                    sock.send_wiretype(
                        SendFileReply(filename)
                    )
                    break
                else:
                    # we missed a packet
                    # ask to resend the missed packets
                    diff_packets = list(set(full_packets) - set(received_sequences))
                    sock.send_wiretype(ResendPacketsReply(filename, diff_packets))

        # connection is now implicitly closed

def main():
    mode = sys.argv[1]
    if mode == "client":
        client = Client()
        client.run()
    elif mode == "server":
        server = Server()
        server.run()
    else:
        print("Invalid mode: {}".format(mode))
        sys.exit(1)

if __name__ == "__main__":
    main()
