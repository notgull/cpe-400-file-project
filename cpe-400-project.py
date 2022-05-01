# John Nunley, Bill Tong, Parker
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

# import section

from abc import ABC, abstractmethod, abstractclassmethod
from pathlib import Path
import shutil
import time
from typing import Any, BinaryIO, Callable, Container, Iterable, Mapping, Optional, Sequence, Tuple, TypeVar, Union

import array
import hashlib
import json
import os
import random
import select
import socket
import struct
import sys
import tempfile
import threading

from numpy import diff

# constants

# the size of the blocks used in file packets
#
# equivalent to 16 KiB
BLOCK_SIZE = 2**14
# the default value for num_concurrency if the user doesn't specify it
DEFAULT_CONCURRENCY = 1
# the default port used for the TCP connection
DEFAULT_PORT = 27850
# the starting port for sending files
# 
# ports from this to this plus num concurrency will b
DEFAULT_FILE_PORT = 27851
# timeout for the TCP connection
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

    # iterate over sys.argv, look for the argument, and get the argument
    # after it
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

class NoOp(WireRepr):
    """
    A quick no-op wire representation object for testing.
    """

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'no_op'
        }

    @classmethod
    def from_wire(cls, mapping: Mapping[str, Any]) -> 'NoOp':
        if mapping['type'] != 'no_op':
            raise ValueError("bad value")

        return cls()

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
        checksums = {}

        # hex strings are easier to send in JSON form
        for filename, checksum in self.checksums.items():
            checksums[filename] = checksum.hex()

        return {
            'type': 'open_request',
            'filenames': self.filenames,
            'num_concurrent': self.num_concurrent,
            'checksums': checksums
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'OpenRequest':
        if wire['type'] != 'open_request':
            raise ValueError('Expected open_request, got {}'.format(wire['type']))

        checksums = {}
        for filename, checksum in wire['checksums'].items():
            # convert from hex
            checksums[filename] = bytes.fromhex(checksum)

        return OpenRequest(
            wire['filenames'],
            wire['num_concurrent'],
            checksums,
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

class ReadyForFileReply(WireRepr):
    """
    Tells the server that we're ready to receive the given file.
    """

    filename: str

    def __init__(self, filename: str) -> None:
        self.filename = filename

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'ready_for_file',
            'filename': self.filename,
        }

    @classmethod
    def from_wire(cls, mapping: Mapping[str, Any]) -> 'ReadyForFileReply':
        if mapping['type'] != 'ready_for_file':
            raise ValueError("Expected ready_for_file, got {}".format(mapping['type']))

        return cls(
            mapping['filename']
        )

class FinishedFileRequest(WireRepr):
    """
    Tell the server that we've finished sending the specified file.

    Contains the filename we just finished sending.
    """

    filename: str
    sequences: Sequence[int]

    def __init__(self, filename: str, sequences: Sequence[int]) -> None:
        self.filename = filename
        self.sequences = sequences

    def to_wire(self) -> Mapping[str, Any]:
        return {
            'type': 'finished_send_file',
            'filename': self.filename,
            'sequences': self.sequences,
        }

    @classmethod
    def from_wire(cls, wire: Mapping[str, Any]) -> 'FinishedFileRequest':
        if wire['type'] != 'finished_send_file':
            raise ValueError('Expected finished_send_file, got {}'.format(wire['type']))

        return cls(
            wire['filename'],
            wire['sequences']
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
        # pack it into two big-endian 32 bit numbers
        return struct.pack('<II', self.seq_num, self.size)

    @classmethod
    def from_bytes(cls, data: bytes) -> 'FilePacketHeader':
        # unpack using two numbers
        seq_num, size = struct.unpack('<II', data)
        return cls(seq_num, size)

    @classmethod
    def size(cls) -> int:
        """
        Get the amount of space needed for a FilePacketHeader.
        """

        return struct.calcsize('<II')

    def __repr__(self) -> str:
        return 'FilePacketHeader(seq_num={}, size={})'.format(self.seq_num, self.size)
    
    def __str__(self) -> str:
        return repr(self)

class FilePacket:
    """
    The total file packet. COntains a slice of the file, and the
    header as mentioned above.

    These are the objects sent over the UDP socket.
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

        # restrict to the size given in the header
        data = data[:header.size]

        return cls(header, data)

    def __repr__(self) -> str:
        builder = f"== seq: {self.header.seq_num} == size: {self.header.size} ==\n"
        for i, byte in enumerate(self.data[:self.header.size]):
            builder += f'{byte:02x} '
            if (i + 1) % 16 == 0:
                builder += '\n'

        return builder
  
    def __str__(self) -> str:
        return repr(self)

# socket functions

WireType = TypeVar("WireType")

class BufferedSocket:
    """
    A wrapper around a (TCP?) socket with an attached read buffer.

    This adds a layer of abstraction over the socket, so that we can
    send and receive WireRepr types over the socket.
    """

    sock: socket.socket

    def __init__(self, sock: socket.socket) -> None:
        self.sock = sock

        # this way, we never hang before a file transfer ends
        self.sock.settimeout(1.0)

    def send_data(self, data: bytes) -> None:
        """
        Send data to the socket.
        """

        # send the amount of data, in a u32 byte format,
        # followed by the data itself
        buf = struct.pack('<I', len(data))
        self.sock.sendall(buf + data)

    def __recvall(self, bufsize: int) -> Optional[bytes]:
        """
        Receive all data from the socket until it fills the buffer.
        """

        data = b''
        while len(data) < bufsize:
            # 1 second timeout
            try:
                total = self.sock.recv(bufsize - len(data))
            except socket.timeout:
                return None
            if not total:
                raise ConnectionError('Connection closed')
            data += total
        return data

    def recv_data(self) -> Optional[bytes]:
        """
        Receive data.
        """

        # receive the amount of data, in a u32 byte format
        buf = self.__recvall(4)
        if buf is None:
            return None
        if len(buf) == 0:
            raise ConnectionResetError('Connection closed')
        elif len(buf) != 4:
            raise ConnectionError('Connection error')
        
        # unpack the amount of data
        size = struct.unpack('<I', buf)[0]

        # receive the data
        buf = self.__recvall(size)
        return buf

    def recv_json(self) -> Optional[Mapping[str, Any]]:
        """
        Receive a JSON object from the socket.
        """

        # receive the JSON object
        data = self.recv_data()
        if data is None:
            return None

        # return the JSON object
        return json.loads(data.decode('utf-8'))

    def recv_wiretype(self, ty) -> Optional[WireRepr]:
        """
        Receive a wire-encoded object from the buffer.
        """

#        print(f"receiving: {ty}")

        map = self.recv_json()
        if not map:
            return None

        # use WireRepr to convert the map to the right type
        return ty.from_wire(map)
    
    def send_wiretype(self, obj: WireRepr) -> None:
        """
        Send a wire-encoded object across the buffer.
        """

#        print(f"sending: {obj}")
        by = obj.to_wire()
        self.send_data(json.dumps(by).encode('utf-8'))

    def recv_many_wiretype(self, *args) -> Optional[Any]:
        """
        Receive one of many wire-encoded types.

        This tries to receive one of the types in args, and returns
        the first one that succeeds.
        """

        map = self.recv_json()
        if not map:
            return None

#        print(f"receiving one of: {args}")

        # try all of the args as constructors until we find one that
        # doesn't die
        for ty in args:
            try:
                return ty.from_wire(map)
            except:
                pass

    def close(self) -> None:
        """
        Close the socket.
        """

        self.sock.close()

def test_buffered_socket():
    """
    Sanity test for the buffered socket.
    """

    # create a pair of sockets
    sock1, sock2 = socket.socketpair()

    # wrap them both in BufferedSocket
    sock1 = BufferedSocket(sock1)
    sock2 = BufferedSocket(sock2)

    # send some basic data over one and watch it be received in the other
    msg = b'Hello, world!'
    sock1.send_data(msg)
    assert sock2.recv_data() == msg 

    class TestType(WireRepr):
        i: int

        def __init__(self, i: int) -> None:
            self.i = i

        def to_wire(self) -> Mapping[str, Any]:
            return {
                'type': 'test_type',
                'i': self.i
            }

        @classmethod
        def from_wire(cls, mapping: Mapping[str, Any]) -> 'TestType':
            if mapping['type'] != 'test_type':
                raise ValueError("bad value")

            return cls(mapping['i'])

        def __eq__(self, o: object) -> bool:
            if not hasattr(o, 'i'):
                return False
            else:
                return self.i == o.i

    sock1.send_wiretype(TestType(27))
    assert sock2.recv_wiretype(TestType) == TestType(27)

    print("buffered sockets work")
            

class FilePacketSender:
    """
    A wrapper around a (UDP) socket that sends file packets as
    datagrams.
    """

    sock: socket.socket
    seq_num: int
    sequences: Sequence[int]
    file_reader: BinaryIO
    host: Optional[str]
    port: Optional[int]
    corrupt: bool
    skip_second_one: bool

    def __init__(
        self, 
        sock: socket.socket, 
        file_reader: BinaryIO, 
        host: Optional[str], 
        port: Optional[int]
    ) -> None:
        self.sock = sock
        self.seq_num = 0
        self.sequences = []
        self.file_reader = file_reader
        self.host = host
        self.port = port

        self.corrupt = False
        self.skip_second_one = False

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
                break 

            # check the sequence number
            if sequences is not None and packet.header.seq_num not in sequences:
                continue

            # if we need to, corrupt the packet
            if self.corrupt:
                # invert all of the bytes
                packet.data = bytes(
                    (b ^ 0xff) for b in packet.data
                )

            # send the packet
            self.sequences.append(packet.header.seq_num)
            if self.skip_second_one and packet.header.seq_num == 1:
                continue
            self.send_packet(packet)

        # send a zero-size packet at the very end
        zsp = FilePacket(FilePacketHeader(self.seq_num + 1, 0), b'\x00' * BLOCK_SIZE)
        #print(f"sending:\n{zsp}")
        self.send_packet(zsp)

        return self.sequences

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

        block_size = len(data)

        # pad it out to the block size
        data += b'\x00' * (BLOCK_SIZE - block_size)

        # create the packet
        packet = FilePacket(FilePacketHeader(self.seq_num, block_size), data)

        # increment the sequence number
        self.seq_num += 1

        return packet

    def send_packet(self, packet: FilePacket) -> None:
        """
        Send a packet across the UDP socket.
        """

#        print(f"sending packet:\n{packet}")

        # send the packet
        if self.host is not None and self.port is not None:
            # repeatedly call sendto until all bytes are sent
            buf = packet.to_bytes()
            while len(buf) > 0:
                by = self.sock.sendto(buf, (self.host, self.port))
                buf = buf[by:]
        else:
            self.sock.sendall(packet.to_bytes())

    def __enter__(self):
        return self

    def __exit__(self):
        self.file_reader.close()
        self.sock.close()

class FilePacketReader(ABC):
    """
    A wrapper around a UDP socket that reads in packets and writes them
    to a file.

    This will either write or append to the stream.
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
        data = b''
        while len(data) != BLOCK_SIZE + FilePacketHeader.size():
            data += self.sock.recv(BLOCK_SIZE + FilePacketHeader.size() - len(data))

        # parse the packet
        packet = FilePacket.from_bytes(data)

        # if the packet's size is 0, we're done
        if packet.header.size == 0:
            return None

        return packet

    @abstractmethod
    def write_packet(self, packet: FilePacket) -> None:
        """
        Write a file packet that we received.
        """

        pass

    @abstractmethod
    def get_going(self) -> None:
        """
        Push any other pending data to the output
        """

        pass

    def close(self) -> None:
        """
        Close the file writer.
        """

        self.file_writer.close()

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
            seqnum = packet.header.seq_num
#            print(f"read packet {seqnum}")
            yield seqnum 

            # write the packet to the file
            self.write_packet(packet)

class WriteFilePacketReader(FilePacketReader):
    """
    Takes a new file and writes into it.

    Used for receiving the initial file and re-receiving the entire thing after a checksum error.
    """

    def __init__(self, sock: socket.socket, file_writer: BinaryIO) -> None:
        self.sock = sock
        self.file_writer = file_writer

    def write_packet(self, packet: FilePacket) -> None:
        # move the file writer to the right position
        self.file_writer.seek(packet.header.seq_num * BLOCK_SIZE)

        # write the packet to the file
        self.file_writer.write(packet.data)

    def get_going(self) -> None:
        pass

class SpliceFilePacketReader(FilePacketReader):
    """
    Takes an existing file path and splices a set number
    of packets into it.

    Used for receiving individual packets.
    """

    file_reader: BinaryIO
    sequences: Sequence[int]
    last_seqnum: int
    final_seqnum: int
    tpath: str

    def __init__(
        self,
        sock: socket.socket,
        fpath: str,
        sequences: Sequence[int],
        final_seqnum: int
    ) -> None:
        # copy the old file to the file plus .tmp
        # and then open the new file to write
        tpath = fpath + ".tmp"
        shutil.copyfile(fpath, tpath)
        file_writer = open(fpath, "wb")
        self.file_reader = open(tpath, "rb")

        super().__init__(
            sock,
            file_writer
        )

        self.sequences = sequences
        self.last_seqnum = -1
        self.final_seqnum = final_seqnum
        self.tpath = tpath

    def __copy_packets(self, up_to: int) -> None:
        """
        Copy all of the unsent packet up to the "up_to" parameter
        into the new file.
        """

        for seqnum in range(self.last_seqnum + 1, up_to + 1):
            self.file_reader.seek(seqnum * BLOCK_SIZE)
            data = self.file_reader.read(BLOCK_SIZE)
            self.file_writer.seek(seqnum * BLOCK_SIZE)
            self.file_writer.write(data)

    def write_packet(self, packet: FilePacket) -> None:
        # catch up on all of the packets we haven't seen yet
        self.__copy_packets(packet.header.seq_num - 1)

        # move the file writer to the right position
        self.file_writer.seek(packet.header.seq_num * BLOCK_SIZE)
        if packet.header.seq_num in self.sequences:
            data = packet.data
        else:
            self.file_reader.seek(packet.header.seq_num * BLOCK_SIZE)
            data = self.file_reader.read(BLOCK_SIZE)

        # write the packet to the file
        self.file_writer.write(data)
        self.last_seqnum = max(self.last_seqnum, packet.header.seq_num)

    def get_going(self) -> None:
        """
        Write all of the packets we haven't written yet.
        """

        # write all of the packets we haven't written yet
        self.__copy_packets(self.final_seqnum)

        # remove the file
        os.unlink(self.tpath)
        

def test_file_packet():
    """
    Sanity test for the file packet system
    """

    # create a pair of sockets
    sock1, sock2 = socket.socketpair()

    # create a temporary file with dummy data
    with tempfile.TemporaryDirectory() as tmp_dir:
        # write some data to the file
        path1 = os.path.join(tmp_dir, "tmp1.bin")
        path2 = os.path.join(tmp_dir, "tmp2.bin")
        data = os.urandom(BLOCK_SIZE * 4)
        with open(path1, "wb") as f:
            f.write(data)

        # wrap the sockets in FilePacketSender and FilePacketReader
        with open(path1, "rb") as f:
            sender = FilePacketSender(sock1, f, None, None)
            with open(path2, "wb") as f2:
                reader = WriteFilePacketReader(sock2, f2)

                # send the file across the sockets
                sender.send(None)

                # expend all of the packets
                for seq in reader.read():
                    pass
                reader.get_going()
                reader.close()

        # check if file is equal
        with open(path2, "rb") as f2:
            data2 = f2.read()
            assert data == data2

        # we also need to check replacement mode
        # see if it works with just the data
        with open(path1, "rb") as f:
            sender = FilePacketSender(sock1, f, None, None)

            reader = SpliceFilePacketReader(
                sock2,
                path2,
                [1,2],
                3
            )

            # send the file across the sockets
            sender.send([1,2])
            for seq in reader.read():
                pass
            reader.get_going()
            reader.close()

        # check if file is equal
        with open(path2, "rb") as f2:
            data2 = f2.read()
            assert data == data2

    print("file senders work")

# checksum
def get_checksum(data: bytes) -> bytes:
    """
    Get the SHA256 checksum for a series of bytes.
    """

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

FileRecvResponse = Union[SendFileReply, ResendPacketsReply]

class Client:
    """
    The client state for the file transfer mechanism.
    """

    files: Mapping[str, FileInfo]
    responses: Mapping[str, FileRecvResponse]
    folder: str
    sock: BufferedSocket
    num_concurrent: int
    running: bool
    ports: Sequence[int]

    current_ports: Mapping[str, int]
    hostname: str
    active: int

    def __init__(self, folder: str, hostname: str):
        self.files = {}
        self.responses = {}
        self.current_ports = {}
        self.running = True
        self.folder = folder
        self.hostname = hostname
        self.active = 0
        
        # read in all files (recursively) from the folder specified in the second
        # argument        
        for root, dirs, files in os.walk(self.folder):
            for filename in files:
                filename = os.path.join(root, filename)

                # get the checksums  for the file
                with open(filename, 'rb') as f:
                    checksum = get_checksum(f.read())

                # add the file to the list of files
                self.files[filename] = FileInfo(filename, checksum)

    def open_socket(self) -> None:
        """
        Opens the socket and connects to the server.
        """

        port = unwrap_or(find_argument("--port"), DEFAULT_PORT)

        # start up a TCP socket connected to the given hostname and port
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((self.hostname, port))
        sock.settimeout(1.0)
        self.sock = BufferedSocket(sock)

    def begin_handshake(self) -> None:
        """
        Send the OpenRequest to begin the handshake.
        """

        num_concurrent = unwrap_or(find_argument("--concurrent"), DEFAULT_CONCURRENCY)
        if isinstance(num_concurrent, str):
            num_concurrent = int(num_concurrent)

        filenames = [info.filename for info in self.files.values()]
        checksums = {info.filename: info.checksum for info in self.files.values()}

        self.sock.send_wiretype(OpenRequest(filenames, num_concurrent, checksums))

    def read_handshake(self) -> None:
        """
        Read the OpenReply to complete the handshake.
        """

        # wait for an Open reply in response
        open_reply = self.sock.recv_wiretype(OpenReply)

        self.num_concurrent = open_reply.num_concurrent
        self.ports = open_reply.ports

    def choose_port(self, file: FileInfo) -> int:
        """
        Choose the port we're sending our file over.
        """

        # iterate until we find one that isn't in use
        while True:
            for port in self.ports:
                if port in self.current_ports.values():
                    continue
                self.current_ports[file.filename] = port 
                return port

    def send_file(
        self,
        file: FileInfo,
        init_sequences: bool, 
        corrupt_packet: bool,
    ) -> None:
        """
        Send a single file across the wire.
        """

        # choose a port that is not currently in use
        current_port = self.choose_port(file)

        self.sock.send_wiretype(SendFileRequest(
            file.filename,
            file.size,
            current_port
        ))

        # wait for server to be ready
        while True:
            if file.filename in self.responses:
                response = self.responses[file.filename]
                del self.responses[file.filename]
                break

        sequences = None

        # open a UDP socket to send files over
        while True:
            file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            f = open(file.filename, "rb")
            sender = FilePacketSender(file_sock, f, self.hostname, current_port)

            # corrupt packet if we want to 
            if corrupt_packet:
                print("Intentionally corrupting packet...")
                sender.corrupt = True
                corrupt_packet = False
            if init_sequences:
                print("Intentionally skipping a sequence number...")
                sender.skip_second_one = True
                init_sequences = False

            last_seq = sender.send(sequences)
            f.close()
            file_sock.close()

            # indicate that we've sent the file
            self.sock.send_wiretype(
                FinishedFileRequest(file.filename, last_seq)
            )

            # wait for the respconse from the server
            while True:
                if file.filename in self.responses:
                    response = self.responses[file.filename]
                    del self.responses[file.filename]
                    break

            # if we received a SendFileReply, we're done
            if isinstance(response, SendFileReply):
                del self.current_ports[file.filename]
                print(f"sent file in full: {file.filename}")
                break
            elif isinstance(response, ResendPacketsReply):
                sequences = response.packets
            else:
                raise ValueError("shouldn't get ready for in progress file")

#        print("done sending file")
        self.active -= 1

    def log_responses(self):
        while self.running:
            # receive the next packet
            try:
                response = self.sock.recv_many_wiretype(
                    ReadyForFileReply, SendFileReply, ResendPacketsReply
                )
            except ValueError:
                # main thread is trying to wake us up
                break
            except ConnectionError:
                break

            if response is None:
                continue

            # add the response to the map
            self.responses[response.filename] = response

    def send_files(self, test: bool) -> None:
        """
        Send all of the files that we need to.
        """

        # create a thread that just sits on the socket and logs its responses
        # into the responses map

        # start the thread in the multiprocessing pool
        logger = threading.Thread(target=self.log_responses)
        logger.start()

        # submits individual elements of the iterable "self.files.values()" 
        # as tasks to be processed by the pool
        threads = []
        for i, file in enumerate(self.files.values()):
            # intentionally corrupt for testing purposes
            if test:
                miss_sequence = i == 0
                corrupt = i == 1
            else:
                miss_sequence = False
                corrupt = False

            # start file thread and append to list
            th = threading.Thread(
                target=self.send_file, 
                args=(file,miss_sequence,corrupt)
            )
            th.start()
            threads.append(th)
            self.active += 1

            # limit concurrent processes
            while self.active >= self.num_concurrent:
                time.sleep(0.1)

        # wait for all threads to finish
        for th in threads:
            th.join()

        # wake up the logger thread
        self.running = False
        logger.join()

    def run(self, test: bool):
        # create the socket
        self.open_socket()

        # send the Open request to indicate that we're open for business
        self.begin_handshake()
        self.read_handshake()

        self.send_files(test)

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
    listener: socket
    sock: BufferedSocket
    file_count: int
    num_concurrent: int
    running: bool

    send_file_requests: Sequence[SendFileRequest]
    finished_file_requests: Mapping[str, FinishedFileRequest]

    def __init__(self, file_root: Path):
        self.files = {}
        self.working_ports = []
        self.file_root = file_root
        self.file_count = 0
        self.send_file_requests = []
        self.finished_file_requests = {}
        self.running = True

    def begin_listening(self) -> None:
        """
        Begin listening on the target port.
        """

        # open a listener on the default port
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        while True:
            try:
                listener.bind(('0.0.0.0', unwrap_or(find_argument("--port"), DEFAULT_PORT)))
                break
            except OSError as e:
                print(e)
                continue
        listener.listen(1)
        self.listener = listener

        print("waiting for client...")

    def accept_client(self) -> None:
        # accept the client response
        sock, _ = self.listener.accept()
        sock = BufferedSocket(sock)
        self.sock = sock

    def handshake(self) -> None:
        """
        Wait for an OpenRequest, analyze it, and send back an OpenReply
        """

        # wait for an Open request that contains information
        # about the files we're going to receive
        open_request = self.sock.recv_wiretype(OpenRequest)

        # register the file info
        for filename in open_request.filenames:
            checksum = open_request.checksums[filename]
            self.files[filename] = ServerFileInfo(filename, checksum)
            self.file_count += 1

        # decide how many working ports we want
        self.working_ports = list(range(DEFAULT_FILE_PORT, DEFAULT_FILE_PORT + open_request.num_concurrent))
        self.num_concurrent = open_request.num_concurrent

        # send an Open reply with this information
        self.sock.send_wiretype(OpenReply(self.working_ports, open_request.num_concurrent))

    def log_requests(self) -> None:
        while self.running:
            # receive a SendFileRequest or a FinishedFileRequest
            try:
                request = self.sock.recv_many_wiretype(
                    SendFileRequest, FinishedFileRequest
                )
            except ValueError:
                # main thread is probably trying to wake us up
                continue
            except ConnectionError:
                break

            # add the request to the appropriate list
            if isinstance(request, SendFileRequest):
                self.send_file_requests.append(request)
            elif isinstance(request, FinishedFileRequest):
                self.finished_file_requests[request.filename] = request
            else:
                # invalid; main thread is waking us up
                continue

    def recv_file(self, sfe: SendFileRequest) -> None:
#        print("recv file was run")
        filename = sfe.filename
        filesize = sfe.size
        port = sfe.port
        total_packets = filesize // BLOCK_SIZE + (filesize % BLOCK_SIZE > 0)

#        print(f"reading file {filename}")

        # this indicates the size of the file, as well as the server port
        # it's being sent over
        fileinfo = self.files[filename]

        file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        file_sock.bind(('', port))

        # we are ready 
        self.sock.send_wiretype(ReadyForFileReply(fileinfo.filename))

        diff_packets = None

        while True:
            # begin receiving files over the designated port
            # open a UDP listening socket
            path = os.path.join(self.file_root, os.path.basename(fileinfo.filename))

            if diff_packets is None:
                f = open(path, "wb")
                receiver = WriteFilePacketReader(file_sock, f)
            else:
                receiver = SpliceFilePacketReader(
                    file_sock,
                    path,
                    diff_packets,
                    total_packets,
                )

            # received the file
            received_sequences = list(receiver.read())
            receiver.get_going()
            receiver.close()

            # wait for the FinishedFileRequest
            while True:
                if filename in self.finished_file_requests:
                    finished_file_request = self.finished_file_requests[filename]
                    del self.finished_file_requests[filename]
                    break
                time.sleep(0.1)

            # if we've received every sequence number up to the one indicated
            # in the request, we're done
            full_packets = finished_file_request.sequences
            #print(f"expected sequences {full_packets}")
            #print(f"received sequences {received_sequences}")
            if received_sequences == full_packets:
                print(f"recv file in full: {filename}")
                # make sure that the file matches the checksum
                with open(path, "rb") as f:
                    data = f.read()
#                    print(data)
                    checksum = get_checksum(data)
                    if checksum != fileinfo.checksum:
                        print("file was corrupted")
                        # ask to resend all packets
                        # round up division 
                        req_packets = list(range(total_packets))
                        self.sock.send_wiretype(ResendPacketsReply(fileinfo.filename, req_packets))
                        diff_packets = None
                        continue

                # remove the filename from self.files
                del self.files[filename]
                file_sock.close()
                self.sock.send_wiretype(
                    SendFileReply(filename)
                )
                break
            else:
                # we missed a packet
                # ask to resend the miss(ed packets
                diff_packets = list(set(full_packets) - set(received_sequences))
                print(f"missed packets: {diff_packets}")
                self.sock.send_wiretype(ResendPacketsReply(filename, diff_packets))
                mode = "ab"

    def recv_files(self) -> None:
        logger = threading.Thread(target=self.log_requests)
        logger.start()

        # wait for a SendFileRequest
        thread_list = []
        print(f"file count is {self.file_count}")
        while self.file_count > 0:
            # wait for the send file request
            while True:
                if len(self.send_file_requests) > 0:
                    send_file_request = self.send_file_requests.pop(0)
                    break
                time.sleep(0.1) 

            # spawn a new thread
            f = threading.Thread(target=self.recv_file, args=(send_file_request,))
            f.start()
            thread_list.append(f)

            self.file_count -= 1

        # wait for all threads to finish
        for thread in thread_list:
            thread.join()

        # done; set running to false and wake up the logger thread
        self.running = False
        #self.sock.close() 
        logger.join()

    def run(self):
        self.begin_listening()
        self.accept_client()
        self.handshake()

        self.recv_files()

        # connection is now implicitly closed

# test single file
def test_single_file(complex: bool) -> None:
    if complex:
        count = 3
    else:
        count = 1
    
    # create two temporary directories to store the temp
    # file in
    with tempfile.TemporaryDirectory() as send_dir:
        with tempfile.TemporaryDirectory() as recv_dir:
            # fill a binary file with random info
            paths = [f"test{f}.bin" for f in range(count)]
            datas = [os.urandom(BLOCK_SIZE * 4) for _ in paths]
            for i, path in enumerate(paths):
                data = datas[i]
                p = os.path.join(send_dir, path)
                with open(p, "wb") as f:
                    f.write(data)

            # open a client and server
            client = Client(send_dir, "localhost")
            server = Server(recv_dir)

            # go through the handshake if only one file
            server.begin_listening()
            client.open_socket()
            server.accept_client()

            client.begin_handshake()
            server.handshake()
            client.read_handshake()

            assert 27851 in client.ports

            def run_client(client: Client) -> None:
                # run the client
                if not complex:
                    client.send_file(
                        FileInfo(
                            os.path.join(send_dir, paths[0]),
                            get_checksum(data)
                        ),
                        False,
                        False,
                    )
                    client.running = False
                else:
                    client.send_files(True)

            def run_server(server: Server, path: Path) -> None:
                try:
                    server.recv_files()
                finally:
                    server.sock.close()
                    server.listener.close()

            def log_drop_err(client: Client) -> None:
                try:
                    client.log_responses()
                except Exception as e:
                    print(e)

            # open a thread for the client and
            # another for the server
            f1 = threading.Thread(target=run_client, args=(client,)) 
            f2 = threading.Thread(target=run_server, args=(server,path))
            f3 = threading.Thread(target=log_drop_err, args=(client,))
            f1.start()
            f2.start()
            f3.start()
            f1.join()
            f2.join()
            f3.join()

            # make sure files are equal
            for i, path in enumerate(paths):
                data = datas[i]
                with open(os.path.join(recv_dir, path), "rb") as f:
                    fdata = f.read()
                    if fdata != data:
                        raise Exception(f"Files are not equal: {path}")

            sys.exit(0)

def main() -> None:
    """
    Program entry point
    """

    mode = sys.argv[1]
    if mode == "client":
        client = Client(sys.argv[2], sys.argv[3])
        client.run(False)
    elif mode == "server":
        server = Server(Path(sys.argv[2]))
        server.run()
        server.listener.close()
    elif mode == "test":
        test_buffered_socket()
        test_file_packet()
        test_single_file(False)
    elif mode == "ctest":
        client = Client(sys.argv[2], sys.argv[3])
        client.run(True)
    else:
        print("Invalid mode: {}".format(mode))
        sys.exit(1)

if __name__ == "__main__":
    main()
