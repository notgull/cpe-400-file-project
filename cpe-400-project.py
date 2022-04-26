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
from concurrent import futures
from pathlib import Path
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
        checksums = {}
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
       return struct.pack('<II', self.seq_num, self.size)

    @classmethod
    def from_bytes(cls, data: bytes) -> 'FilePacketHeader':
        seq_num, size = struct.unpack('<II', data)
        return cls(seq_num, size)

    @classmethod
    def size(cls) -> int:
        return struct.calcsize('<II')

    def __repr__(self) -> str:
        return 'FilePacketHeader(seq_num={}, size={})'.format(self.seq_num, self.size)
    
    def __str__(self) -> str:
        return repr(self)

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
    """

    sock: socket.socket

    def __init__(self, sock: socket.socket) -> None:
        self.sock = sock

    def send_data(self, data: bytes) -> None:
        """
        Send data to the socket.
        """

        # send the amount of data, in a u32 byte format,
        # followed by the data itself
        buf = struct.pack('<I', len(data))
        self.sock.sendall(buf + data)

    def __recvall(self, bufsize: int) -> bytes:
        """
        Receive all data from the socket until it fills the buffer.
        """

        data = b''
        while len(data) < bufsize:
            total = self.sock.recv(bufsize - len(data))
            if not total:
                raise ConnectionResetError('Connection closed')
            data += total
        return data

    def recv_data(self) -> bytes:
        """
        Receive data.
        """

        # receive the amount of data, in a u32 byte format
        buf = self.__recvall(4)
        if len(buf) == 0:
            raise ConnectionResetError('Connection closed')
        elif len(buf) != 4:
            raise ConnectionError('Connection error')
        
        # unpack the amount of data
        size = struct.unpack('<I', buf)[0]

        # receive the data
        buf = self.__recvall(size)
        return buf

    def recv_json(self) -> Mapping[str, Any]:
        """
        Receive a JSON object from the socket.
        """

        # receive the JSON object
        data = self.recv_data()

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

        print(type(obj))
        by = obj.to_wire()
        self.send_data(json.dumps(by).encode('utf-8'))

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

    def close(self) -> None:
        """
        Close the socket.
        """

        self.sock.close()

def test_buffered_socket():
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
    used_seq_num: int
    file_reader: BinaryIO
    host: Optional[str]
    port: Optional[int]

    def __init__(
        self, 
        sock: socket.socket, 
        file_reader: BinaryIO, 
        host: Optional[str], 
        port: Optional[int]
    ) -> None:
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
                break 

            # check the sequence number
            if sequences is not None and packet.header.seq_num not in sequences:
                continue

            # send the packet
            self.used_seq_num = self.seq_num
            #print(f"sending:\n{packet}")
            self.send_packet(packet)

        # send a zero-size packet at the very end
        zsp = FilePacket(FilePacketHeader(self.seq_num + 1, 0), b'\x00' * BLOCK_SIZE)
        #print(f"sending:\n{zsp}")
        self.send_packet(zsp)

        return self.used_seq_num

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
        data = b''
        while len(data) != BLOCK_SIZE + FilePacketHeader.size():
            data += self.sock.recv(BLOCK_SIZE + FilePacketHeader.size() - len(data))

        # parse the packet
        packet = FilePacket.from_bytes(data)

        print(f"recv:\n{packet}")

        # if the packet's size is 0, we're done
        if packet.header.size == 0:
            return None

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

def test_file_packet():
    # create a pair of sockets
    sock1, sock2 = socket.socketpair()

    # create a temporary file with dummy data
    with tempfile.NamedTemporaryFile() as f:
        # write some data to the file
        f.write(b'Hello, world!')
        f.seek(0)

        # wrap the sockets in FilePacketSender and FilePacketReader
        sender = FilePacketSender(sock1, f, None, None)
        with tempfile.NamedTemporaryFile() as f2:
            reader = FilePacketReader(sock2, f2)

            # send the file across the sockets
            sender.send(None)
            for seq in reader.read():
                pass

            f.seek(0)
            f2.seek(0)

            # check that the file is correct
            l = f.read()
            r = f2.read()
            assert l == r

    print("file senders work")

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

    def __init__(self, folder: str, hostname: str):
        self.files = {}
        self.responses = {}
        self.current_ports = {}
        self.running = True
        self.folder = folder
        self.hostname = hostname

    def send_file(self, file: FileInfo) -> None:
        """
        Send a single file across the wire.
        """

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
            with FilePacketSender(file_sock, open(file.filename, "rb"), self.hostname, current_port) as sender:
                last_seq = sender.send()

            # indicate that we've sent the file
            self.sock.send_wiretype(
                FinishedFileRequest(file.filename, last_seq)
            )

            # wait for the response from the server
            while True:
                if file.filename in self.responses:
                    response = self.responses[file.filename]
                    del self.responses[file.filename]
                    break

            # if we received a SendFileReply, we're done
            if isinstance(response, SendFileReply):
                del self.current_ports[file.filename]
                break
            elif isinstance(response, ResendPacketsReply):
                sequences = response.packets
            else:
                raise ValueError("shouldn't get ready for in progress file")

    def run(self):
        # read in all files (recursively) from the folder specified in the second
        # argument        
        for root, dirs, files in os.walk(self.folder):
            for filename in files:
                filename = os.path.join(root, filename)

                # get the checksums for the file
                with open(filename, 'rb') as f:
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

        # create pool object with given number of processes
        pool_obj = futures.ThreadPoolExecutor(max_workers=self.num_concurrent) 

        # create a thread that just sits on the socket and logs its responses
        # into the responses map
        def log_responses():
            while self.running:
                # receive the next packet
                response = self.sock.recv_many_wiretype(
                    ReadyForFileReply, SendFileReply, ResendPacketsReply
                )

                # add the response to the map
                self.responses[response.filename] = response

        # start the thread in the multiprocessing pool
        logger = pool_obj.submit(log_responses)

        # submits individual elements of the iterable "self.files.values()" 
        # as tasks to be processed by the pool
        futures.wait(pool_obj.map(self.send_file, list(self.files.values())))

        # we're done
        logger.cancel()

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
    sock: BufferedSocket
    file_count: int

    def __init__(self, file_root: Path):
        self.files = {}
        self.working_ports = []
        self.file_root = file_root
        self.file_count = 0

    def recv_file(self, sfe: SendFileRequest) -> None:
        filename = sfe.filename
        filesize = sfe.filesize
        port = sfe.port

        # this indicates the size of the file, as well as the server port
        # it's being sent over
        fileinfo = self.files[filename]

        file_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        file_sock.bind(('', port))

        # we are ready
        self.sock.send_wiretype(ReadyForFileReply(fileinfo.filename))

        while True:
            # begin receiving files over the designated port
            # open a UDP listening socket
            path = os.path.join(self.file_root, fileinfo.filename)
            f = open(path, "wb")
            with FilePacketReader(file_sock, f, filesize) as receiver:
                # receive the file
                received_sequences = list(receiver.read())

            # wait for the FinishedFileRequest
            finished_file_request = self.sock.recv_wiretype(FinishedFileRequest)

            # if we've received every sequence number up to the one indicated
            # in the request, we're done
            full_packets = finished_file_request.sequences
            if received_sequences == full_packets:
                # make sure that the file matches the checksum
                with open(path, "rb") as f:
                    checksum = get_checksum(f.read())
                    if checksum != fileinfo.checksum:
                        # ask to resend all packets
                        self.sock.send_wiretype(ResendPacketsReply(fileinfo.filename, full_packets))
                        continue

                # remove the filename from self.files
                del self.files[filename]
                self.sock.send_wiretype(
                    SendFileReply(filename)
                )
                break
            else:
                # we missed a packet
                # ask to resend the missed packets
                diff_packets = list(set(full_packets) - set(received_sequences))
                self.sock.send_wiretype(ResendPacketsReply(filename, diff_packets))

    def run(self):
        # open a listener on the default port
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.bind(('', unwrap_or(find_argument("--port"), DEFAULT_PORT)))

        print("waiting for client...")

        # wait for a connection
        listener.listen(1)
        sock, addr = listener.accept()
        sock = BufferedSocket(sock)
        self.sock = sock

        # wait for an Open request that contains information
        # about the files we're going to receive
        open_request = sock.recv_wiretype(OpenRequest)

        # register the file info
        for filename in open_request.filenames:
            checksum = open_request.checksums[filename]
            self.files[filename] = ServerFileInfo(filename, checksum)
            self.file_count += 1

        # decide how many working ports we want
        self.working_ports = list(range(DEFAULT_FILE_PORT, DEFAULT_FILE_PORT + open_request.num_concurrent))

        # send an Open reply with this information
        sock.send_wiretype(OpenReply(self.working_ports, open_request.num_concurrent))

        # open an executor, for concurrency
        pool = futures.ThreadPoolExecutor(max_workers=open_request.num_concurrent)

        # wait for a SendFileRequest
        while len(self.files) > 0:
            # wait for the send file request
            send_file_request = sock.recv_wiretype(SendFileRequest)

            # spawn a new thread
            pool.submit(self.recv_file, self, send_file_request)

        # connection is now implicitly closed

# test single file
def test_single_file() -> None:
    # create two temporary directories to store the temp
    # file in
    with tempfile.TemporaryDirectory() as send_dir:
        with tempfile.TemporaryDirectory() as recv_dir:
            recv_dir = "."

            # fill a binary file with random info
            path = os.path.join(send_dir, "test.bin")
            data = os.urandom(1024)
            with open(path, "wb") as f:
                f.write(data)

            def run_client(path: Path) -> None:
                # open a client
                client = Client(path, "localhost")

                client.ports = [27851]
                client.files = {
                    "test.bin": FileInfo(path, get_checksum(data))
                }
                client.num_concurrent = 1

                # run the client
                client.send_file("test.bin")

            def run_server(path: Path) -> None:
                # open a server
                server = Server(path)

                server.files = {
                    "test.bin": ServerFileInfo("test.bin", get_checksum(data))
                }
                server.working_ports = [27851]
                server.file_count = 1

                sfe = SendFileRequest(
                    "test.bin",
                    1024,
                    27851
                )

                # run the server
                server.recv_file(sfe)

            # open a thread for the client and
            # another for the server
            pool = futures.ThreadPoolExecutor(max_workers=2)
            print(f"Dirs: {send_dir} {recv_dir}")
            f1 = pool.submit(run_client, send_dir)
            f2 = pool.submit(run_server, recv_dir)
            futures.wait([f1, f2])

            # wait for user input
            input("Press enter to continue...")

            # make sure files are equal
            with open(os.path.join(recv_dir, "test.bin"), "rb") as f:
                if f.read() != data:
                    raise Exception("Files are not equal")

def main() -> None:
    mode = sys.argv[1]
    if mode == "client":
        client = Client(sys.argv[2], sys.argv[3])
        client.run()
    elif mode == "server":
        server = Server(Path(sys.argv[2]))
        server.run()
    elif mode == "test":
        test_buffered_socket()
        test_file_packet()
        test_single_file()
        #test = Test(Client(), Server())
        #test.run()
    else:
        print("Invalid mode: {}".format(mode))
        sys.exit(1)

if __name__ == "__main__":
    main()
