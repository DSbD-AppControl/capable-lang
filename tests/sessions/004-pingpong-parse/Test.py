import socket as s
import subprocess
import tempfile

with s.socket(s.AF_UNIX, s.SOCK_STREAM) as sock:
    sock.bind("/tmp/capable-test.sock")
    sock.listen()
    print("Listening")
    conn, addr = sock.accept()
    print("Spawing")
    with conn:
        with subprocess.Popen(
            ["./build/exec/bar"],
            stdin =subprocess.PIPE,
            stdout=subprocess.PIPE
        ) as proc:
            i = conn.recv(1024)
#            print("Received")
#            print(i)
            proc.stdin.write(i)
            proc.stdin.flush()
            o = proc.stdout.readline()
#            print("Sending")
#            print(o)
            conn.sendall(o)
