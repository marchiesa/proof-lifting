#!/usr/bin/env python
import os
import sys
from io import BytesIO, IOBase


def main():
    for _ in range(int(input())):
        n,m = map(int,input().split())
        s = input()
        INF = 10 ** 10
        last1 = -INF
        left = []
        for i in range(len(s)):
            if s[i] == "1":
                last1 = i
            left.append(last1)
        last1 = INF
        right = []
        for i in range(len(s) - 1, -1, -1):
            if s[i] == "1":
                last1 = i
            right.append(last1)
        right.reverse()
        ans = []
        for i in range(n):
            if left[i] == i:
                ans.append("1")
            elif (i - left[i] <= m or right[i] - i <= m) and i - left[i] != right[i] - i:
                ans.append("1")
            else:
                ans.append("0")
        print("".join(ans))


# region fastio

BUFSIZE = 8192


class FastIO(IOBase):
    newlines = 0

    def __init__(self, file):
        self._fd = file.fileno()
        self.buffer = BytesIO()
        self.writable = "x" in file.mode or "r" not in file.mode
        self.write = self.buffer.write if self.writable else None

    def read(self):
        while True:
            b = os.read(self._fd, max(os.fstat(self._fd).st_size, BUFSIZE))
            if not b:
                break
            ptr = self.buffer.tell()
            self.buffer.seek(0, 2), self.buffer.write(b), self.buffer.seek(ptr)
        self.newlines = 0
        return self.buffer.read()

    def readline(self):
        while self.newlines == 0:
            b = os.read(self._fd, max(os.fstat(self._fd).st_size, BUFSIZE))
            self.newlines = b.count(b"\n") + (not b)
            ptr = self.buffer.tell()
            self.buffer.seek(0, 2), self.buffer.write(b), self.buffer.seek(ptr)
        self.newlines -= 1
        return self.buffer.readline()

    def flush(self):
        if self.writable:
            os.write(self._fd, self.buffer.getvalue())
            self.buffer.truncate(0), self.buffer.seek(0)


class IOWrapper(IOBase):
    def __init__(self, file):
        self.buffer = FastIO(file)
        self.flush = self.buffer.flush
        self.writable = self.buffer.writable
        self.write = lambda s: self.buffer.write(s.encode("ascii"))
        self.read = lambda: self.buffer.read().decode("ascii")
        self.readline = lambda: self.buffer.readline().decode("ascii")


sys.stdin, sys.stdout = IOWrapper(sys.stdin), IOWrapper(sys.stdout)
input = lambda: sys.stdin.readline().rstrip("\r\n")

# endregion

if __name__ == "__main__":
    main()