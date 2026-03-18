mod=10**9+7
#import resource
#resource.setrlimit(resource.RLIMIT_STACK, [0x100000000, resource.RLIM_INFINITY])
#import threading
#threading.stack_size(2**27)
#import sys
#sys.setrecursionlimit(10**6)
#fact=[1]
#for i in range(1,1000001):
#    fact.append((fact[-1]*i)%mod)
#ifact=[0]*1000001
#ifact[1000000]=pow(fact[1000000],mod-2,mod)
#for i in range(1000000,0,-1):
#    ifact[i-1]=(i*ifact[i])%mod
from sys import stdin, stdout
import bisect
from bisect import bisect_left as bl              #c++ lowerbound bl(array,element)
from bisect import bisect_right as br             #c++ upperbound
import itertools
import collections
import math
import heapq
#from random import randint as rn
#from Queue import Queue as Q
def modinv(n,p):
    return pow(n,p-2,p)
def ncr(n,r,p):                        #for using this uncomment the lines calculating fact and ifact
    t=((fact[n])*((ifact[r]*ifact[n-r])%p))%p
    return t
def ain():                           #takes array as input
    return list(map(str,sin().split()))
def sin():
    return input().strip()
def GCD(x,y):
    while(y):
        x, y = y, x % y
    return x
"""*******************************************************"""
def main():
    a=int(input())
    b=int(input())
    c=int(input())
    d=int(input())
    e=int(input())
    f=int(input())
    if(e>f):
        x=min(a,d)
        a-=x
        d-=x
        s=(x*e)+(min(b,c,d)*f)
    else:
        x=min(b,c,d)
        b-=x
        c-=x
        d-=x
        s=(x*f)+(min(a,d)*e)
    print s

######## Python 2 and 3 footer by Pajenegod and c1729
py2 = round(0.5)
if py2:
    from future_builtins import ascii, filter, hex, map, oct, zip
    range = xrange

import os, sys
from io import IOBase, BytesIO

BUFSIZE = 8192
class FastIO(BytesIO):
    newlines = 0
    def __init__(self, file):
        self._file = file
        self._fd = file.fileno()
        self.writable = "x" in file.mode or "w" in file.mode
        self.write = super(FastIO, self).write if self.writable else None

    def _fill(self):
        s = os.read(self._fd, max(os.fstat(self._fd).st_size, BUFSIZE))
        self.seek((self.tell(), self.seek(0,2), super(FastIO, self).write(s))[0])
        return s
    def read(self):
        while self._fill(): pass
        return super(FastIO,self).read()

    def readline(self):
        while self.newlines == 0:
            s = self._fill(); self.newlines = s.count(b"\n") + (not s)
        self.newlines -= 1
        return super(FastIO, self).readline()

    def flush(self):
        if self.writable:
            os.write(self._fd, self.getvalue())
            self.truncate(0), self.seek(0)

class IOWrapper(IOBase):
    def __init__(self, file):
        self.buffer = FastIO(file)
        self.flush = self.buffer.flush
        self.writable = self.buffer.writable
        if py2:
            self.write = self.buffer.write
            self.read = self.buffer.read
            self.readline = self.buffer.readline
        else:
            self.write = lambda s:self.buffer.write(s.encode('ascii'))
            self.read = lambda:self.buffer.read().decode('ascii')
            self.readline = lambda:self.buffer.readline().decode('ascii')

sys.stdin, sys.stdout = IOWrapper(sys.stdin), IOWrapper(sys.stdout)
input = lambda: sys.stdin.readline().rstrip('\r\n')

if __name__ == '__main__':
    main()
#threading.Thread(target=main).start()