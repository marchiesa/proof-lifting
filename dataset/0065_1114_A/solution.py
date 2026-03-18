from sys import exit, setrecursionlimit, stderr
from functools import reduce
from itertools import *
from collections import defaultdict, Counter
from bisect import bisect

setrecursionlimit(10**7)

def read():
  return int(input())

def reads():
  return [int(x) for x in input().split()]

x, y, z = reads()
a, b, c = reads()

c -= z
if c < 0:
  b += c
b -= y
if b < 0:
  a += b
a -= x

print("YES" if a >= 0 else "NO")