from collections import *
from sys import stdin,stderr
def rl():
    return [int(w) for w in stdin.readline().split()]

t, = rl()
for _ in range(t):
    n, = rl()
    print(*range(1, n+1))