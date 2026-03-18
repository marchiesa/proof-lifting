import sys,math
from collections import Counter,deque,defaultdict
from bisect import bisect_left,bisect_right 
mod = 10**9+7
INF = float('inf')
def inp(): return int(sys.stdin.readline())
def inpl(): return list(map(int, sys.stdin.readline().split()))

for _ in range(inp()):
    n,x = inpl()
    if n <= 2:
        print(1)
    else:
        n -= 3
        print(n//x+2)