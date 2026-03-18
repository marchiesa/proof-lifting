import sys
import math
from itertools import permutations
from bisect import bisect_left
import heapq
from collections import deque
def II():
	return int(sys.stdin.readline())
 
def LI():
	return list(map(int, sys.stdin.readline().split()))
 
def MI():
	return map(int, sys.stdin.readline().split())
 
def SI():
	return sys.stdin.readline().strip()
 
def FACT(n, mod):
    s = 1
    facts = [1]
    for i in range(1,n+1):
        s*=i
        s%=mod
        facts.append(s)
    return facts[n]
 
def C(n, k, mod):
    return (FACT(n,mod) * pow((FACT(k,mod)*FACT(n-k,mod))%mod,mod-2, mod))%mod
 
def lcm(a,b):
    return abs(a*b) // math.gcd(a, b)

for _ in range(II()):
    n,m,x = MI()
    x-=1
    r = x//n
    c = x%n
    print(c*m+r+1)