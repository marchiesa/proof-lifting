from collections import Counter, defaultdict, deque
import bisect
from sys import stdin, stdout
from itertools import repeat, permutations
import math
import heapq


def inp(force_list=False):
    re = map(int, raw_input().split())
    if len(re) == 1 and not force_list:
        return re[0]
    return re

def inst():
    return raw_input().strip()

def gcd(x, y):
   while(y):
       x, y = y, x % y
   return x

MOD = 998244353

def qmod(a, b, mod=MOD):
    res = 1
    while b:
        if b&1:
            res = (res*a)%mod
        b >>= 1
        a = (a*a)%mod
        # print b
    return res

def inv(a):
    return qmod(a, MOD-2)


def my_main():
    kase = inp()
    pans = []
    for _ in range(kase):
        n = inp()
        ans = inp()
        ans.sort()
        ans[0], ans[-1] =  ans[-1], ans[0]
        for i in range(1, n-1):
            ans[i*2], ans[i*2+1] = ans[i*2+1], ans[i*2]
        pans.append(' '.join(map(str, ans)))
    # print ans
    print '\n'.join(pans)




my_main()