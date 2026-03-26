# import sys
# from collections import deque
# from math import gcd

# print(help(deque))
# 26
# input = lambda: sys.stdin.readline().strip()
# ipnut = input
for i in range(int(input())):
    n,k = map(int,input().split())
    a = list(map(int,input().split()))
    b = list(map(int,input().split()))
    a.sort(reverse=True)
    b.sort()
    for i in range(k):
        if a[-1]>=b[-1]:
            break
        a[-1],b[-1]=b[-1],a[-1]
        a.sort(reverse=True)
        b.sort()
    print(sum(a))

"""
10
10 11 12 13 14 15 16 17 11 11
"""