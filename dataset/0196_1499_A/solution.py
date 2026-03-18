"""

"""

import sys
from sys import stdin

tt = int(stdin.readline())
ANS = []

for loop in range(tt):

    n,k1,k2 = map(int,stdin.readline().split())
    w,b = map(int,stdin.readline().split())

    r1,r2 = n-k1,n-k2
    
    W = min(k1,k2) + abs(k1-k2)//2
    B = min(r1,r2) + abs(r1-r2)//2

    if W >= w and B >= b:
        ANS.append("YES")
    else:
        ANS.append("NO")

print ("\n".join(ANS))