import sys
from math import *
from fractions import *

def main():
    #n = int(sys.stdin.readline().strip())
    n, x = map(int, sys.stdin.readline().split())
    q = list(map(int, sys.stdin.readline().split()))
    w = list(map(int, sys.stdin.readline().split()))
    print("YES"if n == sum([((q[i] + w[n - i - 1]) <= x) for i in range(n)]) else "NO")
    
    
    
    
        
for i in range(int(input()) - 1): 
    main()
    input()
main()