#Bhargey Mehta (Junior)
#DA-IICT, Gandhinagar
import sys, math
mod = 10**9

def solve(test_index):
    n = int(input())
    a = sorted(map(int, input().split()))
    ans = 'YES'
    for i in range(1, n):
        if a[i]-a[i-1] >= 2:
            ans = 'NO'
    print(ans)
    return

if 'PyPy' not in sys.version:
    sys.stdin = open('input.txt', 'r')

sys.setrecursionlimit(100000)
num_tests = 1
num_tests = int(input())
for test in range(1, num_tests+1):
    #print("Case #{}: ".format(test), end="")
    solve(test)