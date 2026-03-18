import sys

input = sys.stdin.readline

for _ in range(int(input())):
    n = int(input())
    s = input().rstrip()
    s = [s[i] for i in range(n)]
    s.sort()
    print("".join(s))