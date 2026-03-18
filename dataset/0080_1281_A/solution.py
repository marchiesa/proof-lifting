import sys
reader = (s.rstrip() for s in sys.stdin)
input = reader.__next__


def solve():
    s = input()
    if s[-1] == "o":
        print("FILIPINO")
    elif s[-1] == "u":
        print("JAPANESE")
    else:
        print("KOREAN")


t = int(input())
for i in range(t):
    solve()