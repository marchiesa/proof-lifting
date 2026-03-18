import sys

def read_ints():
    return [int(i) for i in sys.stdin.readline().strip().split()]

def read_int():
    return int(sys.stdin.readline().strip())

n = read_int()
for i in range(n):
    h = read_int()
    strengths = read_ints()
    min_hero = min(strengths)
    print(sum(1 for s in strengths if s > min_hero))