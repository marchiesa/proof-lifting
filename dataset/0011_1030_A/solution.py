n = int(input())

xs = [int(x) for x in input().split()]

if all(x == 0 for x in xs):
    print("EASY")
else:
    print("HARD")