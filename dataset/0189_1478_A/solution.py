T = int(input())

for _ in range(T):
    N = int(input())
    A = [int(_) for _ in input().split()]
    freq = [0] * (N + 1)

    for a in A:
        freq[a] += 1

    print(max(freq))