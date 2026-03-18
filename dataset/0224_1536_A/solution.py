import io
import os

from bisect import bisect_left, bisect_right
from collections import Counter, defaultdict, deque
from heapq import heappush, heappop, heapify
from math import gcd, inf


def solve(N, A):
    A.sort()
    B = list(A)
    mx = max(A)
    seen = set(A)
    for x in B:
        for y in B:
            d = abs(x - y)
            if d > mx:
                return "NO"
            if d not in seen:
                B.append(d)
                seen.add(d)

    # return "NO"
    return "YES\n" + str(len(B)) + "\n" + " ".join(map(str, B))


if __name__ == "__main__":
    input = io.BytesIO(os.read(0, os.fstat(0).st_size)).readline

    TC = int(input())
    for tc in range(1, TC + 1):
        (N,) = [int(x) for x in input().split()]
        A = [int(x) for x in input().split()]
        ans = solve(N, A)
        print(ans)