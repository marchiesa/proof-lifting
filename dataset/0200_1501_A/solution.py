import math
t = int(input())
for _ in range(t):
    n = int(input())

    aas = [0]
    bs = [0]

    for i in range(n):
        ai,bi = list(map(int,input().split()))
        aas.append(ai)
        bs.append(bi)

    tms = list(map(int,input().split()))



    """actual_arrival = [0]
    actual_departure = [0]"""

    current_time = 0
    for i in range(1,n+1):
        travel_time = aas[i] - bs[i-1] + tms[i-1]
        current_time += travel_time

        if i == n:
            break

        current_time += math.ceil((bs[i] - aas[i]) / 2)
        if current_time < bs[i]:
            current_time = bs[i]

    print(current_time)