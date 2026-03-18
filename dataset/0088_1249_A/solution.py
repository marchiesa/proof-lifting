q = int(input())
for i in range(q):
    n = int(input())
    a = list(map(int, input().split()))
    b = [0 for i in range(100 + 2)]
    for i in range(n):
        b[a[i]] += 1
    flag = False
    for i in range(1, 101):
        if b[i] == 1 and (b[i + 1] == 1 or b[i - 1] == 1):
            flag = True
    if flag:
        print(2)
    else:
        print(1)