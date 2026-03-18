for t in range(int(input())):
    n = int(input())
    a = [int(i) for i in input().split()]
    s = 0
    z = 0
    for i in a:
        s += i
        if i==0:
            z += 1
    if s+z == 0:
        print(z+1)
    else:
        print(z)