for _ in range(input()):
    a=[int(i) for i in raw_input().split()]
    a.sort()
    val=max(2*a[0],a[1])
    print val*val