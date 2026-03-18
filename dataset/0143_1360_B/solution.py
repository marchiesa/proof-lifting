for _ in range(input()):
    n=input()
    a=[int(i) for i in raw_input().split()]
    a.sort()
    val=10**18
    for i in range(1,n):
        val=min(val,a[i]-a[i-1])
    print val