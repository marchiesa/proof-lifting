for _ in range(input()):
    n=input()
    maxx=10**18
    pos=-1
    a=[int(i) for i in raw_input().split()]
    d={}
    for i in a:
        d[i]=d.get(i,0)+1
    for i in range(n):
        if d[a[i]]==1 and a[i]<maxx:
            maxx=a[i]
            pos=i+1
    print pos