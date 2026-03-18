for i in range(int(input())):

    m=list(map(int,input().split()))

    m.remove(max(m))

    print(min(m)*max(m))