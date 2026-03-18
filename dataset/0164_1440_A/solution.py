for _ in range(int(input())):
    n, c0, c1, h = map(int, input().split())
    s = input()
    c1 = min(c1, h+c0)
    c0 = min(c0, h+c1)
    print(s.count("0")*c0 + s.count("1")*c1)