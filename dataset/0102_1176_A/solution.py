q = input()
for i in range(q):
    n = input()
    ans = 0
    while(n % 2 == 0):
        ans += 1
        n /= 2
    while(n % 3 == 0):
        ans += 2
        n /= 3
    while(n % 5 == 0):
        ans += 3
        n /= 5
    if(n != 1):
        print -1
    else:
        print ans