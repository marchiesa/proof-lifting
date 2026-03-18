for i in range(int(input())):
    s = input()
    l = -1
    r = -1
    for i in range(len(s)):
        if s[i] == '1':
            r = i
            if l == -1:
                l = i
                
        ans = 0
    for i in range(l, r):
        if s[i] == '0':
            ans += 1
    print(ans)