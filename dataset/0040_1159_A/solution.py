n = int(input())
s = input()
ans = 0
for si in s:
    if si == '-':
        if ans > 0:
            ans -= 1
    else:
        ans += 1
print(ans)