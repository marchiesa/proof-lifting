s = input()
n = len(s)
u = 0
ans = ''
ans += s[(n - 1) // 2]
u1 = (n - 1) // 2 + 1
u2 = (n - 1) // 2 - 1
u = 1
while u1 < n and u2 >= 0:
    ans += s[u1]
    ans += s[u2]
    u1 += 1
    u2 -= 1
if n % 2 == 0:
    ans += s[-1]
print(ans)