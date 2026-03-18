n = int(raw_input())
arr = map(int, raw_input().split())

ans = []
cnt = 0
for i in xrange(len(arr)):
    if i == 0:
        cnt = 1
    elif arr[i] == 1:
        ans.append(cnt)
        cnt = 1
    else:
        cnt += 1

ans.append(cnt)
print len(ans)
print ' '.join(map(str, ans))