t = int(input())

for _ in range(t):
	s = list(map(int, input().split()))

	if (min(s[2], s[3]) > max(s[0], s[1])) or (min(s[0], s[1]) > max(s[2], s[3])):
		print('NO')
	else:
		print("YES")