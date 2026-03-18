t = int(input())
for i in range(t):
	n, m = map(int, input().split())
	a = list(map(int, input().split()))
	s = sum(a)
	print(min(m, s))