for _ in range(int(input())):
	n = int(input())
	print(*[2*i+2*n+2 for i in range(n)])