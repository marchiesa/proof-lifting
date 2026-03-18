t = int(input())
for _ in range(t):
	n = int(input())
	arr = [int(j) for j in input().split()]

	mi = min(arr)
	c = arr.count(mi)

	print(n-c)