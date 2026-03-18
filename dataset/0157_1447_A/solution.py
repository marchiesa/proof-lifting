import io,os
from math import *
input = io.BytesIO(os.read(0,os.fstat(0).st_size)).readline

for _ in range(int(input())):
	n = int(input())
	print(n)
	print(*list(range(1,n+1)))