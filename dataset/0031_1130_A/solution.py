from collections import defaultdict as dd
import math
def nn():
	return int(input())

def li():
	return list(input())

def mi():
	return map(int, input().split())

def lm():
	return list(map(int, input().split()))


n=nn()

l=lm()

pcount=0
zcount=0
ncount=0

for i in l:
	if i>0:
		pcount+=1
	if i<0:
		ncount+=1
	if i==0:
		zcount+=1

if pcount>=math.ceil(n/2):
	print(1)
elif ncount>=math.ceil(n/2):
	print(-1)
else:
	print(0)