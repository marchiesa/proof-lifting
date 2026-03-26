n=int(raw_input())

a=map(int,raw_input().split())

b=[0]*n

for i in xrange(len(a)):
    b[a[i]-1]=i+1

for i in b:
    print i,