for t in range(int(raw_input())):
	a,b,k=map(int,raw_input().split())
	f=k/2
	ans=a*f-b*f
	if k&1:
		ans+=a
	print ans