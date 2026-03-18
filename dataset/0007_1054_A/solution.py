x, y, z, a, b, c=map(int, raw_input().split())
if a*abs(x-y)>=b*abs(x-y)+b*abs(x-z)+c*3:
	print "YES"
else:
	print "NO"