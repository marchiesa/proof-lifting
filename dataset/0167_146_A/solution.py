import sys

n = int(raw_input())
s = raw_input()
a = 0
b = 0
for i in range(0, len(s)):
	if s[i] != '4' and s[i] != '7':
		print 'NO'
		sys.exit()
	if i < len(s) / 2:
		a += int(s[i])
	elif i >= len(s) / 2:
		b += int(s[i])
if a == b:
	print 'YES'
else:
	print 'NO'