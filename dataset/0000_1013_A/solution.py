n = input()
v = map(int, raw_input().split(' '))
b = map(int, raw_input().split(' '))

v_sum = sum(v)
b_sum = sum(b)

if b_sum <= v_sum:
	print "Yes"
else:
	print "No"