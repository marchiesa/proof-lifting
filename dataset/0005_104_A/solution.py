#!/usr/bin/python

n = int(raw_input())

vals = [[10], [2], [3], [4], [5], [6], [7], [8], [9], [10], [10], [10], [1, 11]]

r = 0
for i in xrange(len(vals)):
	x = vals[i]
	for y in x:
		if y + 10 == n:
			r += 3
			if i:
				r += 1
print r