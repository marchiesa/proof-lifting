from sys import *

b = [stdin.readline()[:-1] for i in range(3)]
bad = False
for i in xrange(0,3):
    for j in xrange(0,3):
        if b[i][j] == 'X' and b[2-i][2-j] != 'X':
            bad = True
if bad: print "NO"
else: print "YES"