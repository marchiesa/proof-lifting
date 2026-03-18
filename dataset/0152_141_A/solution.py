import sys
a = sys.stdin.readline().strip()
b = sys.stdin.readline().strip()
c = sys.stdin.readline().strip()
ab = list(a+b)
c_ = list(c)
ab.sort()
c_.sort()
if "".join(ab) == "".join(c_):
    print 'YES'
else:
    print 'NO'