s=raw_input().rstrip('\r').lower()
t=raw_input().rstrip('\r').lower()
if s<t:
    print -1
elif t<s:
    print 1
else:
    print 0