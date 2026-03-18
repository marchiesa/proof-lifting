n = input()
status = [0] * 10
s = raw_input()

for ch in s:
    if ch == 'L':
        for i in range(10):
            if not status[i]:
                status[i] = 1
                break
    elif ch == 'R':
        for i in range(10):
            if not status[9-i]:
                status[9-i] = 1
                break
    else:
        i = int(ch)
        status[i]=0

print "".join(map(str,status))