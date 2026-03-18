T = int(raw_input())

def solve(line):
    line = list(line)
    n = len(line)

    step = 0
    while True:
        flag = False
        for i in xrange(n - 1, -1, -1):
            if line[i] == 'A':
                if i + 1 < n and line[i + 1] == 'P':
                    line[i + 1] = 'A'
                    flag = True
        #print ''.join(line)
        if flag == False:
            break
        step += 1
    return step

assert solve('PPAP') == 1
assert solve('APPAPPPAPPPP') == 4
assert solve('AAP') == 1
assert solve('PA') == 0
assert solve('AA') == 0

for case_ in xrange(T):
    n = int(raw_input())
    line = raw_input().strip()
    print solve(line)