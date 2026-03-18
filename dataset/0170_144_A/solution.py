res = 10**100

def try_max():
    global res, a
    cur = 0
    na = [i for i in a]
    pmx = -1
    for i in range(n):
        if na[i] == mx:
            pmx = i
            break
    for i in range(pmx-1, -1, -1):
        na[i], na[i+1] = na[i+1], na[i]
        cur += 1
    pmn = -1
    for i in range(n-1, -1, -1):
        if na[i] == mn:
            pmn = i
            break
    for i in range(pmn, n-1):
        cur += 1
        na[i], na[i+1] = na[i+1], na[i]
    res = min(res, cur)
    
def try_min():
    global res, a
    cur = 0
    na = [i for i in a]
    pmn = -1
    for i in range(n-1, -1, -1):
        if na[i] == mn:
            pmn = i
            break
    for i in range(pmn, n-1):
        cur += 1
        na[i], na[i+1] = na[i+1], na[i]
    pmx = -1
    for i in range(n):
        if na[i] == mx:
            pmx = i
            break
    for i in range(pmx-1, -1, -1):
        na[i], na[i+1] = na[i+1], na[i]
        cur += 1
    res = min(res, cur)

n = int(raw_input())
a = [int(i) for i in raw_input().split()]
mn, mx = min(a), max(a)
try_min()
try_max()
print res