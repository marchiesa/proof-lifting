#      
import collections, atexit, math, sys, bisect 

sys.setrecursionlimit(1000000)
def getIntList():
    return list(map(int, input().split()))    

isdebug = False
try :
    #raise ModuleNotFoundError
    import numpy
    def dprint(*args, **kwargs):
        #print(*args, **kwargs, file=sys.stderr)
        # in python 3.4 **kwargs is invalid???
        print(*args,  file=sys.stderr)
    dprint('debug mode')
    isdebug = True
except Exception:
    def dprint(*args, **kwargs):
        pass



inId = 1
outId = 0
if not isdebug:
    inId = 0
    outId = 0
if inId>0:
    dprint('use input', inId)
    try:
        f = open('input'+ str(inId) + '.txt', 'r')
        sys.stdin = f #标准输出重定向至文件
    except Exception:
        dprint('invalid input file')
if outId>0:
    dprint('use output', outId)
    try:
        f = open('stdout'+ str(outId) + '.txt', 'w')
        sys.stdout = f #标准输出重定向至文件
    except Exception:
        dprint('invalid output file')
        
    atexit.register(lambda :sys.stdout.close())     #idle 中不会执行 atexit
    
N, = getIntList()
#print(N)
zs = []
for i in range(N):
    zs.append( input() )
dprint(zs)
r = 0
for a in range(1,N-1):
    for b in range(1,N-1):
        if zs[a][b] !='X': continue
        if zs[a-1][b-1]=='X' and zs[a-1][b+1]=='X' and zs[a+1][b-1]=='X' and zs[a+1][b+1] =='X':
            r +=1




print(r)