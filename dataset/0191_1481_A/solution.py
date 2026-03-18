import sys
input = sys.stdin.readline
for f in range(int(input())):
    x,y=map(int,input().split())
    s=input()
    p=True
    if x>0 and s.count("R")<x:p=False
    if x<0 and s.count("L")<-x:p=False
    if y>0 and s.count("U")<y:p=False
    if y<0 and s.count("D")<-y:p=False
    if p:print("YES")
    else:print("NO")