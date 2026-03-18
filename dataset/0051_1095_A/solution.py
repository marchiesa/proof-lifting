from sys import stdin
n=int(stdin.readline().strip())
#n,m=map(int,stdin.readline().strip().split())
#s=list(map(int,stdin.readline().strip().split()))
s=input()
ans=""
x=0
y=1
while x<n:
    ans+=s[x]
    x+=y
    y+=1
print(ans)