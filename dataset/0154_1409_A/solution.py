for _ in range(int(input())):
    a,b = map(int,input().split())
    if(a>b):
        a,b = b,a
    ans = (b-a)//10
    if((b-a)%10!=0):
        ans+=1
    print(ans)