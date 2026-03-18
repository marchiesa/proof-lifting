import sys
input=sys.stdin.readline
t=int(input())
for you in range(t):
    n=int(input())
    l=input().split()
    li=[int(i) for i in l]
    odd=[]
    even=[]
    for i in li:
        if(i%2):
            odd.append(i)
        else:
            even.append(i)
    for i in odd:
        print(i,end=" ")
    for i in even:
        print(i,end=" ")
    print()