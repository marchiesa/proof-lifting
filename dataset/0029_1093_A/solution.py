T=int(input())
for t in range(0,T):
    x=int(input())
    print(1 if x<=7 else x//7+(1 if x%7 else 0))