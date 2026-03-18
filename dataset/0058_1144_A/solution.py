n = int(input())
for i in range(n):
    a = input()
    b = [0 for j in range(26)]
    for j in a:
        b[ord(j)-97]+=1
    y = 0
    x = 0
    b.append(0)
    for i in b:
        if i>1:
            print("No")
            break
        if y==0 and i==1:
            y=1
        if y==1 and i==0:
            x=1
            y=0
        if x==1 and i>=1:
            print("No")
            break
    else:
        print("Yes")