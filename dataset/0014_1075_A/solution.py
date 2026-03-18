n = int(input())
x, y = [int(w) for w in input().split()]

def dist(a, b, x, y):
    return max(abs(x-a), abs(y-b))

if dist(1,1,x,y) <= dist(n,n,x,y):
    print("White")
else:
    print("Black")