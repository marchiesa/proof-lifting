for _ in range(input()):
    n=input()
    if n==1:
        print 0
    elif n==2:
        print 1
    elif n%2==0 or n==3:
        print 2
    else:
        print 3