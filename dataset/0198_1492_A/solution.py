for _ in range(input()):
    p,a,b,c=[int(i) for i in raw_input().split()]
    print min((a-p%a)%a,(b-p%b)%b,(c-p%c)%c)