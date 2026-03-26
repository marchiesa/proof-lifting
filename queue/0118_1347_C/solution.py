def solve():
    #a , b , c = [int(i) for i in raw_input().split(' ')]
    n = int(raw_input())
    t = 1
    a = []
    while n > 0:
        if n % 10 > 0:
            a.append(str((n % 10) * t))
        n /= 10
        t *= 10
    print len(a)
    print " ".join(a)

def main():
    T = int(raw_input())
    for i in xrange(T):
        solve()

main()