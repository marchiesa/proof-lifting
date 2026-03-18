def main():
    n, m = map(int, input().split(' '))
    c = [int(x) for x in input().split(' ')]
    a = [int(x) for x in input().split(' ')]
    a.reverse()
    c.reverse()

    ans = 0
    while a and c:
        if a[-1] >= c[-1]:
            ans += 1
            a.pop()
        c.pop()
    print(ans)

if __name__ == '__main__':
    main()