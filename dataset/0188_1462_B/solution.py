import sys
input = sys.stdin.readline
for _ in range(int(input())):
    n = int(input())
    s = input().strip()
    if s[0:4] == '2020' or s[-4:] == '2020' or s[0] == '2' and s[-3:] == '020' or s[0:2] == '20' and s[-2:] == '20' or s[0:3] == '202' and s[-1] == '0':
        print('YES')
    else:
        print('NO')