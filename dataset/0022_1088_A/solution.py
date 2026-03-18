from sys import stdin, stdout
from math import sin, tan, cos, pi, atan2, sqrt, acos, atan, factorial


n = int(stdin.readline())
label = 0

for a in range(1, n + 1):
    if label:
        break
    
    for b in range(1, a + 1):
        if a % b == 0 and a * b > n and a // b < n:
            stdout.write(str(a) + ' ' + str(b))
            label = 1
            break

if not label:
    stdout.write('-1\n')