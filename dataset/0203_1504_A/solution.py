import sys
input = iter(sys.stdin.read().splitlines()).__next__


def solve():
    s = input()
    if set(s) == {'a'}:
        return "NO"
    elif ''.join(reversed(s+'a')) == s + 'a':
        return 'YES\na' + s
    return 'YES\n' + s + 'a'

t = int(input())
output = []
for _ in range(t):
    output.append(solve())
print(*output, sep="\n")