t = int(input())
answers = []
for _ in range(t):
    s = (input())
    ans = []
    for i, c in enumerate(s):
        if i % 2 == 0:  # Alice
            ans.append('a' if c != 'a' else 'b')
        else:
            ans.append('z' if c != 'z' else 'y')
    answers.append(''.join(ans))
print('\n'.join(answers))