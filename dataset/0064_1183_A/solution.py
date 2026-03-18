a = int(raw_input())

def sum_digits(x):
    return 0 if x == 0 else x % 10 + sum_digits(x / 10)

while sum_digits(a) % 4 != 0:
    a += 1

print(a)