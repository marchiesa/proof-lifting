import sys
import itertools

n, k, l, c, d, p, nl, np = [int(s) for s in sys.stdin.readline().split(' ')]

total_drink = k * l
drinks_possible = total_drink / nl
drinks_possible = min(drinks_possible, c * d)
drinks_possible = min(drinks_possible, p / np)

print (drinks_possible / n)