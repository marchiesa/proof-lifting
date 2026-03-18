from fractions import gcd
from math import factorial, ceil, sqrt, atan2, log, pi, e, asin,acos, cos, sin, floor, atan
from itertools import *
from fractions import Fraction
import string
import copy
import random
import bisect
from decimal import *
from collections import deque
from sys import *
digs = string.digits + string.ascii_letters

def id_generator(size=20, chars=string.digits):
    return ''.join(random.choice(chars) for _ in range(size))
 
def mp():
    return map(int,str(raw_input()).strip().split())

clear=stdout.flush()

n=input()
l=list(mp())
a=l.count(0)
b=l.count(1)
x=0
y=0
for i in range(n):
	if l[i]==1:
		y+=1
	else:
		x+=1
	if x==a or y==b:
		print i+1
		exit()