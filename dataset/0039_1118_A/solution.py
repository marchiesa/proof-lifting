# -*- coding: utf-8 -*-
"""
Created on Tue Feb 19 20:06:40 2019

@author: HP
"""

for _ in range(int(input())):
    n,a,b = map(int,input().split())
    two = 2*a
    ans = (n//2)*(min(two,b))
    ans += (n%2)*(a)
    print(ans)