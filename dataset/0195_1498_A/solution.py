import math
t=int(input())
for _ in range(t):
  n=int(input())
  
  while True:
    msum=0
    for i in str(n):
      msum+=int(i)
    if math.gcd(msum,n)>1:
      print(n)
      break
    n+=1