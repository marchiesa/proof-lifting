from sys import stdin,stdout

def main():
   n,m=map(int,stdin.readline().split())
   A=[True for _ in range(m)]
   
   for _ in range(n):
      a,b=map(int,stdin.readline().split())
      for i in range(a-1,b):
         A[i]=False
   
   R=[]
   for i in range(m):
      if A[i]:
         R.append(i+1)
   
   stdout.write('{}\n'.format(len(R)))
   stdout.write(" ".join(map(str,R)))


main()