import sys
input=sys.stdin.buffer.readline

for t in range(int(input())):
  N=int(input())
  print((1<<(N.bit_length()-1))-1)