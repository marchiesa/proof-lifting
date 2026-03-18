import math
# helpful:
# r,g,b=map(int,input().split())
#list1 = input().split()
#for i in range(len(list1)):
#    list1[i] = int(list1[i])
# print(list1)
# arr = [[0 for x in range(columns)] for y in range(rows)]

n = int(input())
list1 = input().split()
for i in range(len(list1)):
    list1[i] = int(list1[i])
m = int(input())
list2 = input().split()
for i in range(len(list2)):
    list2[i] = int(list2[i])
list1.sort()
list2.sort()
print(str(list1[n-1]) + " " + str(list2[m-1]))