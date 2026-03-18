n = int(input())
sn = str(n)
count = 0
for i in sn:
    if i == "4" or i == "7":
        count += 1
sc = str(count)
flag = True
for i in sc:
    flag = flag and (i == "4" or i == "7")
if flag:
    print ("YES")
else:
    print ("NO")