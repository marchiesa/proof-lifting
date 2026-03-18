import sys

lines = [a.strip() for a in sys.stdin.readlines()[1:]]

#print lines

while True:
  a = False
  for i in range(len(lines)):
    if lines[i][0]=="*":
      a=True
      break
  if not a:
    #print "a"
    lines = [l[1:] for l in lines]
    continue
  b = False
  for i in range(len(lines)):
    if lines[i][-1]=="*":
      b=True
      break
  if not b:
    lines = [l[:-1] for l in lines]
    #print "b"
    continue
  c = False
  if lines[0] == "."*len(lines[0]):
    lines = lines[1:]
    #print "c"
    continue
  if lines[-1] == "."*len(lines[0]):
    lines = lines[:-1]
    #print "d"
    continue
  break

sys.stdout.write("\n".join(lines))