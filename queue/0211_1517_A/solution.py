#from typing import List, Set, Dict, Tuple, Text, Optional
from collections import deque
from types import GeneratorType
import os
import sys
import math
import heapq
from atexit import register
from io import BytesIO
import __pypy__  # type: ignore

#########
# INPUT #
#########


class Input(object):
  def __init__(self):
    if 'CPH' not in os.environ:
      sys.stdin = BytesIO(os.read(0, os.fstat(0).st_size))
      sys.stdout = BytesIO()
      register(lambda: os.write(1, sys.stdout.getvalue()))

  def rawInput(self):
    # type: () -> str
    return sys.stdin.readline().rstrip('\r\n')

  def readInt(self):
    return int(self.rawInput())

##########
# OUTPUT #
##########


class Output(object):
  def __init__(self):
    self.out = __pypy__.builders.StringBuilder()

  def write(self, text):
    # type: (str) -> None
    self.out.append(str(text))

  def writeLine(self, text):
    # type: (str) -> None
    self.write(str(text) + '\n')

  def finalize(self):
    if sys.version_info[0] < 3:
      os.write(1, self.out.build())
    else:
      os.write(1, self.out.build().encode())

###########
# LIBRARY #
###########


def bootstrap(f, stack=[]):
  # Deep Recursion helper.
  # From: https://github.com/cheran-senthil/PyRival/blob/c1972da95d102d95b9fea7c5c8e0474d61a54378/docs/bootstrap.rst
  # Usage:

  # @bootstrap
  # def recur(n):
  #   if n == 0:
  #     yield 1
  #   yield (yield recur(n-1)) * n
  def wrappedfunc(*args, **kwargs):
    if stack:
      return f(*args, **kwargs)
    else:
      to = f(*args, **kwargs)
      while True:
        if type(to) is GeneratorType:
          stack.append(to)
          to = next(to)
        else:
          stack.pop()
          if not stack:
            break
          to = stack[-1].send(to)
      return to

  return wrappedfunc


#########
# LOGIC #
#########


def main(inp, out):
  # type: (Input, Output) -> any
  n = inp.readInt()
  for _ in range(n):
    x = inp.readInt()
    if x % 2050:
      out.writeLine(-1)
    else:
      mult = x // 2050
      nums = 0
      while mult:
        nums += mult % 10
        mult //= 10
      out.writeLine(nums)


###############
# BOILERPLATE #
###############

output_obj = Output()
main(Input(), output_obj)
output_obj.finalize()