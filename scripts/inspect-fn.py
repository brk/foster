import fileinput
import re

gcroots = []
gcroot_loads = []
nongcroot_loads = []
gcroot_stores = []
nongcroot_stores = []

def summarize():
  print "%10d    gcroots" % len(gcroots)
  print "%10d    gcroot loads" % len(gcroot_loads)
  print "%10d    gcroot stores" % len(gcroot_stores)
  print "%10d nongcroot loads" % len(nongcroot_loads)
  print "%10d nongcroot stores" % len(nongcroot_stores)

def inspect(line):
  if re.search('!fostergcroot !', line):
    gcroots.append(line)
  elif "autoload" in line:
    if "gcroot" in line:
      gcroot_loads.append(line)
    else:
      nongcroot_loads.append(line)
  elif "store " in line:
    if "gcroot" in line:
      gcroot_stores.append(line)
    else:
      nongcroot_stores.append(line)


for line in fileinput.input():
  inspect(line)

summarize()
