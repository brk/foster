import sys

def parse_args(args):
  args = args.split()
  argv = sys.argv[1:]

  if len(args) != len(argv):
    print "expected %d args (%s),\n     got %d %s" % (
        len(args), ' '.join(args), len(argv), argv)
    sys.exit(1)

  return dict(zip(args, argv))

def example_usage():
  for var,val in parse_args("arg1 arg2").items():
    exec "%s = '%s'" % (var, val)
  print arg1
  print arg2

if __name__ == "__main__":
  example_usage()
