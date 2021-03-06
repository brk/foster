#!/usr/bin/env python3

from optparse import OptionParser

from run_cmd import *

def default_exename(path):
  import platform
  return path + {
    'Darwin': "",
    'Linux':  "",
    'Windows': ".exe"
  }[platform.system()]

def shared(lib):
  import platform
  suffix = {
    'Darwin': ".dylib",
    'Linux':  ".so",
    'Windows': '.dll'
  }[platform.system()]
  return lib + suffix

def is64bit():
  import platform
  return platform.machine().endswith('64')

def pinobjdirname():
  if is64bit():
    return "obj-intel64"
  else:
    return "obj-ia32"

def run_pin(options, args):
  pinexe = os.path.join(options.pindir, default_exename('pin'))
  pintool = os.path.join(options.pindir, 'source', 'tools', 'SimpleExamples',
                         pinobjdirname(), shared('opcodemix'))

  if not os.path.exists(pinexe):
    raise Exception("It look like " + pinexe + " + does not exist ... :-(")

  with open(os.devnull, 'w') as devnull:
    run_cmd(' '.join([pinexe, '-injection', 'child', '-t', pintool, '--'] + args), stdout=devnull, stderr=devnull)
  # writes output to opcodemix.out

  if options.outfile is not None:
    os.rename('opcodemix.out', options.outfile)


if __name__ == '__main__':
  parser = OptionParser()
  parser.add_option("--pindir", dest="pindir", action="store", default=None,
                    help="Path to the `pin` root")
  parser.add_option("--output", dest="outfile", action="store", default=None,
                    help="Name for the output (default: opcodemix.out)")
  (options, args) = parser.parse_args()
  if options.pindir is None:
    print("`--pindir <path>` is required")
    sys.exit(1)

  run_pin(options, args)
