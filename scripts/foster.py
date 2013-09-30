#!/usr/bin/env python

from run_cmd import run_command
import run_test
import sys
import optparse
import os
import os.path

def parse_cmdline():
    parser = optparse.OptionParser("usage: %prog [options] path_to_module.foster")

    parser.add_option("-e", "--execute_from",
                        action="store",
                        dest="execute_from",
                        default=".",
                        help="Execute fosterparse (etc) from this directory")

    (options, args) = parser.parse_args()
    if len(args) != 1:
        parser.error("missing input module source path")
    return (options, args)

def main():
    (options, input_paths) = parse_cmdline()

    print options
    input_path = input_paths[0]

    dirs = {
        'out.s' : os.path.join('fc-output', 'out.s'),
        'a.out' : os.path.join('fc-output', 'a.out'),
    }
    for bin in ['fosterparse', 'fostercheck', 'fosterlower',
                'libfoster.bc', 'libcpuid.a', 'libfoster_main.o',
                'libchromium_base.a']:
        dirs[bin] = os.path.join(options.execute_from, bin)

    # running fosterparse on a source file produces a ParsedAST
    (s1, e1) = run_command(['fosterparse', input_path, 'out.pb'], dirs, input_path, strictrv=True)

    # running fostercheck on a ParsedAST produces an ElaboratedAST
    (s2, e2) = run_command(['fostercheck', 'out.pb', 'out2.pb'], dirs, input_path, strictrv=True)

    # running fosterlower on a ParsedAST produces a bitcode Module
    # linking a bunch of Modules produces a Module
    # Running opt on a Module produces a Module
    # Running llc on a Module produces an assembly file
    (s3, e3) = run_command(['fosterlower', 'out2.pb'], dirs, input_path, strictrv=True)

    # Running gcc on an assembly file compiles (and links) it.
    (s4, e4) = run_command('g++ out.s %s %s -o a.out' % (run_test.get_static_libs(),
                                                         run_test.get_link_flags()),
                        dirs, input_path, strictrv=True)

if __name__ == "__main__":
    main()
