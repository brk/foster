#!/usr/bin/env python

import sys, re, os

if len(sys.argv) < 2:
    fp = sys.stdin
else:
    fp = open(sys.argv[1], 'rU')

def call_dc(pgm):
    (send, recv) = os.popen2('dc', 't', 0)
    send.write(pgm)
    send.close()
    data = recv.read().strip()
    recv.close()

    return data.replace('\\\n', '')

def compute_qtodec_output(rec):
    if rec['input'][0].find('/') < 0:
        num = rec['input'][0]
        den = '1'
    else:
        (num, den) = rec['input'][0].split('/')
    rdx = int(rec['input'][1])
    prec = int(rec['input'][2])
    
    if num[0] == '-':
        num = num[1:] + '_'
    else:
        num += ' '
    
    pgm = '%dk%do%s%s/p' % ( prec + 15, rdx,
                             num, den )
    
    result = call_dc(pgm)
    if result.find(' ') >= 0:
        result = unpack_radix(result, rdx)
    
    if result[:2] == '-.':
        result = '-0.' + result[2:]
    elif result[0] == '.':
        result = '0' + result
    
    if result[-1] == '.':
        if prec > 0:
            result += ('0' * prec)
        else:
            result = result[:-1]
    
    if result == '0' and prec > 0:
        result = '0.' + ('0' * prec)
    
    pos = result.find('.')
    if pos >= 0 and pos + prec + 1 < len(result):
        result = result[:(pos + prec + 1)]
        if result[-1] == '.':
            result = result[:-1]
    
    if re.match('-0(\.0+)?$', result):
        result = result[1:]
    
    rec['output'] = [result]
    return result

def unpack_radix(s, rdx):
    sig = s[0]
    
    if s.find('.') < 0:
        fst = s
        sec = ''
    else:
        (fst, sec) = str.split(s, '.')
    
    dfst = [ int(x) for x in fst.split(' ') if x not in ('', '-') ]
    dsec = [ int(x) for x in sec.split(' ') if x not in ('', '-') ]
    
    sfst = str.join('', [ (x < 10 and chr(x + ord('0'))) or chr(x - 10 + ord('A'))
                          for x in dfst ])
    ssec = str.join('', [ (x < 10 and chr(x + ord('0'))) or chr(x - 10 + ord('A'))
                          for x in dsec ])

    if sig == '-':
        return sig + sfst + '.' + ssec
    else:
        return sfst + '.' + ssec

tests = [] ; line_num = 0
for line in fp.readlines():
    line_num += 1
    if re.match('\s*(#.+)?$', line):
        continue
    
    match = re.match('(\w+):(.+):(.*)$', line.strip())
    if match:
        rec = { 'tag': match.group(1),
                'input': match.group(2).split(','),
                'output': match.group(3).split(','),
                'line': line_num }
        
        if rec['tag'] == 'qtodec':
            try:
                compute_qtodec_output(rec)
            except:
                print >> sys.stderr, "failed at line %d" % rec['line']
                raise
        
        tests.append(rec)

fp.close()

for rec in tests:
    print '%s:%s:%s' % (rec['tag'],
                        str.join(',', rec['input']),
                        str.join(',', rec['output']))

# Here there be dragons
