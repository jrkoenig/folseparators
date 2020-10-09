
import re, sys
from collections import Counter

def parse(f, ng):
    in_model = False
    symbol_arbitrary = re.compile('^; \\(([a-zA-z0-9]+) .* is arbitrary$')
    symbol_defined = re.compile('(?:\\(not |\\(= )?\\(([a-zA-z0-9]+) .*$')
    not_golden = ng.split(",")

    arbitrary = Counter()
    defined = Counter()
    
    #print("golden arbitrary, golden defined, extra arbitrary, extra defined")
    for line in open(f).readlines():
        line = line.strip()
        if line == '--- end generalized model ---':
            in_model = False
            #for key in sorted(set([*arbitrary.keys(), *defined.keys()])):
            #    print(key, '\t', "\t", arbitrary[key], "\t", defined[key])
            print(arbitrary['golden'], defined['golden'],arbitrary['extra'], defined['extra'])

        if in_model:
            if m := symbol_arbitrary.match(line):
                #print(line, "ARB", m.group(1))
                arbitrary['golden' if m.group(1) not in not_golden else 'extra'] += 1
            elif m := symbol_defined.match(line):
                #print(line, "DEF", m.group(1))
                defined['golden' if m.group(1) not in not_golden else 'extra'] += 1
            else:
                #print("???", line)
                pass
        if line == '--- Generalized model is ---':
            in_model = True
            arbitrary = Counter()
            defined = Counter()


import json
print("golden arbitrary, golden defined, extra arbitrary, extra defined")
for j in json.loads(open('blocked_symbols.json').read()):
    print(f'{j["base"]}-{j["conjecture"]}')
    parse(f'out/term-base/{j["base"]}-{j["conjecture"]}-0.out', j['extra'][0][len('--blocked-symbols='):])