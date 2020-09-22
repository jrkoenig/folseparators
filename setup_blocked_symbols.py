
from separators.separate import *
from separators.learn import *
from separators.parse import parse
from separators.interpret import interpret

def sig_symbols(s: Signature) -> List[str]:
    r: List[str] = []
    r.extend(s.relations.keys())
    r.extend(s.functions.keys())
    r.extend(s.constants.keys())
    return r

def main() -> None:
    modified = []
    for l in sorted(json.load(open("conjectures/benchmark.json")), key = lambda x: x['file']):
        if not l['file'].startswith("conjectures/mypyvy"): continue
        file = interpret(parse(open(l['file'], "r").read()))
        ss = sig_symbols(file.sig)
        syms = list(symbols(file.conjectures[0]))
        print(l['base'], l['conjecture'], len(set([x for x in syms if x in ss])), len(ss))
        arg = '--blocked-symbols=' + ','.join(set(ss) - set(syms))
        l['extra'] = [arg]
        if l['existentials'] == 0:
            l['extra'].append('--logic=universal')
        modified.append(l)
    with open('blocked_symbols.json', 'w') as f:
        json.dump(modified, f, indent=1)
main()