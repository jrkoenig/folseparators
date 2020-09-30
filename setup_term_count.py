
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

def nop(file, l):
    return
def sig_and_count_limit(file, l):
    ss = sig_symbols(file.sig)
    syms = list(symbols(file.conjectures[0]))
    arg = '--blocked-symbols=' + ','.join(sorted(set(ss) - set(syms)))
    arg2 = f'--expt-flags=termlimit{ l["relation_counts"][0] }'
    l['extra'] = [arg, arg2]
    if l['existentials'] == 0:
        l['extra'].append('--logic=universal')
def term_count_limit(file, l):
    arg = f'--expt-flags=termlimit{ l["relation_counts"][0] }'
    l['extra'] = [arg]
    return
            
def main() -> None:
    for extra_operation, label in [(nop, "baseline"), (term_count_limit, "term_limit"), (sig_and_count_limit, "sig_and_count_limit")]:
        modified = []
        for l in sorted(json.load(open("out/mypyvy.json")), key = lambda x: x['file']):
            # if not l['file'].startswith("conjectures/mypyvy"): continue
            file = interpret(parse(open(l['file'], "r").read()))
            extra_operation(file, l)
            modified.append(l)
        with open(f'{label}.json', 'w') as f:
            json.dump(modified, f, indent=1)
main()