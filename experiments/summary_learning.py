#!/usr/bin/python3.7

import argparse, random, json, os
from collections import Counter, defaultdict
from typing import *
import typing

def int_bins(x: List[int]) -> List[float]:
    l,h = min(x),max(x)
    return [x - 0.5 for x in range(l,h+2)]

def main() -> None:
    
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=argparse.FileType('r'))
    parser.add_argument("--benchmark", type=argparse.FileType('r'), default = "/root/folseparators/conjectures/benchmark.json")
    parser.add_argument("--output", "-o", type=str, default = "out/charts")
    args = parser.parse_args()

    descs = json.load(args.benchmark)
    desc_by_id = {}
    for d in descs:
        desc_by_id[(d['base'], d['conjecture'])] = d
    def desc_of(r: Dict) -> Dict:
        return desc_by_id[(r['base'], r['conjecture'])]
    
    results = json.load(args.results)
    results = [r for r in results if (r['base'], r['conjecture']) in desc_by_id]


    try:
        os.makedirs(args.output, exist_ok=True)
        os.chdir(args.output)
    except OSError as e:
        print(e)
        return

    summary_file = open("summary.txt", "w")
    def _print(*args: Any) -> None:
        print(*args, file=summary_file)

    _print(f"Total CPU hours {sum(r['stats']['total_time'] for r in results if 'stats' in r)/3600:.0f}\n")

    for r in results:
        if 'stats' not in r: continue
        if r['stats']['formula'] == 'false':
            print (r['base'], r['conjecture'])

    
    s: typing.Counter[str] = Counter()
    f: typing.Counter[str] = Counter()
    k: typing.Counter[str] = Counter()
    for r in results:
        if r['success']:
            s[r['base']] += 1
        elif r['killed']:
            k[r['base']] += 1
        else:
            f[r['base']] += 1

    missing_experiments = set((d['base'], d['conjecture']) for d in descs) - set((d['base'], d['conjecture']) for d in results)
    if len(missing_experiments) > 0:
        _print(f"Missing {len(missing_experiments)} results from benchmark")
    _print("Results count: ", len(results), "{}/{}/{} succ/kill/fail".format(sum(s.values()),sum(k.values()), sum(f.values())))
    _print(f"Success rate: {sum(s.values())/len(results)*100.0:0.1f}")

    by_base_example: DefaultDict[str, Tuple[int, int]] = defaultdict(lambda: (0,0))
    for r in results:
        (successful, total) = by_base_example[r['base']]
        by_base_example[r['base']] = (successful + (1 if r ['success'] else 0), total + 1)

    _print("\n")
    _print("Example\tsucc.\ttotal\n  * = all successful\n-----")
    for (b, (succ, tot)) in sorted(by_base_example.items()):
        _print(f"{'*' if succ == tot else ' '} {b}\t{succ}\t{tot}")

    
    s = Counter()
    f = Counter()
    k = Counter()
    for r in results:
        golden_quant_count = desc_by_id[r['base'], r['conjecture']]['quantifiers']
        if r['success']:
            s[golden_quant_count] += 1
        elif r['killed']:
            k[golden_quant_count] += 1
        else:
            f[golden_quant_count] += 1

    labels = list(sorted(set(s.keys()) | set(k.keys()) | set(f.keys())))

    _print("\nQuant. @ success @ killed @ failed")
    for l in labels:
        _print (l, "@", s[l],"@", k[l],"@", f[l])
    _print("\n")

    _print("\nBar-ish chart, by quantifier count:")
    for l in labels:
        _print (l, "x" * (f[l] + k[l]) + "." * s[l])
    _print("\n")

    c_to = 0
    s_to = 0
    for r in results:
        if 'stats' in r:
            if r['stats']['counterexample_time'] > r['timeout'] - 5:
                c_to += 1
            if r['stats']['separation_time'] > r['timeout'] - 5:
                s_to += 1
    _print(f"counterexample timeout: {c_to}, separation timeout: {s_to}")

    m_heavy = 0
    m_light = 0
    lower_limit = 200
    _print("\nFormula with hard to infer matrices:")
    for r in results:
        if 'stats' in r:
            if r['stats']['separation_time'] > lower_limit:
                if r['stats']['matrix_time'] > r['stats']['separation_time']*0.5:
                    m_heavy += 1
                    print(r['success'],"\t", desc_of(r)['golden_formula'])
                else:
                    m_light += 1
    _print(f"For examples taking > {lower_limit} sec")
    _print(f"matrix >50%: {m_heavy}, matrix <=50%: {m_light}")


    errors = []
    for r in results:
        if r['killed']:
            qc = desc_of(r)['quantifiers']
            gold = desc_of(r)['golden_formula']
            errors.append((qc, gold, r['base'] + "-" + r['conjecture']))
    errors.sort()
    _print("\nKilled Conjuncts:")
    for (q, gold, name) in errors:
        _print(name, q, gold)
            
    errors2 = []
    for r in results:
        if not r['killed'] and not r['success']:
            qc = desc_of(r)['quantifiers']
            gold = desc_of(r)['golden_formula']
            if 'stats' in r:
                x = min(1, r['stats']['counterexample_time']/float(r['timeout']))
            else:
                x = 0.0
            errors2.append((qc, gold, r['base'] + "-" + r['conjecture'], x, r))
    errors2.sort()
    _print("\nFailed Conjuncts(counter frac, matrix frac, quants, name, error):")
    # for (q, gold, name, x, r) in errors:
    #     print(f"{x:0.2f} {name}","@", q, "@", gold)
    for (q, gold, name, x, r) in errors2:
        if 'stats' in r:
            c_frac = min(1, r['stats']['counterexample_time']/float(r['timeout']))
            m_frac = min(1, r['stats']['matrix_time']/max(0.001, r['stats']['separation_time']))
            error = r['stats']['error']
        else:
            c_frac = 0.0
            m_frac = 0.0
            error = "?"
        _print(f"{c_frac:0.2f}\t{m_frac:0.2f}\t{q}\t{name}\t{error}")
            
    _print ("\n\nAll timings:")
    for (n, t) in sorted([(r['base'] + "-" + r['conjecture'], '-' if 'stats' not in r or not r['stats']['success'] else f"{r['stats']['total_time']:0.2f}") for r in results]):
        _print(n, "\t\t", t)

if __name__ == "__main__":
    main()
