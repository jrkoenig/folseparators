# Copyright 2020 Stanford University

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import argparse, random, json, os
import numpy as np
import pandas as pd
import matplotlib
matplotlib.use("Agg")

import matplotlib.pyplot as plt


import seaborn as sns
from collections import Counter
from typing import *
import typing

def int_bins(x: List[int]) -> List[float]:
    l,h = min(x),max(x)
    return [x - 0.5 for x in range(l,h+2)]
def intdistplot(x: Any, **kwargs: Any) -> Any:
    return sns.distplot(x, bins = int_bins(x), **kwargs)


def main() -> None:
    
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=argparse.FileType('r'))
    parser.add_argument("--description", type=argparse.FileType('r'), default = "conjectures/benchmark.json")
    parser.add_argument("--output", "-o", type=str, default = "out/charts")
    args = parser.parse_args()


    try:
        os.makedirs(args.output, exist_ok=True)
        os.chdir(args.output)
    except OSError as e:
        print(e)
        return

    sns.set(style="white", palette="muted", color_codes=True)
    font = {'size':16, 'family':'serif', 'serif': ['CMU Serif']}
    plt.rc('font', **font)
    plt.rc('mathtext', fontset='cm')
    plt.rc('axes', labelsize='medium')
    plt.rc('xtick', labelsize='medium')
    plt.rc('ytick', labelsize='medium')
    plt.rc('legend', fontsize='medium')

    descs = json.load(args.description)
    desc_by_id = {}
    for d in descs:
        desc_by_id[(d['base'], d['conjecture'])] = d
    def desc_of(r: Dict) -> Dict:
        return desc_by_id[(r['base'], r['conjecture'])]
    results = json.load(args.results)
    results = [r for r in results if r['base'] != 'tlb-safety']

    summary_file = open("summary.txt", "w")
    def _print(*args: Any) -> None:
        print(*args, file=summary_file)

    # print("Random Formula:")
    # sample = random.sample(results, 5)
    # for r in sample:
    #     print(desc_by_id[(r['base'], r['conjecture'])]['golden_formula'])
    # print("")

    # print("There are {} protocols".format(len(set([r['base'] for r in results]))))



    #intdistplot([d['quantifiers'] for d in descs], axlabel="quantifier count", kde=False).get_figure().savefig("quantifier_distribution.png")
    
    # fig = plt.figure(figsize=(8,6))
    # ax = sns.countplot(data = pd.DataFrame([d['base'].replace("_", " ").replace("-", " ") for d in descs]), color="c", y = 0, orient='h')
    # ax.set_ylabel("protocol")
    # ax.set_xlabel("number of conjuncts")
    # plt.subplots_adjust(left=0.5)
    # fig.suptitle("Distribution of conjucts over protocols")
    # plt.savefig("conjunct_distribution.png")
    _print(f"Total CPU hours {sum(r['stats']['total_time'] for r in results)/3600:.0f}\n")

    for r in results:
        if r['killed']: continue
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


    # fig = plt.figure(figsize=(8,6))
    # plt.subplots_adjust(left=0.5)
    # ax = plt.axes()
    # labels = list(sorted(set(s.keys()) | set(f.keys()) | set(k.keys())))
    # labels.reverse()
    # plt.barh(range(len(labels)), list(1 for l in labels), color='#319b7c', linewidth=0)
    # plt.barh(range(len(labels)), list(((k[l]+f[l])/float(s[l]+f[l]+k[l]) for l in labels)), color='#fdce4b', linewidth=0)
    # plt.barh(range(len(labels)), list((k[l]/float(s[l]+f[l]+k[l]) for l in labels)), color='#e44033', linewidth=0)
    # plt.yticks(range(len(labels)), labels)
    # plt.xlim(0,1)
    # ax.spines['top'].set_visible(False)
    # ax.spines['right'].set_visible(False)
    # ax.spines['bottom'].set_visible(False)
    # ax.spines['left'].set_visible(False)
    # fig.suptitle("Success rate by protocol (normalized)")
    # plt.savefig("success_by_protocol.png")

    missing_experiments = set((d['base'], d['conjecture']) for d in descs) - set((d['base'], d['conjecture']) for d in results)
    if len(missing_experiments) > 0:
        _print(f"Missing {len(missing_experiments)} results from benchmark")
    _print("Results count: ", len(results), "{}/{}/{} succ/kill/fail".format(sum(s.values()),sum(k.values()), sum(f.values())))
    _print(f"Success rate: {sum(s.values())/len(results)*100.0:0.1f}" )
   
    # print ("\nProb Succ Killed Failed")
    # for l in labels:
    #     print(l, s[l], k[l], f[l])
    # print("")

    fig = plt.figure(figsize=(6,4))
    
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

    ax = plt.axes()
    labels = list(sorted(set(s.keys()) | set(k.keys()) | set(f.keys())))
    plt.bar(range(len(labels)), list(k[l]+f[l]+s[l] for l in labels), edgecolor='0', color='#FFFFFF', linewidth=0.5, clip_on=False)
    plt.bar(range(len(labels)), list(k[l]+f[l] for l in labels), color='#444444',edgecolor='#444444', linewidth=0.5)
    #plt.bar(range(len(labels)), list(k[l] for l in labels), color='#e44033', linewidth=0)
    plt.xticks(range(len(labels)), labels)
    plt.ylim(0,None)
    
    plt.xlabel("Number of quantifiers in golden formula")
    ax.tick_params(axis='y', left=True, width=0.5)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['bottom'].set_visible(False)
    ax.spines['left'].set_visible(False)
    ax.legend(['Success', 'Failure'], frameon=False)
    #fig.suptitle("Quantifier conjunct distribution with success rate")
    plt.savefig("success_by_quantifier_count.eps", bbox_inches='tight')
    plt.savefig("success_by_quantifier_count.png", bbox_inches='tight')

    _print("\nQuant. @ success @ killed @ failed")
    for l in labels:
        _print (l, "@", s[l],"@", k[l],"@", f[l])
    _print("\n")

    fig = plt.figure(figsize=(6,4))
    times = []
    for r in results:
        if r['success']:
            times.append(r['stats']['total_time'])
        else:
            times.append(float('Inf'))
    times.sort()
    ax = plt.axes()
    plt.plot([x+0.5 for x in range(len(times))], times, color='black')
    plt.yscale("log")
    plt.xlim(0,len(times))
    plt.ylim(1,3600)
    plt.ylabel("Time to learn (sec)")
    plt.xlabel("Conjecture (ordinal)")
    #fig.suptitle("Ordinal chart of time to learn conjuncts")
    plt.savefig("ordinal_learning_times.eps", bbox_inches='tight')
    plt.savefig("ordinal_learning_times.png", bbox_inches='tight')

    # fig = plt.figure(figsize=(6,4))
    # xs = []
    # ys = []
    # for r in results:
    #     if 'stats' in r:
    #         xs.append(max(0.001, r['stats']['counterexample_time']/60.0))
    #         ys.append(max(0.001, r['stats']['separation_time']/60.0))
    # times.sort()
    # ax = plt.axes()
    # #ax.set_aspect('equal', 'datalim')
    # plt.scatter(xs, ys, color='black')
    # plt.yscale("log")
    # plt.ylim(0.001,10)
    # plt.xscale("log")
    # plt.xlim(0.001,10)
    # plt.ylabel("Separation")
    # plt.xlabel("Counterexample")
    # #fig.suptitle("Ordinal chart of time to learn conjuncts")
    # plt.savefig("time_scatter.eps", bbox_inches='tight')
    # plt.savefig("time_scatter.png", bbox_inches='tight')

    c_to = 0
    s_to = 0
    for r in results:
        if 'stats' in r:
            if r['stats']['counterexample_time'] > r['timeout'] - 5:
                c_to += 1
            if r['stats']['separation_time'] > r['timeout'] - 5:
                s_to += 1
    _print(f"counterexample timeout: {c_to}, separation timeout: {s_to}")



    # fig = plt.figure(figsize=(6,4))
    # xs = []
    # ys = []
    # for r in results:
    #     if 'stats' in r:
    #         xs.append(r['stats']['separation_time'])
    #         ys.append(r['stats']['matrix_time']/max(0.0001,r['stats']['separation_time']))
    # times.sort()
    # ax = plt.axes()
    # #ax.set_aspect('equal', 'datalim')
    # plt.scatter(xs, ys, color='black')
    # plt.ylim(0,1)
    # #plt.xscale("log")
    # plt.ylabel("Matrix Fraction")
    # plt.xlabel("Separation Time")
    # #fig.suptitle("Ordinal chart of time to learn conjuncts")
    # plt.savefig("matrix_percentage.eps", bbox_inches='tight')
    # plt.savefig("matrix_percentage.png", bbox_inches='tight')

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
        if r['killed'] and d['max_term_depth'] <= 1:
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
        _print(f"{c_frac:0.2f}\t{m_frac:0.2f}\t{q}\t{name}\t{error}\t{r['stats']['formula_quantifiers']}")
            

    _print("\nFailed Conjuncts(counter frac, matrix frac, quants, name, error):")
    # for (q, gold, name, x, r) in errors:
    #     print(f"{x:0.2f} {name}","@", q, "@", gold)
    cc: typing.Counter[Tuple[bool, bool]] = Counter()
    for (q, gold, name, x, r) in errors2:
        if 'stats' in r:
            c_frac = min(1, r['stats']['counterexample_time']/float(r['timeout']))
            m_frac = min(1, r['stats']['matrix_time']/max(0.001, r['stats']['separation_time']))
            error = r['stats']['error']
        else:
            c_frac = 0.0
            m_frac = 0.0
            error = "?"
        reason_c = c_frac >= 0.99 or error.startswith("Z3")
        reason_m = not reason_c and  m_frac >= 0.95
        cc[(not reason_c, not reason_m)] += 1
        if not reason_c and not reason_m:
            _print(f"{c_frac:0.2f}\t{m_frac:0.2f}\t{q}\t{name}\t{error}")
    for kk,v in cc.items():
        (counter, matrix) = kk
        _print(f"{('c < 0.99' if counter else 'c >= 0.99')}, {('m < 0.95' if matrix else 'm >= 0.95')}: {v}")  


if __name__ == "__main__":
    main()
