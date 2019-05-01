import argparse
import json
import numpy as np
import pandas as pd
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import seaborn as sns
from collections import Counter

def int_bins(x):
    l,h = min(x),max(x)
    return [x - 0.5 for x in range(l,h+2)]
def intdistplot(x, **kwargs):
    return sns.distplot(x, bins = int_bins(x), **kwargs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=argparse.FileType('r'))
    parser.add_argument("--description", type=argparse.FileType('r'), default = "out/extracted.json")
    parser.add_argument("--suffix", default = "")
    args = parser.parse_args()

    sns.set(style="white", palette="muted", color_codes=True)
    descs = json.load(args.description)
    desc_by_id = {}
    for d in descs:
        desc_by_id[(d['base'], d['conjecture'])] = d

    results = json.load(args.results)

    SUFFIX = args.suffix
    if SUFFIX != "" and not SUFFIX.startswith("-"):
        SUFFIX = "-" + SUFFIX

    #intdistplot([d['quantifiers'] for d in descs], axlabel="quantifier count", kde=False).get_figure().savefig("out/quantifier_distribution.png")
    
    fig = plt.figure(figsize=(8,6))
    ax = sns.countplot(data = pd.DataFrame([d['base'].replace("_", " ").replace("-", " ") for d in descs]), color="c", y = 0, orient='h')
    ax.set_ylabel("protocol")
    ax.set_xlabel("number of conjuncts")
    plt.subplots_adjust(left=0.5)
    fig.suptitle("Distribution of conjucts over protocols")
    plt.savefig("out/conjunct_distribution"+SUFFIX+".png")



    fig = plt.figure(figsize=(8,6))
    plt.subplots_adjust(left=0.5)
    
    s = Counter()
    f = Counter()
    for r in results:
        if r['success']:
            s[r['base']] += 1
        else:
            f[r['base']] += 1

    ax = plt.axes()
    labels = list(sorted(set(s.keys()) | set(f.keys())))
    labels.reverse()
    plt.barh(range(len(labels)), list(1 for l in labels))
    plt.barh(range(len(labels)), list(f[l]/float(s[l]+f[l]) for l in labels))
    plt.yticks(range(len(labels)), labels)
    plt.xlim(0,1)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['bottom'].set_visible(False)
    ax.spines['left'].set_visible(False)
    fig.suptitle("Success rate by protocol (normalized)")
    plt.savefig("out/success_by_protocol"+SUFFIX+".png")



    print (len(results))
    for l in labels:
        print(l, s[l], f[l])

    fig = plt.figure(figsize=(8,6))
    
    s = Counter()
    f = Counter()
    for r in results:
        golden_quant_count = desc_by_id[r['base'], r['conjecture']]['quantifiers']
        if r['success']:
            s[golden_quant_count] += 1
        else:
            f[golden_quant_count] += 1
            if golden_quant_count == 0:
                print(r['base'], r['conjecture'])

    ax = plt.axes()
    labels = list(sorted(set(s.keys()) | set(f.keys())))
    plt.bar(range(len(labels)), list(s[l]+f[l] for l in labels))
    plt.bar(range(len(labels)), list(f[l] for l in labels))
    plt.xticks(range(len(labels)), labels)
    plt.ylim(0,None)
    plt.xlabel("Number of quantifiers in golden formula")
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['bottom'].set_visible(False)
    ax.spines['left'].set_visible(False)
    fig.suptitle("Quantifier conjunct distribution with success rate")
    plt.savefig("out/success_by_quantifier_count"+SUFFIX+".png")



    fig = plt.figure()
    times = []
    for r in results:
        if r['success']:
            times.append(r['stats']['total_time']/60.0)
        else:
            times.append(float('Inf'))
    times.sort()
    ax = plt.axes()
    plt.plot([x+0.5 for x in range(len(times))], times)
    plt.yscale("log")
    plt.xlim(0,len(times))
    plt.ylim(0.01,10)
    plt.ylabel("Time to learn (minutes)")
    plt.xlabel("Conjecture (ordinal)")
    fig.suptitle("Ordinal chart of time to learn conjuncts")
    plt.savefig("out/ordinal_learning_times"+SUFFIX+".png")

if __name__ == "__main__":
    main()