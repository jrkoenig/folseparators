import argparse, random, json, os
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
    parser.add_argument("--output", "-o", default = "out/charts")
    args = parser.parse_args()

    sns.set(style="white", palette="muted", color_codes=True)
    descs = json.load(args.description)
    desc_by_id = {}
    for d in descs:
        desc_by_id[(d['base'], d['conjecture'])] = d
    def desc_of(r):
        return desc_by_id[(r['base'], r['conjecture'])]
    results = json.load(args.results)

    blacklist = ['tlb100', 'tlb101', 'tlb102', 'tlb103', 'tlb104', 'tlb105', 'tlb106', 'tlb107', 'tlb108', 'tlb109', 'tlb110', 'tlb111', 'tlb112', 'tlb113', 'tlb114', 'tlb115', 'tlb116', 'tlb117', 'tlb118', 'tlb119', 'tlb120', 'tlb121', 'tlb122', 'tlb123', 'tlb124', 'tlb125', 'tlb126', 'tlb127', 'tlb128', 'tlb129', 'tlb130', 'tlb131', 'tlb132', 'tlb133', 'tlb134', 'tlb135', 'tlb136', 'tlb137', 'tlb138', 'tlb139', 'tlb140', 'tlb141', 'tlb142', 'tlb143', 'tlb144', 'tlb145', 'tlb146', 'tlb147', 'tlb148', 'tlb149', 'tlb150', 'tlb151', 'tlb152', 'tlb153', 'tlb154', 'tlb155', 'tlb156', 'tlb157', 'tlb158', 'tlb159', 'tlb160', 'tlb161', 'tlb162', 'tlb163', 'tlb164', 'tlb165', 'tlb166', 'tlb167', 'tlb168', 'tlb169', 'tlb170', 'tlb171', 'tlb172', 'tlb173', 'tlb174', 'tlb175', 'tlb176', 'tlb177', 'tlb178', 'tlb179', 'tlb180', 'tlb181', 'tlb182', 'tlb183', 'tlb184', 'tlb185', 'tlb186', 'tlb187', 'tlb188', 'tlb189', 'tlb190', 'tlb191', 'tlb192', 'tlb193', 'tlb194', 'tlb195', 'tlb196', 'tlb197', 'tlb198', 'tlb199', 'tlb200', 'tlb201', 'tlb202', 'tlb203', 'tlb204', 'tlb205', 'tlb206', 'tlb207', 'tlb208', 'tlb209', 'tlb210', 'tlb211', 'tlb212', 'tlb213', 'tlb214', 'tlb215', 'tlb216', 'tlb217', 'tlb218', 'tlb219', 'tlb220', 'tlb221', 'tlb222', 'tlb223', 'tlb224', 'tlb225', 'tlb226', 'tlb227', 'tlb228', 'tlb229', 'tlb230', 'tlb231', 'tlb232', 'tlb233', 'tlb234', 'tlb235', 'tlb236', 'tlb237', 'tlb238', 'tlb239', 'tlb240', 'tlb241', 'tlb242', 'tlb243', 'tlb244', 'tlb245', 'tlb246', 'tlb247', 'tlb248', 'tlb249', 'tlb25', 'tlb250', 'tlb251', 'tlb252', 'tlb253', 'tlb254', 'tlb255', 'tlb256', 'tlb257', 'tlb258', 'tlb259', 'tlb26', 'tlb260', 'tlb261', 'tlb262', 'tlb263', 'tlb264', 'tlb265', 'tlb266', 'tlb267', 'tlb268', 'tlb269', 'tlb27', 'tlb270', 'tlb271', 'tlb272', 'tlb273', 'tlb274', 'tlb275', 'tlb276', 'tlb277', 'tlb278', 'tlb279', 'tlb28', 'tlb280', 'tlb281', 'tlb282', 'tlb283', 'tlb284', 'tlb285', 'tlb286', 'tlb287', 'tlb288', 'tlb289', 'tlb29', 'tlb290', 'tlb291', 'tlb292', 'tlb293', 'tlb294', 'tlb295', 'tlb296', 'tlb297', 'tlb298', 'tlb299', 'tlb30', 'tlb300', 'tlb31', 'tlb32', 'tlb33', 'tlb34', 'tlb35', 'tlb36', 'tlb37', 'tlb38', 'tlb39', 'tlb40', 'tlb41', 'tlb42', 'tlb43', 'tlb44', 'tlb45', 'tlb46', 'tlb47', 'tlb48', 'tlb49', 'tlb50', 'tlb51', 'tlb52', 'tlb53', 'tlb54', 'tlb55', 'tlb56', 'tlb57', 'tlb58', 'tlb59', 'tlb60', 'tlb61', 'tlb62', 'tlb63', 'tlb64', 'tlb65', 'tlb66', 'tlb67', 'tlb68', 'tlb69', 'tlb70', 'tlb71', 'tlb72', 'tlb73', 'tlb74', 'tlb75', 'tlb76', 'tlb77', 'tlb78', 'tlb79', 'tlb80', 'tlb81', 'tlb82', 'tlb83', 'tlb84', 'tlb85', 'tlb86', 'tlb87', 'tlb88', 'tlb89', 'tlb90', 'tlb91', 'tlb92', 'tlb93', 'tlb94', 'tlb95', 'tlb96', 'tlb97', 'tlb98', 'tlb99']
    original_len = len(results)
    print("Original problem count", len(descs))
    print("Total results", original_len)
    results = [r for r in results if not (r['base'] == 'tlb_pcrel' and r['conjecture'] in blacklist)]
    print("Blacklisted", original_len-len(results))
    print("Remaining problems", len(results))
    print("")

    # print("Random Formula:")
    # sample = random.sample(results, 5)
    # for r in sample:
    #     print(desc_by_id[(r['base'], r['conjecture'])]['golden_formula'])
    # print("")

    # print("There are {} protocols".format(len(set([r['base'] for r in results]))))


    try:
        os.makedirs(args.output, exist_ok=True)
        os.chdir(args.output)
    except OSError as e:
        print(e)
        return
    # SUFFIX = args.suffix
    # if SUFFIX != "" and not SUFFIX.startswith("-"):
    #     SUFFIX = "-" + SUFFIX

    #intdistplot([d['quantifiers'] for d in descs], axlabel="quantifier count", kde=False).get_figure().savefig("quantifier_distribution.png")
    
    # fig = plt.figure(figsize=(8,6))
    # ax = sns.countplot(data = pd.DataFrame([d['base'].replace("_", " ").replace("-", " ") for d in descs]), color="c", y = 0, orient='h')
    # ax.set_ylabel("protocol")
    # ax.set_xlabel("number of conjuncts")
    # plt.subplots_adjust(left=0.5)
    # fig.suptitle("Distribution of conjucts over protocols")
    # plt.savefig("conjunct_distribution.png")


    
    s = Counter()
    f = Counter()
    k = Counter()
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



    print ("Results count: ", len(results), "{}/{}/{} succ/kill/fail".format(sum(s.values()),sum(k.values()), sum(f.values())))
   
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
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['bottom'].set_visible(False)
    ax.spines['left'].set_visible(False)
    #fig.suptitle("Quantifier conjunct distribution with success rate")
    plt.savefig("success_by_quantifier_count.eps", bbox_inches='tight')
    plt.savefig("success_by_quantifier_count.png", bbox_inches='tight')

    print("\nQuant. @ success @ killed @ failed")
    for l in labels:
        print (l, "@", s[l],"@", k[l],"@", f[l])
    print("\n")

    fig = plt.figure(figsize=(6,4))
    times = []
    for r in results:
        if r['success']:
            times.append(r['stats']['total_time']/60.0)
        else:
            times.append(float('Inf'))
    times.sort()
    ax = plt.axes()
    plt.plot([x+0.5 for x in range(len(times))], times, color='black')
    plt.yscale("log")
    plt.xlim(0,len(times))
    plt.ylim(0.01,60)
    plt.ylabel("Time to learn (minutes)")
    plt.xlabel("Conjecture (ordinal)")
    #fig.suptitle("Ordinal chart of time to learn conjuncts")
    plt.savefig("ordinal_learning_times.eps", bbox_inches='tight')
    plt.savefig("ordinal_learning_times.png", bbox_inches='tight')

    fig = plt.figure(figsize=(6,4))
    xs = []
    ys = []
    for r in results:
        if 'stats' in r:
            xs.append(max(0.001, r['stats']['counterexample_time']/60.0))
            ys.append(max(0.001, r['stats']['separation_time']/60.0))
    times.sort()
    ax = plt.axes()
    #ax.set_aspect('equal', 'datalim')
    plt.scatter(xs, ys, color='black')
    plt.yscale("log")
    plt.ylim(0.001,10)
    plt.xscale("log")
    plt.xlim(0.001,10)
    plt.ylabel("Separation")
    plt.xlabel("Counterexample")
    #fig.suptitle("Ordinal chart of time to learn conjuncts")
    plt.savefig("time_scatter.eps", bbox_inches='tight')
    plt.savefig("time_scatter.png", bbox_inches='tight')

    c_to = 0
    s_to = 0
    for r in results:
        if 'stats' in r:
            if r['stats']['counterexample_time'] > r['timeout'] - 5:
                c_to += 1
            if r['stats']['separation_time'] > r['timeout'] - 5:
                s_to += 1
    print(f"counterexample timeout: {c_to}, separation timeout: {s_to}")



    fig = plt.figure(figsize=(6,4))
    xs = []
    ys = []
    for r in results:
        if 'stats' in r:
            xs.append(r['stats']['separation_time'])
            ys.append(r['stats']['matrix_time']/max(0.0001,r['stats']['separation_time']))
    times.sort()
    ax = plt.axes()
    #ax.set_aspect('equal', 'datalim')
    plt.scatter(xs, ys, color='black')
    plt.ylim(0,1)
    #plt.xscale("log")
    plt.ylabel("Matrix Fraction")
    plt.xlabel("Separation Time")
    #fig.suptitle("Ordinal chart of time to learn conjuncts")
    plt.savefig("matrix_percentage.eps", bbox_inches='tight')
    plt.savefig("matrix_percentage.png", bbox_inches='tight')

    m_heavy = 0
    m_light = 0
    lower_limit = 200
    print("\nFormula with hard to infer matrices:")
    for r in results:
        if 'stats' in r:
            if r['stats']['separation_time'] > lower_limit:
                if r['stats']['matrix_time'] > r['stats']['separation_time']*0.5:
                    m_heavy += 1
                    print(r['success'],"\t", desc_of(r)['golden_formula'])
                else:
                    m_light += 1
    print(f"For examples taking > {lower_limit} sec")
    print(f"matrix >50%: {m_heavy}, matrix <=50%: {m_light}")


    errors = []
    for r in results:
        if r['killed'] and d['max_term_depth'] <= 1:
            qc = desc_of(r)['quantifiers']
            gold = desc_of(r)['golden_formula']
            errors.append((qc, gold, r['base'] + "-" + r['conjecture']))
    errors.sort()
    print("\nKilled Conjuncts:")
    for (q, gold, name) in errors:
        print(name, q, gold)
            
    errors = []
    for r in results:
        if not r['killed'] and not r['success']:
            qc = desc_of(r)['quantifiers']
            gold = desc_of(r)['golden_formula']
            if 'stats' in r:
                x = min(1, r['stats']['counterexample_time']/float(r['timeout']))
            else:
                x = 0.0
            errors.append((qc, gold, r['base'] + "-" + r['conjecture'], x, r))
    errors.sort()
    print("\nFailed Conjuncts(counter frac, matrix frac, quants, name, error):")
    # for (q, gold, name, x, r) in errors:
    #     print(f"{x:0.2f} {name}","@", q, "@", gold)
    for (q, gold, name, x, r) in errors:
        if 'stats' in r:
            c_frac = min(1, r['stats']['counterexample_time']/float(r['timeout']))
            m_frac = min(1, r['stats']['matrix_time']/max(0.001, r['stats']['separation_time']))
            error = r['stats']['error']
        else:
            c_frac = 0.0
            m_frac = 0.0
            error = "?"
        print(f"{c_frac:0.2f}\t{m_frac:0.2f}\t{q}\t{name}\t{error}\t{r['stats']['formula_quantifiers']}")
            

    print("\nFailed Conjuncts(counter frac, matrix frac, quants, name, error):")
    # for (q, gold, name, x, r) in errors:
    #     print(f"{x:0.2f} {name}","@", q, "@", gold)
    cc = Counter()
    for (q, gold, name, x, r) in errors:
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
            print(f"{c_frac:0.2f}\t{m_frac:0.2f}\t{q}\t{name}\t{error}")
    for k,v in cc.items():
        (counter, matrix) = k
        print(f"{('c < 0.99' if counter else 'c >= 0.99')}, {('m < 0.95' if matrix else 'm >= 0.95')}: {v}")  


if __name__ == "__main__":
    main()
