
import json, os, sys
from interpret import interpret
from parse import parse
from logic import *

def count_quantifiers(f):
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifiers(f.f)
    if isinstance(f, (And, Or)):
        return sum(count_quantifiers(x) for x in f.c)
    if isinstance(f, Not):
        return count_quantifiers(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0

def count_existentials(f):
    if isinstance(f, (Exists)):
        return 1 + count_existentials(f.f)
    if isinstance(f, (Forall)):
        return count_existentials(f.f)
    if isinstance(f, (And, Or)):
        return sum(count_existentials(x) for x in f.c)
    if isinstance(f, Not):
        return count_existentials(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0


def max_quantifier_depth(f):
    if isinstance(f, (Exists, Forall)):
        return 1 + max_quantifier_depth(f.f)
    if isinstance(f, (And, Or)):
        return max(max_quantifier_depth(x) for x in f.c)
    if isinstance(f, Not):
        return max_quantifier_depth(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0

def term_depth(t):
    if isinstance(t, Var):
        return 0
    elif isinstance(t, Func):
        return 1 + max(term_depth(a) for a in t.args)

def max_term_depth(f):
    if isinstance(f, (Exists, Forall)):
        return max_term_depth(f.f)
    if isinstance(f, (And, Or)):
        return max(max_term_depth(x) for x in f.c)
    if isinstance(f, Not):
        return max_term_depth(f.f)
    if isinstance(f, (Relation, Equal)):
        if len(f.args) > 0:
            return max(term_depth(a) for a in f.args)
        else:
            return 0


def main():
    o = open("out/extracted.json", "w")
    p = 'conjectures/extracted'
    files = [os.path.join(p, f) for f in os.listdir(p)]
    files.sort()
    descs = []
    for f in files:
        original_file = os.path.splitext(os.path.basename(f))[0]
        base = "-".join(original_file.split("-")[:-1])
        conj = original_file.split("-")[-1]
        (sig, axioms, conjectures, models) = interpret(parse(open(f).read()))
        assert len(conjectures) == 1
        descs.append({'base': base,
                      'conjecture': conj,
                      'file': f,
                      'quantifiers': count_quantifiers(conjectures[0]),
                      'max_quantifier_depth': max_quantifier_depth(conjectures[0]),
                      'existentials': count_existentials(conjectures[0]),
                      'max_term_depth': max_term_depth(conjectures[0]),
                      'golden_formula': str(conjectures[0])
                     })
    json.dump(descs, o, indent=1)
    o.close()

main()