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

import json, os, sys
from typing import List
import typing
sys.path.append(".")
from separators.interpret import interpret, SemanticError
from separators.parse import parse, SyntaxError
from separators.logic import Formula, Exists, Forall, And, Or, Not, Relation, Equal, Iff, Signature, Term, Func, Var, symbols
from collections import Counter

def count_quantifiers(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifiers(f.f)
    if isinstance(f, (And, Or, Iff)):
        return sum(count_quantifiers(x) for x in f.c)
    if isinstance(f, Not):
        return count_quantifiers(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0
    assert False

def count_existentials(f: Formula) -> int:
    if isinstance(f, (Exists)):
        return 1 + count_existentials(f.f)
    if isinstance(f, (Forall)):
        return count_existentials(f.f)
    if isinstance(f, (And, Or, Iff)):
        return sum(count_existentials(x) for x in f.c)
    if isinstance(f, Not):
        return count_existentials(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0
    assert False


def max_quantifier_depth(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + max_quantifier_depth(f.f)
    if isinstance(f, (And, Or, Iff)):
        return max(max_quantifier_depth(x) for x in f.c)
    if isinstance(f, Not):
        return max_quantifier_depth(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0
    assert False

def term_depth(t: Term) -> int:
    if isinstance(t, Var):
        return 0
    elif isinstance(t, Func):
        return 1 + max(term_depth(a) for a in t.args)
    assert False

def max_term_depth(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return max_term_depth(f.f)
    if isinstance(f, (And, Or, Iff)):
        return max(max_term_depth(x) for x in f.c)
    if isinstance(f, Not):
        return max_term_depth(f.f)
    if isinstance(f, (Relation, Equal)):
        if len(f.args) > 0:
            return max(term_depth(a) for a in f.args)
        else:
            return 0
    assert False

def count_relations(f: Formula, sig: Signature) -> List[int]:
    counts: typing.Counter[str] = Counter()
    for x in symbols(f):
        if x in sig.relations:
            counts[x] += 1
    c = list(sorted(counts.values(), reverse=True))
    return c

def main() -> None:
    o = open("out/mypyvy.json", "w")
    p = 'conjectures/mypyvy'
    files = [os.path.join(p, f) for f in os.listdir(p)]
    files.sort()
    descs = []
    for f in files:
        original_file = os.path.splitext(os.path.basename(f))[0]
        base = "-".join(original_file.split("-")[:-1])
        conj = original_file.split("-")[-1]
        #print(f)
        try:
            contents = open(f).read()
            fol = interpret(parse(contents))
            formula = fol.conjectures[0]
            is_safety = '\n; Original: safety ' in contents
            descs.append({'base': base,
                        'conjecture': conj,
                        'file': f,
                        'quantifiers': count_quantifiers(formula),
                        'max_quantifier_depth': max_quantifier_depth(formula),
                        'existentials': count_existentials(formula),
                        'max_term_depth': max_term_depth(formula),
                        'golden_formula': str(formula),
                        'relation_counts': count_relations(formula, fol.sig)
                        })
            print(f"{'SAFE' if is_safety else 'INV '}\t{base}-{conj}\t\"{','.join(map(str, count_relations(formula, fol.sig)))}\"\t{str(formula)}")
        except (SyntaxError, SemanticError) as e:
            print("File ", f, "was not valid", str(e))
    json.dump(descs, o, indent=1)
    o.close()

main()