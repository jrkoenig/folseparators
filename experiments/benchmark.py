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
sys.path.append(".")
from separators.interpret import interpret, SemanticError
from separators.parse import parse, SyntaxError
from separators.logic import Formula, Exists, Forall, And, Or, Not, Relation, Equal, Term, Func, Var

def count_quantifiers(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifiers(f.f)
    if isinstance(f, (And, Or)):
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
    if isinstance(f, (And, Or)):
        return sum(count_existentials(x) for x in f.c)
    if isinstance(f, Not):
        return count_existentials(f.f)
    if isinstance(f, (Relation, Equal)):
        return 0
    assert False


def max_quantifier_depth(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + max_quantifier_depth(f.f)
    if isinstance(f, (And, Or)):
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
    if isinstance(f, (And, Or)):
        return max(max_term_depth(x) for x in f.c)
    if isinstance(f, Not):
        return max_term_depth(f.f)
    if isinstance(f, (Relation, Equal)):
        if len(f.args) > 0:
            return max(term_depth(a) for a in f.args)
        else:
            return 0
    assert False

ivy_whitelist = ['alternating_bit_protocol', 'byz_paxos', 'fast_paxos', 'fast_paxos_epr', 'flexible_paxos_epr', 
                 'multi_paxos_epr', 'stoppable_paxos_epr', 'vertical_paxos_epr_unverified_optimization']

tlb_pcrel_blacklist = ['tlb100', 'tlb101', 'tlb102', 'tlb103', 'tlb104', 'tlb105', 'tlb106', 'tlb107', 'tlb108',
                       'tlb109', 'tlb110', 'tlb111', 'tlb112', 'tlb113', 'tlb114', 'tlb115', 'tlb116', 'tlb117',
                       'tlb118', 'tlb119', 'tlb120', 'tlb121', 'tlb122', 'tlb123', 'tlb124', 'tlb125', 'tlb126',
                       'tlb127', 'tlb128', 'tlb129', 'tlb130', 'tlb131', 'tlb132', 'tlb133', 'tlb134', 'tlb135',
                       'tlb136', 'tlb137', 'tlb138', 'tlb139', 'tlb140', 'tlb141', 'tlb142', 'tlb143', 'tlb144',
                       'tlb145', 'tlb146', 'tlb147', 'tlb148', 'tlb149', 'tlb150', 'tlb151', 'tlb152', 'tlb153',
                       'tlb154', 'tlb155', 'tlb156', 'tlb157', 'tlb158', 'tlb159', 'tlb160', 'tlb161', 'tlb162',
                       'tlb163', 'tlb164', 'tlb165', 'tlb166', 'tlb167', 'tlb168', 'tlb169', 'tlb170', 'tlb171',
                       'tlb172', 'tlb173', 'tlb174', 'tlb175', 'tlb176', 'tlb177', 'tlb178', 'tlb179', 'tlb180',
                       'tlb181', 'tlb182', 'tlb183', 'tlb184', 'tlb185', 'tlb186', 'tlb187', 'tlb188', 'tlb189',
                       'tlb190', 'tlb191', 'tlb192', 'tlb193', 'tlb194', 'tlb195', 'tlb196', 'tlb197', 'tlb198',
                       'tlb199', 'tlb200', 'tlb201', 'tlb202', 'tlb203', 'tlb204', 'tlb205', 'tlb206', 'tlb207',
                       'tlb208', 'tlb209', 'tlb210', 'tlb211', 'tlb212', 'tlb213', 'tlb214', 'tlb215', 'tlb216',
                       'tlb217', 'tlb218', 'tlb219', 'tlb220', 'tlb221', 'tlb222', 'tlb223', 'tlb224', 'tlb225',
                       'tlb226', 'tlb227', 'tlb228', 'tlb229', 'tlb230', 'tlb231', 'tlb232', 'tlb233', 'tlb234',
                       'tlb235', 'tlb236', 'tlb237', 'tlb238', 'tlb239', 'tlb240', 'tlb241', 'tlb242', 'tlb243',
                       'tlb244', 'tlb245', 'tlb246', 'tlb247', 'tlb248', 'tlb249', 'tlb25', 'tlb250', 'tlb251',
                       'tlb252', 'tlb253', 'tlb254', 'tlb255', 'tlb256', 'tlb257', 'tlb258', 'tlb259', 'tlb26',
                       'tlb260', 'tlb261', 'tlb262', 'tlb263', 'tlb264', 'tlb265', 'tlb266', 'tlb267', 'tlb268',
                       'tlb269', 'tlb27', 'tlb270', 'tlb271', 'tlb272', 'tlb273', 'tlb274', 'tlb275', 'tlb276',
                       'tlb277', 'tlb278', 'tlb279', 'tlb28', 'tlb280', 'tlb281', 'tlb282', 'tlb283', 'tlb284',
                       'tlb285', 'tlb286', 'tlb287', 'tlb288', 'tlb289', 'tlb29', 'tlb290', 'tlb291', 'tlb292',
                       'tlb293', 'tlb294', 'tlb295', 'tlb296', 'tlb297', 'tlb298', 'tlb299', 'tlb30', 'tlb300',
                       'tlb31', 'tlb32', 'tlb33', 'tlb34', 'tlb35', 'tlb36', 'tlb37', 'tlb38', 'tlb39', 'tlb40',
                       'tlb41', 'tlb42', 'tlb43', 'tlb44', 'tlb45', 'tlb46', 'tlb47', 'tlb48', 'tlb49', 'tlb50',
                       'tlb51', 'tlb52', 'tlb53', 'tlb54', 'tlb55', 'tlb56', 'tlb57', 'tlb58', 'tlb59', 'tlb60',
                       'tlb61', 'tlb62', 'tlb63', 'tlb64', 'tlb65', 'tlb66', 'tlb67', 'tlb68', 'tlb69', 'tlb70',
                       'tlb71', 'tlb72', 'tlb73', 'tlb74', 'tlb75', 'tlb76', 'tlb77', 'tlb78', 'tlb79', 'tlb80',
                       'tlb81', 'tlb82', 'tlb83', 'tlb84', 'tlb85', 'tlb86', 'tlb87', 'tlb88', 'tlb89', 'tlb90',
                       'tlb91', 'tlb92', 'tlb93', 'tlb94', 'tlb95', 'tlb96', 'tlb97', 'tlb98', 'tlb99']
    
def whitelist(base: str, conj: str, is_mypyvy: bool) -> bool:
    if is_mypyvy:
        return True
    elif base in ivy_whitelist:
        return True
    elif base == 'tlb_pcrel':
        if conj not in tlb_pcrel_blacklist:
            return True
    return False

def main() -> None:
    o = open("conjectures/benchmark.json", "w")
    p = 'conjectures/extracted'
    files = [os.path.join(p, f) for f in os.listdir(p)]
    p = 'conjectures/mypyvy'
    files.extend([os.path.join(p, f) for f in os.listdir(p)])
    files.sort()
    descs = []
    for f in files:
        original_file = os.path.splitext(os.path.basename(f))[0]
        base = "-".join(original_file.split("-")[:-1])
        conj = original_file.split("-")[-1]
        if whitelist(base, conj, f.startswith('conjectures/mypyvy')):
            print(f)
            try:
                parsed = interpret(parse(open(f).read()))
                conjectures = parsed.conjectures
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
            except (SyntaxError, SemanticError) as e:
                print("File ", f, "was not valid", str(e))
    json.dump(descs, o, indent=1)
    o.close()

main()