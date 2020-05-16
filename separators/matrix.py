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


import itertools, copy, sys
from array import array

import z3

from .logic import And, Or, Not, Func, Var, Relation, Equal, Formula, Term, Signature, Model
from .check import check, resolve_term
from .timer import Timer
from typing import List, Dict, Optional, Sequence, Iterable, Tuple, Generator

K_function_unrolling = 1


# models is a map from name (eg M134) to model. sat_formula is a formula that
# uses the variables Mi, and should be made true by the resulting formula.
# sat_formula must be satisfiable, but may potentially have many satisfying
# assignments that must be explored to find a good generalizable matrix formula.
def infer_matrix(models: Dict[int, Model], sig: Signature, sat_formula: z3.ExprRef, quiet: bool, timer: Timer, N_clauses: int = 10) -> Optional[Formula]:

    trivial = trivial_check(sat_formula, models.keys())
    if trivial is not None:
        return trivial

    if not quiet: print ("Computing atom-model matrix")
    model_positions = dict((model_id, i) for (i, model_id) in enumerate(models.keys()))
    atom_model_matrix = [(array('b', (check(a, m) for m in models.values())), a) for a in atoms(sig)]
    atom_model_matrix_reduced = [(row, atom) for (row, atom) in atom_model_matrix if not (all(row) or all(not x for x in row))]
    atom_model_matrix_reduced.sort()
    for i in range(len(atom_model_matrix_reduced)-1, 1, -1):
        (r1, _), (r2, _) = atom_model_matrix_reduced[i-1], atom_model_matrix_reduced[i]
        if r1 == r2:
            del atom_model_matrix_reduced[i]

    if not quiet: print ("Retained", len(atom_model_matrix_reduced), "of", len(atom_model_matrix), "atoms")
    if not quiet: print ("Have", len(models), "distinct FO-types/models")
    timer.check_time()
    # print("\n".join(["".join('1' if x else '0' for x in row) + " " + str(atom) for (row, atom) in atom_model_matrix_reduced]))
    # print (sat_formula)
    # print (models.keys())

    m = compute_minimal_with_z3_maxsat(atom_model_matrix_reduced, model_positions, sat_formula, quiet, timer, N_clauses)
    return trivial_simplify(m) if m is not None else m

def trivial_check(sat_formula: z3.ExprRef, vars: Iterable[int]) -> Optional[Formula]:
    s = z3.Solver()
    s.add(sat_formula)
    if s.check(*[z3.Bool('M'+str(x)) for x in vars]) == z3.sat:
        return And([])
    if s.check(*[z3.Not(z3.Bool('M'+str(x))) for x in vars]) == z3.sat:
        return Or([])
    return None

def compute_minimal_with_z3_maxsat(M: List[Tuple[array, Formula]], model_positions: Dict[int,int], sat_formula: z3.ExprRef, quiet: bool, timer: Timer, N_clauses: int) -> Optional[Formula]:
    solver = z3.Optimize()
    B = z3.Bool
    solver.add(sat_formula)
    p_terms = [[B("xp{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    n_terms = [[B("xn{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    if not quiet: print("Encoding model constraints")
    for x, m_index in model_positions.items():
        definition = []
        for i in range(N_clauses):
            clause = [(p_terms[i][j] if row[m_index] else n_terms[i][j]) for j, (row, _) in enumerate(M)]
            definition.append(z3.Or(*clause))
        solver.add(B("M"+str(x)) == z3.And(*definition))
        timer.check_time()
    # A clause may not have both positive and negative instances of an atom
    if not quiet: print("Adding disjunction exclusions")
    for i in range(N_clauses):
        for j in range(len(M)):
            solver.add(z3.Or(z3.Not(B("xp{}_{}".format(i,j))),
                             z3.Not(B("xn{}_{}".format(i,j)))))
        timer.check_time()
    
    for j in range(len(M)):
        # minimize number of atoms
        #solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format(p, i, j)) for i in range(N_clauses) for p in ["xp", "xn"]])))
        
        # minimize number of literals
        solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format('xp', i, j)) for i in range(N_clauses)])))
        solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format('xn', i, j)) for i in range(N_clauses)])))
    if not quiet: print("Constructed minimization problem")
    r = timer.solver_check(solver)
    if r == z3.sat:
        if not quiet: print("Found a formula")
        assignment = solver.model()
        f = []
        used = set()
        for i in range(N_clauses):
            cl = []
            for j, (row, atom) in enumerate(M):
                if assignment[B("xp{}_{}".format(i,j))]:
                    cl.append(atom)
                    used.add(j)
                elif assignment[B("xn{}_{}".format(i,j))]:
                    cl.append(Not(atom))
                    used.add(j)
            cl.sort()
            f.append(Or(cl))
        if not quiet: print("Used", len(used), "distinct atoms")
        f.sort()
        f_minimal: List[Formula] = []
        for clause2 in f:
            if len(f_minimal) > 0 and f_minimal[-1] == clause2:
                continue
            f_minimal.append(clause2)
        return And(f_minimal)
    else:
        print(f"Z3 could not solve max-SAT problem ({r})")
        return None

def atoms(sig: Signature) -> Iterable[Formula]:
    terms_by_sort: Dict[str, List[Term]] = dict([(s,[]) for s in sig.sorts])

    for c, sort in sig.constants.items():
        terms_by_sort[sort].append(Var(c))

    for _ in range(K_function_unrolling):
        prior_terms = copy.deepcopy(terms_by_sort)
        for f, (arg_sorts, result_sort) in sig.functions.items():
            arg_terms = itertools.product(*[prior_terms[s] for s in arg_sorts])
            terms_by_sort[result_sort].extend([Func(f, list(a)) for a in arg_terms])

    for r, sorts in sig.relations.items():
        for args in itertools.product(*[terms_by_sort[s] for s in sorts]):
            yield Relation(r, list(args))

    for sort in sig.sorts:
        for (a,b) in itertools.product(terms_by_sort[sort], terms_by_sort[sort]):
            yield (Equal(a, b))

def trivial_simplify(f: Formula) -> Formula:
    if isinstance(f, Not):
        sub_f = trivial_simplify(f.f)
        if isinstance(sub_f, Not):
            return sub_f.f
        return Not(sub_f)
    elif isinstance(f, And):
        if len(f.c) == 1:
            return trivial_simplify(f.c[0])
        else:
            return And([trivial_simplify(c) for c in f.c])
    elif isinstance(f, Or):
        if len(f.c) == 1:
            return trivial_simplify(f.c[0])
        else:
            return Or([trivial_simplify(c) for c in f.c])
    else:
        return f
