
import itertools, copy, sys
import z3
from array import array

from models import *
from check import check, resolve_term

K_function_unrolling = 1

def compute_dnf(M, tr, fl):
    def reduce(clause):
        changed = True
        while changed:
            i = 0
            changed = False
            while i < len(clause):
                for m_index in fl:
                    if all(M[a][0][m_index] == value for (a, value) in clause[:i]) and \
                       all(M[a][0][m_index] == value for (a, value) in clause[i+1:]):
                        i += 1
                        break
                else:
                    del clause[i]
                    changed = True
        return clause

    if True:
        print("Reduced matrix: (true | false  atom)")
        for (row, atom) in M:
            x = ''
            for t in tr:
                x += '1' if row[t] else '0'
            x += ' | '
            for f in fl:
                x += '1' if row[f] else '0'
            x += "  " + str(atom)
            print(x)

    # dnf is a list of lists. Inner is "and", outer is "or"
    dnf = [[(a, M[a][0][t]) for a in range(len(M))] for t in tr]
    dnf = [reduce(clause) for clause in dnf]
    minimal = []
    dnf.sort(key = len)
    # need to cover all the true models
    remaining_tr = set(tr)
    for clause in dnf:
        keep = False
        old = set(remaining_tr)
        for t in old:
            if all(M[a][0][t] == value for (a, value) in clause):
                remaining_tr.remove(t)
                keep = True
        if keep:
            minimal.append(clause)
    dnf = minimal
    used_literals = set(a for clause in dnf for (a, _) in clause)
    print("Used", len(used_literals), "literals")
    return Or([And([M[a][1] if polarity else Not(M[a][1]) for (a, polarity) in clause]) for clause in dnf])

# M has a row per literal and a column per model. A model x corresponds to
# Mx in the sat formula,
def compute_minimal_with_z3(M, model_positions, sat_formula):
    N_clauses = 10

    solver = z3.Solver()
    B = z3.Bool
    solver.add(z3.simplify(sat_formula))
    p_terms = [[B("xp{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    n_terms = [[B("xn{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    print("Encoding model constraints")
    for x, m_index in model_positions.items():
        definition = []
        for i in range(N_clauses):
            clause = []
            for j, (row, atom) in enumerate(M):
                if row[m_index]:
                    clause.append(p_terms[i][j])
                else:
                    clause.append(n_terms[i][j])
            definition.append(z3.Or(*clause))
        solver.add(B("M"+str(x)) == z3.And(*definition))
    # A clause may not have both positive and negative instances of an atom
    print("Adding disjunction exclusions")
    for i in range(N_clauses):
        for j in range(len(M)):
            solver.add(z3.Or(z3.Not(B("xp{}_{}".format(i,j))),
                             z3.Not(B("xn{}_{}".format(i,j)))))
    num_literals = z3.Sum(*[z3.If(z3.Or(*[B("{}{}_{}".format(p, i, j)) for i in range(N_clauses) for p in ["xp", "xn"]]), 1, 0) for j in range(len(M))])
    print("Constructed minimization problem")
    for K_bound in range(0, len(M) + 1):
        solver.push()
        solver.add(num_literals <= K_bound)
        r = solver.check()
        if r == z3.sat:
            print("Found a formula with", K_bound, "literals and", N_clauses, "clauses")
            assignment = solver.model()
            f = []
            for i in range(N_clauses):
                cl = []
                for j, (row, atom) in enumerate(M):
                    if assignment[B("xp{}_{}".format(i,j))]:
                        cl.append(atom)
                    elif assignment[B("xn{}_{}".format(i,j))]:
                        cl.append(Not(atom))
                cl.sort()
                f.append(Or(cl))
            f.sort()
            f_minimal = []
            for clause in f:
                if len(f_minimal) > 0 and f_minimal[-1] == clause:
                    continue
                f_minimal.append(clause)
            return And(f_minimal)
        else:
            print("Couldn't do it in", K_bound, "literals and", N_clauses, "clauses")
        solver.pop()
    assert False

# models is a map from name (eg M134) to model. sat_formula is a formula that
# uses the variables M_i, and should be made true by the resulting formula.
# sat_formula must be satisfiable, but may potentially have many satisfying
# assignments that must be explored to find a good generalizable matrix formula.
def infer_matrix(models, sig, sat_formula):

    trivial = trivial_check(sat_formula, models.keys())
    if trivial is not None:
        return trivial

    print ("Computing atom-model matrix")
    model_positions = dict((model_id, i) for (i, model_id) in enumerate(models.keys()))
    atom_model_matrix = [(array('b', (check(a, m) for m in models.values())), a) for a in atoms(sig)]
    atom_model_matrix_reduced = [(row, atom) for (row, atom) in atom_model_matrix if not (all(row) or all(not x for x in row))]
    atom_model_matrix_reduced.sort()
    for i in range(len(atom_model_matrix_reduced)-1, 1, -1):
        (r1, a1), (r2, a2) = atom_model_matrix_reduced[i-1], atom_model_matrix_reduced[i]
        if r1 == r2:
            del atom_model_matrix_reduced[i]

    print ("Retained", len(atom_model_matrix_reduced), "of", len(atom_model_matrix), "atoms")
    print ("Have", len(models), "distinct FO-types/models")

    # print("\n".join(["".join('1' if x else '0' for x in row) + " " + str(atom) for (row, atom) in atom_model_matrix_reduced]))
    # print (sat_formula)
    # print (models.keys())

    M = atom_model_matrix_reduced

    m = compute_minimal_with_z3(M, model_positions, sat_formula)
    return trivial_simplify(m)

    (true_model_ids, false_model_ids) = compute_assignment(sat_formula, models.keys())
    dnf = compute_dnf(M, [model_positions[i] for i in true_model_ids], [model_positions[i] for i in false_model_ids])
    dnf = trivial_simplify(dnf)
    return dnf

def trivial_check(sat_formula, vars):
    s = z3.Solver()
    s.add(sat_formula)
    s.push()
    for x in vars: s.add(z3.Bool('M'+str(x)))
    if s.check() == z3.sat:
        return And([])
    s.pop()
    for x in vars: s.add(z3.Not(z3.Bool('M'+str(x))))
    if s.check() == z3.sat:
        return Or([])
    return None


def compute_assignment(sat_formula, vars):
    # OLD: computes one assignment
    solver = z3.Solver()
    solver.add(sat_formula)
    r = solver.check()
    assert r == z3.sat
    assignment = solver.model()

    # Minimize the model by using the unsat_core to find only those variables
    # which must be set
    s2 = z3.Solver()
    s2.add(z3.Not(sat_formula))
    z3_vars = [z3.Bool('M'+str(x)) for x in vars]
    expect_unsat = s2.check([v if assignment[v] else z3.Not(v) for v in z3_vars])
    assert expect_unsat == z3.unsat
    unsat_core = s2.unsat_core()
    # print("Formula:\n", z3.simplify(f))
    # print("Unsat core:", unsat_core)\
    true_model_ids = set()
    false_model_ids = set()
    for x in vars:
        if z3.Bool('M'+str(x)) in unsat_core:
            true_model_ids.add(x)
        elif z3.Not(z3.Bool('M'+str(x))) in unsat_core:
            false_model_ids.add(x)
    return true_model_ids, false_model_ids


    # if len(false_models) < len(true_models):
    #     cnf = And([Not(all_facts2(fl, sig)) for fl in false_models])
    #     cnf = trivial_simplify(cnf)
    #     cnf = simplify_formula_wrt_models(cnf, true_models, false_models)
    #     cnf = simplify_wrt_sat_formula(cnf, models, sat_formula)
    #     cnf = trivial_simplify(cnf)
    #     final = cnf
    # else:
    #     dnf = Or([all_facts2(tr, sig) for tr in true_models])
    #     dnf = trivial_simplify(dnf)
    #     dnf = simplify_formula_wrt_models(dnf, true_models, false_models)
    #     dnf = simplify_wrt_sat_formula(dnf, models, sat_formula)
    #     dnf = trivial_simplify(dnf)
    #     final = dnf
    # return final

# Simplify boolean formula preserving truth on true models and falsehood on false models
def simplify_formula_wrt_models(formula, true_models, false_models):
    def false_in_false_models(f):
        for false_model in false_models:
            if check(f, false_model):
                return False
        return True

    def separates(f):
        for true_model in true_models:
            if not check(f, true_model):
                return False
        for false_model in false_models:
            if check(f, false_model):
                return False
        return True

    assert separates(formula)
    # cont = True
    # while cont:
    #     cont = False
    #     for r in reversed(list(removals(formula, False))):
    #         if false_in_false_models(r):
    #             formula = r
    #             cont = True
    #             break

    assert separates(formula)
    cont = True
    while cont:
        cont = False
        for r in reversed(list(removals(formula))):
            if separates(r):
                formula = r
                cont = True
                break

    return formula

def removals(f, allow_dropping_disjuncts = True):
    if isinstance(f, And):
        for i in range(len(f.c)):
            before = f.c[:i]
            after = f.c[i+1:]
            yield And(before+after)
            for sub_f in removals(f.c[i]):
                yield And(before + [sub_f] + after)
    if isinstance(f, Or):
        for i in range(len(f.c)):
            before = f.c[:i]
            after = f.c[i+1:]
            if allow_dropping_disjuncts:
                yield Or(before+after)
            for sub_f in removals(f.c[i]):
                yield Or(before + [sub_f] + after)
            if allow_dropping_disjuncts:
                yield f.c[i]
    if isinstance(f, Not):
        for sub_f in removals(f.f):
            yield Not(sub_f)
    else:
        return

def atoms(sig):
    terms_by_sort = dict([(s,[]) for s in sig.sorts])

    for c, sort in sig.constants.items():
        terms_by_sort[sort].append(Var(c))

    for iter in range(K_function_unrolling):
        prior_terms = copy.deepcopy(terms_by_sort)
        for f, (arg_sorts, result_sort) in sig.functions.items():
            arg_terms = itertools.product(*[prior_terms[s] for s in arg_sorts])
            terms_by_sort[result_sort].extend([Func(f, list(a)) for a in arg_terms])

    for r, sorts in sig.relations.items():
        for args in itertools.product(*[terms_by_sort[s] for s in sorts]):
            yield Relation(r, args)

    for sort in sig.sorts:
        for (a,b) in itertools.product(terms_by_sort[sort], terms_by_sort[sort]):
            yield (Equal(a, b))


def all_facts2(model, sig):
    return And([a if check(a, model) else Not(a) for a in atoms(sig)])
    #
    # terms_by_sort = dict([(s,[]) for s in sig.sorts])
    #
    # for c in model.constants.keys():
    #     s = model.sorts[model.constants[c]]
    #     terms_by_sort[s].append(Var(c))
    #
    # for iter in range(K_function_unrolling):
    #     prior_terms = copy.deepcopy(terms_by_sort)
    #     for f, (arg_sorts, result_sort) in sig.functions.items():
    #         arg_terms = itertools.product(*[prior_terms[s] for s in arg_sorts])
    #         terms_by_sort[result_sort].extend([Func(f, list(a)) for a in arg_terms])
    #
    # relations = []
    # for r,sorts in sig.relations.items():
    #     model_r = model.relations[r]
    #     for args in itertools.product(*[terms_by_sort[s] for s in sorts]):
    #         if tuple(resolve_term(a, model) for a in args) in model_r:
    #             relations.append(Relation(r, args))
    #         else:
    #             relations.append(Not(Relation(r, args)))
    # # equalities
    # equalities = []
    # for sort in sig.sorts:
    #     for (a,b) in itertools.product(terms_by_sort[sort], terms_by_sort[sort]):
    #         if resolve_term(a, model) == resolve_term(b, model):
    #             equalities.append(Equal(a, b))
    #         else:
    #             equalities.append(Not(Equal(a, b)))
    #
    # return And(equalities + relations)

# def all_facts(model, sig):
#     equalities = [(Equal(Var(x),Var(y)) if model.constants[x] == model.constants[y]
#                    else Not(Equal(Var(x), Var(y))))
#                   for x in model.constants for y in model.constants if x < y]
#
#     def constants_of_sort(s):
#         return [c for c in model.constants if model.sorts[model.constants[c]] == s]
#     relations = []
#     for r,sorts in sig.relations.items():
#         model_r = model.relations[r]
#         for args in itertools.product(*[constants_of_sort(s) for s in sorts]):
#             args_as_vars = [Var(a) for a in args]
#             if tuple([model.constants[a] for a in args]) in model_r:
#                 relations.append(Relation(r, args_as_vars))
#             else:
#                 relations.append(Not(Relation(r, args_as_vars)))
#     return And(equalities + relations)


def trivial_simplify(f):
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



def simplify_wrt_sat_formula(formula, models, sat_formula):
    s3 = z3.Solver()
    s3.add(sat_formula)
    def will_work(f):
        s3.push()
        for x, m in models.items():
            if check(f, m):
                s3.add(z3.Bool('M'+str(x)))
            else:
                s3.add(z3.Not(z3.Bool('M'+str(x))))
        r = s3.check()
        s3.pop()
        return r == z3.sat

    assert will_work(formula)
    cont = True
    while cont:
        cont = False
        for r in reversed(list(removals(formula))):
            if will_work(r):
                formula = r
                # print("Further simplified formula.")
                cont = True
                break
    return formula
