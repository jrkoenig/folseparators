
import itertools, copy, sys
import z3
from array import array

from logic import And, Or, Not, Func, Var, Relation, Equal
from check import check, resolve_term

K_function_unrolling = 1


# models is a map from name (eg M134) to model. sat_formula is a formula that
# uses the variables Mi, and should be made true by the resulting formula.
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
        (r1, _), (r2, _) = atom_model_matrix_reduced[i-1], atom_model_matrix_reduced[i]
        if r1 == r2:
            del atom_model_matrix_reduced[i]

    print ("Retained", len(atom_model_matrix_reduced), "of", len(atom_model_matrix), "atoms")
    print ("Have", len(models), "distinct FO-types/models")

    # print("\n".join(["".join('1' if x else '0' for x in row) + " " + str(atom) for (row, atom) in atom_model_matrix_reduced]))
    # print (sat_formula)
    # print (models.keys())

    m = compute_minimal_with_z3_maxsat(atom_model_matrix_reduced, model_positions, sat_formula)
    return trivial_simplify(m)

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

def compute_minimal_with_z3_maxsat(M, model_positions, sat_formula):
    N_clauses = 10

    solver = z3.Optimize()
    B = z3.Bool
    solver.add(z3.simplify(sat_formula))
    p_terms = [[B("xp{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    n_terms = [[B("xn{}_{}".format(i,j)) for j in range(len(M))] for i in range(N_clauses)]
    print("Encoding model constraints")
    for x, m_index in model_positions.items():
        definition = []
        for i in range(N_clauses):
            clause = []
            for j, (row, _) in enumerate(M):
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
    
    for j in range(len(M)):
        solver.add_soft(z3.Not(z3.Or(*[B("{}{}_{}".format(p, i, j)) for i in range(N_clauses) for p in ["xp", "xn"]])))
    print("Constructed minimization problem")
    r = solver.check()
    if r == z3.sat:
        print("Found a formula")
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
        print("Error, z3 could not solve max-SAT problem")
        assert False

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
