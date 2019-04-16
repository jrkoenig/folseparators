
import itertools
import z3

from logic import *
from check import check
from separate import separate

sorts_to_z3 = {}
z3_rel_func = {}

def toZ3(f, env):
    def R(f): return toZ3(f, env)
    if isinstance(f, And):
        return z3.And(*[R(x) for x in f.c])
    elif isinstance(f, Or):
        return z3.Or(*[R(x) for x in f.c])
    elif isinstance(f, Not):
        return z3.Not(R(f.f))
    elif isinstance(f, Relation):
        return z3_rel_func[f.rel](*[R(x) for x in f.args])
    elif isinstance(f, Func):
        return z3_rel_func[f.f](*[R(x) for x in f.args])
    elif isinstance(f, Equal):
        return R(f.args[0]) == R(f.args[1])
    elif isinstance(f, Var):
        return z3.Const(f.var, sorts_to_z3[env.lookup_var(f.var)])
    elif isinstance(f, Forall) or isinstance(f, Exists):
        env.bind(f.var, f.sort)
        sub_f = toZ3(f.f, env)
        env.pop()
        bv = z3.Const(f.var, sorts_to_z3[f.sort])
        return z3.ForAll(bv, sub_f) if isinstance(f, Forall) else z3.Exists(bv, sub_f)
    else:
        print ("Can't translate", f)
        assert False

def extract_model(solver, sig, label = ""):
    m = solver.model()
    M = Model(sig)
    M.label = label
    z3_to_model_elems = {}
    # add elements
    for sort in sorted(sig.sorts):
        univ = m.get_universe(sorts_to_z3[sort])
        assert len(univ) > 0
        for e in sorted(univ, key = str):
            z3_to_model_elems[str(e)] = M.add_elem(str(e), sort)
    # assign constants
    for const, sort in sorted(sig.constants.items()):
        M.add_constant(const, str(m.evaluate(z3.Const(const, sorts_to_z3[sort]), model_completion=True)))
    # assign relations
    for rel, sorts in sorted(sig.relations.items()):
        univs = [m.get_universe(sorts_to_z3[s]) for s in sorts]
        for t in itertools.product(*univs):
            ev = m.evaluate(z3_rel_func[rel](*t), model_completion = True)
            if ev:
                M.add_relation(rel, [str(x) for x in t])
    for func, (sorts, _) in sorted(sig.functions.items()):
        univs = [m.get_universe(sorts_to_z3[s]) for s in sorts]
        for t in itertools.product(*univs):
            ev = m.evaluate(z3_rel_func[func](*t), model_completion = True)
            M.add_function(func, [str(x) for x in t], str(ev))
    return M


def learn(sig, axioms, formula):
    # ask z3 if the current formula and the ot
    s = z3.Solver()
    for sort in sig.sorts:
        sorts_to_z3[sort] = z3.DeclareSort(sort, ctx=s.ctx)
    for const, sort in sig.constants.items():
        z3.Const(const, sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
    for fun, (sorts, ret) in sig.functions.items():
        z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])

    print ("Constructed environment")
    env = Environment(sig)
    current = Or([])
    models = []

    for ax in axioms:
        s.add(toZ3(ax, env))

    while True:
        print ("Checking formula")
        have_new_model = False
        negative_was_unsat = False
        positive_was_unsat = False

        if not have_new_model:
            s.push()
            s.add(toZ3(current, env))
            s.add(z3.Not(toZ3(formula, env)))
            res = s.check()
            if res == z3.sat:
                print("Found new negative separating model")
                have_new_model = True
                models.append(extract_model(s, sig, "-"))
                print(print_model(models[-1]))
            elif res == z3.unsat:
                negative_was_unsat = True
            s.pop()

        if not have_new_model:
            s.push()
            s.add(z3.Not(toZ3(current, env)))
            s.add(toZ3(formula, env))
            res = s.check()
            if res == z3.sat:
                print("Found new positive separating model")
                have_new_model = True
                models.append(extract_model(s, sig, "+"))
                print(print_model(models[-1]))
            elif res == z3.unsat:
                positive_was_unsat = True
            s.pop()

        if negative_was_unsat and positive_was_unsat:
            print ("formula matches!")
            print (current)
            return models
        elif have_new_model:
            print ("Have new model, now have", len(models), "models total")
            current = separate(models, sig, 10)
            if current is None:
                raise RuntimeError("couldn't separate models")
            print("Learned new possible formula: ", current)
        else:
            print("Error, z3 did not show equivalence or give a model")
            raise RuntimeError("Z3 error")

if __name__ == "__main__":
    from interpret import interpret
    from parse import parse
    import sys

    if len(sys.argv) not in [1,2]:
        print("Usage: python3 learn.py [file.fol]")
        exit(1)

    file = "conjectures/toy_lock_simple.fol" if len(sys.argv) == 1 else sys.argv[1]
    (sig, axioms, conjectures, models) = interpret(parse(open(file).read()))

    seed = 140297207
    z3.set_param("sat.random_seed", seed, "smt.random_seed", seed, "sls.random_seed", seed, "fp.spacer.random_seed", seed, "nlsat.seed", seed)
    models = learn(sig, axioms, conjectures[0])
    for m in models:
        print(print_model(m))
