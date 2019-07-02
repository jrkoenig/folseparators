
import itertools, random, json, time, sys, argparse
import z3

from interpret import interpret
from parse import parse
from logic import *
from check import check
from separate import Separator


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

def extract_model(m, sig, label = ""):
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

def fm(a, b, env, solver):
    solver.push()
    solver.add(toZ3(a, env))
    solver.add(z3.Not(toZ3(b, env)))
    r = solver.check()
    m = None
    if r == z3.sat:
        m = solver.model()
    solver.pop()
    return (r, m)

def bound_sort_counts(solver, bounds):
    for sort, K in bounds.items():
        S = sorts_to_z3[sort]
        bv = z3.Const("elem_{}".format(sort), S)
        solver.add(z3.ForAll(bv, z3.Or([z3.Const("elem_{}_{}".format(sort, i), S) == bv for i in range(K)])))            

def find_model_or_equivalence(current, formula, env, s):
    (r1, m) = fm(current, formula, env, s)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(current, formula, env, s)
            s.pop()
            if m is not None:
                return extract_model(m, env.sig, "-")
        assert False
    (r2, m) = fm(formula, current, env, s)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(formula, current, env, s)
            s.pop()
            if m is not None:
                return extract_model(m, env.sig, "+")
        assert False
    if r1 == z3.unsat and r2 == z3.unsat:
        return None
    
    # TODO: try bounded model checking up to some limit
    raise RuntimeError("Z3 did not produce equivalence or model")

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

    env = Environment(sig)
    current = Or([])
    separator = Separator(sig, quiet=args.quiet, logic=args.logic, epr_wrt_formulas=axioms+[formula, Not(formula)])

    for ax in axioms:
        s.add(toZ3(ax, env))

    while True:
        if not args.quiet:
            print ("Checking formula")
        result = find_model_or_equivalence(current, formula, env, s)
        if result is None:
            if not args.quiet:
                print ("formula matches!")
                print (current)
            return (current, separator.models)
        else:
            separator.add_model(result)
            if not args.quiet:
                print (print_model(result))
                print ("Have new model, now have", len(separator.models), "models total")
            if args.not_incremental:
                separator.forget_learned_facts()
            current = separator.separate()
            if current is None:
                raise RuntimeError("couldn't separate models")
            
            if not args.quiet:
                print("Learned new possible formula: ", current)

def count_quantifier_prenex(f):
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifier_prenex(f.f)
    else: return 0

def main():
    global args
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", metavar="FILE", help=".fol file to learn conjecture of")
    parser.add_argument("--not-incremental", action="store_true", help="disable incremental inference")
    parser.add_argument("--expand-partial", action="store_true", help="expand partial counterexample models")
    parser.add_argument("--skip-pure-prenex", action="store_true", help="skip pure variables during prenex search")
    parser.add_argument("--skip-pure-matrix", action="store_true", help="skip pure variables during matrix inference")
    parser.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="restrict form of quantifier to given logic (fol is unrestricted)")
    parser.add_argument("-q", "--quiet", action="store_true", help="disable most output")
    args = parser.parse_args()
    
    (sig, axioms, conjectures, models) = interpret(parse(open(args.filename).read()))

    seed = random.randrange(0, 2**31)
    z3.set_param("sat.random_seed", seed, "smt.random_seed", seed, "sls.random_seed", seed, "fp.spacer.random_seed", seed, "nlsat.seed", seed)
    start = time.time()
    formula, models = learn(sig, axioms, conjectures[0])
    end = time.time()
    if not args.quiet:
        for m in models:
            print(print_model(m))
    result = {
        'total_time': end-start,
        'model_count': len(models),
        'formula': str(formula),
        'formula_quantifiers': count_quantifier_prenex(formula)
    }
    
    print(json.dumps(result, separators=(',',':'), indent=None))

if __name__ == "__main__":
    main()