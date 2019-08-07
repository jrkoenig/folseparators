
import itertools, random, json, time, sys, argparse
import z3

from interpret import interpret
from parse import parse
from logic import *
from check import check
from separate import Separator, SeparatorReductionV1, SeparatorReductionV2
from timer import Timer, UnlimitedTimer, TimeoutException

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

def fm(a, b, env, solver, timer):
    solver.push()
    solver.add(toZ3(a, env))
    solver.add(z3.Not(toZ3(b, env)))
    r = timer.solver_check(solver)
    m = solver.model() if r == z3.sat else None
    solver.pop()
    return (r, m)

def bound_sort_counts(solver, bounds):
    for sort, K in bounds.items():
        S = sorts_to_z3[sort]
        bv = z3.Const("elem_{}".format(sort), S)
        solver.add(z3.ForAll(bv, z3.Or([z3.Const("elem_{}_{}".format(sort, i), S) == bv for i in range(K)])))            

def find_model_or_equivalence(current, formula, env, s, t):
    (r1, m) = fm(current, formula, env, s, t)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(current, formula, env, s, t)
            s.pop()
            if m is not None:
                return extract_model(m, env.sig, "-")
        assert False
    (r2, m) = fm(formula, current, env, s, t)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(formula, current, env, s, t)
            s.pop()
            if m is not None:
                return extract_model(m, env.sig, "+")
        assert False
    if r1 == z3.unsat and r2 == z3.unsat:
        return None
    
    # TODO: try bounded model checking up to some limit
    # test = Timer(1000000)
    # with test:
    #     r = fm(current, formula, env, s, test)
    #     if repr(r) != "unknown":
    #         print("Inconsistency in timeouts")

    raise RuntimeError("Z3 did not produce equivalence or model")

def learn(sig, axioms, formula, timeout):
    counterexample_timer = Timer(timeout)
    separation_timer = Timer(timeout)
    matrix_timer = UnlimitedTimer()
    
    S = SeparatorReductionV1 if args.separator == 'v1' else\
        SeparatorReductionV2 if args.separator == 'v2' else\
        Separator
        
    separator = S(sig, quiet=args.quiet, logic=args.logic, epr_wrt_formulas=axioms+[formula, Not(formula)])
    env = Environment(sig)
    current = Or([])

    try:
        with counterexample_timer:
            s = z3.Solver()
            for sort in sig.sorts:
                sorts_to_z3[sort] = z3.DeclareSort(sort, ctx=s.ctx)
            for const, sort in sig.constants.items():
                z3.Const(const, sorts_to_z3[sort])
            for rel, sorts in sig.relations.items():
                z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
            for fun, (sorts, ret) in sig.functions.items():
                z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])

            for ax in axioms:
                s.add(toZ3(ax, env))

        while True:
            with counterexample_timer:
                if not args.quiet:
                    print ("Checking formula")
                result = find_model_or_equivalence(current, formula, env, s, counterexample_timer)
                counterexample_timer.check_time()
                if result is None:
                    if not args.quiet:
                        print ("formula matches!")
                        print (current)
                    return (True, current, separator.models, counterexample_timer, separation_timer, matrix_timer, "(none)")
            
            with separation_timer:
                separator.add_model(result)
                if not args.quiet:
                    print (print_model(result))
                    print ("Have new model, now have", len(separator.models), "models total")
                if args.not_incremental:
                    separator.forget_learned_facts()
                current = separator.separate(timer = separation_timer, matrix_timer = matrix_timer)
                if current is None:
                    raise RuntimeError("couldn't separate models")
                if not args.quiet:
                    print("Learned new possible formula: ", current)
    except TimeoutException:
        return (False, current, separator.models, counterexample_timer, separation_timer, matrix_timer, "timeout")
    except RuntimeError as e:
        print("Error:", e)
        return (False, current, separator.models, counterexample_timer, separation_timer, matrix_timer, str(e))


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
    parser.add_argument("--timeout", metavar='T', type=float, default = 1000000, help="timeout for each of learning and separation (seconds)")
    parser.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="restrict form of quantifier to given logic (fol is unrestricted)")
    parser.add_argument("--separator", choices=('naive', 'v1', 'v2'), default='naive', help="separator algorithm to use")
    parser.add_argument("-q", "--quiet", action="store_true", help="disable most output")
    args = parser.parse_args()
    
    (sig, axioms, conjectures, models) = interpret(parse(open(args.filename).read()))

    seed = random.randrange(0, 2**31)
    z3.set_param("sat.random_seed", seed, "smt.random_seed", seed, "sls.random_seed", seed, "fp.spacer.random_seed", seed, "nlsat.seed", seed)    
    success, formula, models, ctimer, stimer, mtimer, error = learn(sig, axioms, conjectures[0], timeout = args.timeout)
    if not args.quiet:
        for m in models:
            print(print_model(m))
    result = {
        'success': success,
        'total_time': ctimer.elapsed() + stimer.elapsed(),
        'separation_time': stimer.elapsed(),
        'counterexample_time': ctimer.elapsed(),
        'matrix_time': mtimer.elapsed(),
        'model_count': len(models),
        'formula': str(formula),
        'formula_quantifiers': count_quantifier_prenex(formula),
        'error': error
    }
    
    print(json.dumps(result, separators=(',',':'), indent=None))

if __name__ == "__main__":
    main()