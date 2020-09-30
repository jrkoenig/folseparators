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

import itertools, random, json, time, sys, argparse, copy
from collections import defaultdict
import z3

from .interpret import interpret, FOLFile
from .parse import parse
from .logic import Signature, Environment, Model, And, Or, Not, Exists, Forall, Equal, Relation, Formula, Term, Var, Func, Iff, model_is_complete_wrt_sig, model_is_partial_wrt_sig
from .check import check
from .separate import Separator, HybridSeparator, DiagonalPartialSeparator
from .timer import Timer, UnlimitedTimer, TimeoutException
from .cvc4 import solve_with_cvc4
from typing import *

sorts_to_z3: Dict[str, z3.SortRef] = {}
z3_rel_func: Dict[str, z3.FuncDeclRef] = {}

def toZ3(f: Union[Formula, Term], env: Environment, sorts: Dict[str, z3.SortRef] = sorts_to_z3, rel_funcs: Dict[str, z3.FuncDeclRef] = z3_rel_func) -> z3.ExprRef:
    def R(f: Union[Formula, Term]) -> z3.ExprRef: return toZ3(f, env, sorts, rel_funcs)
    if isinstance(f, And):
        if len(f.c) == 0:
            return z3.BoolVal(True)
        return z3.And(*[R(x) for x in f.c])
    elif isinstance(f, Or):
        if len(f.c) == 0:
            return z3.BoolVal(False)
        return z3.Or(*[R(x) for x in f.c])
    elif isinstance(f, Not):
        return z3.Not(R(f.f))
    elif isinstance(f, Iff):
        return R(f.c[0]) == R(f.c[1])
    elif isinstance(f, Relation):
        return rel_funcs[f.rel](*[R(x) for x in f.args])
    elif isinstance(f, Func):
        return rel_funcs[f.f](*[R(x) for x in f.args])
    elif isinstance(f, Equal):
        return R(f.args[0]) == R(f.args[1])
    elif isinstance(f, Var):
        v = env.lookup_var(f.var)
        if v is None: raise RuntimeError("Cannot convert invalid formula to z3")
        return z3.Const(f.var, sorts[v])
    elif isinstance(f, Forall) or isinstance(f, Exists):
        env.bind(f.var, f.sort)
        sub_f = R(f.f)
        env.pop()
        bv = z3.Const(f.var, sorts[f.sort])
        return z3.ForAll(bv, sub_f) if isinstance(f, Forall) else z3.Exists(bv, sub_f)
    else:
        print ("Can't translate", f)
        assert False

def toZ32(f: Union[Formula, Term], env: Environment, sorts: Dict[str, z3.SortRef], rel_funcs: Dict[str, z3.FuncDeclRef], ctx: z3.Context) -> z3.ExprRef:
    def R(f: Union[Formula, Term]) -> z3.ExprRef: return toZ32(f, env, sorts, rel_funcs, ctx)
    if isinstance(f, And):
        if len(f.c) == 0:
            return z3.BoolVal(True, ctx)
        return z3.And(*[R(x) for x in f.c])
    elif isinstance(f, Or):
        if len(f.c) == 0:
            return z3.BoolVal(False, ctx)
        return z3.Or(*[R(x) for x in f.c])
    elif isinstance(f, Not):
        return z3.Not(R(f.f))
    elif isinstance(f, Iff):
        return R(f.c[0]) == R(f.c[1])
    elif isinstance(f, Relation):
        return rel_funcs[f.rel](*[R(x) for x in f.args])
    elif isinstance(f, Func):
        return rel_funcs[f.f](*[R(x) for x in f.args])
    elif isinstance(f, Equal):
        return R(f.args[0]) == R(f.args[1])
    elif isinstance(f, Var):
        v = env.lookup_var(f.var)
        if v is None: raise RuntimeError("Cannot convert invalid formula to z3")
        return z3.Const(f.var, sorts[v])
    elif isinstance(f, Forall) or isinstance(f, Exists):
        env.bind(f.var, f.sort)
        sub_f = R(f.f)
        env.pop()
        bv = z3.Const(f.var, sorts[f.sort])
        return z3.ForAll(bv, sub_f) if isinstance(f, Forall) else z3.Exists(bv, sub_f)
    else:
        print ("Can't translate", f)
        assert False

def extract_model(m: z3.ModelRef, sig: Signature, label: str = "") -> Model:
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
        M.add_constant(const, str(m.eval(z3.Const(const, sorts_to_z3[sort]), model_completion=True)))
    # assign relations
    for rel, sorts in sorted(sig.relations.items()):
        univs = [m.get_universe(sorts_to_z3[s]) for s in sorts]
        for t in itertools.product(*univs):
            ev = m.eval(z3_rel_func[rel](*t), model_completion = True)
            M.add_relation(rel, [str(x) for x in t], True if ev else False)
    for func, (sorts, _) in sorted(sig.functions.items()):
        univs = [m.get_universe(sorts_to_z3[s]) for s in sorts]
        for t in itertools.product(*univs):
            ev = m.eval(z3_rel_func[func](*t), model_completion = True)
            M.add_function(func, [str(x) for x in t], str(ev))
    assert model_is_complete_wrt_sig(M, sig)
    return M


def expand_completions(M: Model) -> Iterable[Model]:
    for c, e in M.constants.items():
        if e is None:
            for e_i in M.universe(M.sig.constants[c]):
                Mp = M.copy()
                Mp.add_constant(c, e_i)
                yield from expand_completions(Mp)
            return
    for r, interp in M.relations.items():
        sorts = M.sig.relations[r]
        for t in itertools.product(*[M.elems_of_sort[sort] for sort in sorts]):
            if t not in interp:
                for truth in [True, False]:
                    Mp = M.copy()
                    Mp.add_relation(r, [M.names[x] for x in t], truth)
                    yield from expand_completions(Mp)
                return
    for f, finterp in M.functions.items():
        sorts, ret_sort = M.sig.functions[f]
        for t in itertools.product(*[M.elems_of_sort[sort] for sort in sorts]):
            if t not in finterp:
                for e_i in M.universe(ret_sort):
                    Mp = M.copy()
                    Mp.add_function(f, [M.names[x] for x in t], e_i)
                    yield from expand_completions(Mp)
                return
    yield M
    
def sig_without_primed(old: Signature) -> Signature:
    sig = Signature()
    sig.sorts = set(old.sorts)
    sig.finalize_sorts()
    sig.relations = dict(x for x in old.relations.items() if not x[0].endswith('\''))
    sig.constants = dict(x for x in old.constants.items() if not x[0].endswith('\''))
    sig.functions = dict(x for x in old.functions.items() if not x[0].endswith('\''))
    return sig
    
def two_state_pre(M: Model) -> Model:
    '''Projects the pre-state out of a two-state model as a one state model'''
    Mp = M.copy()
    Mp.sig = sig_without_primed(M.sig)
    Mp.relations = dict(x for x in Mp.relations.items() if not x[0].endswith('\''))
    Mp.constants = dict(x for x in Mp.constants.items() if not x[0].endswith('\''))
    Mp.functions = dict(x for x in Mp.functions.items() if not x[0].endswith('\''))
    assert model_is_partial_wrt_sig(Mp, Mp.sig)
    return Mp
    

def two_state_post(M: Model) -> Model:
    '''Projects the post-state out of a two-state model as a one state model'''
    Mp = M.copy()
    Mp.sig = sig_without_primed(M.sig)
    Mp.relations = dict(x for x in Mp.relations.items() if not x[0].endswith('\''))
    Mp.constants = dict(x for x in Mp.constants.items() if not x[0].endswith('\''))
    Mp.functions = dict(x for x in Mp.functions.items() if not x[0].endswith('\''))
    # overwrite unprimed symbols with primed ones
    for x, r in M.relations.items():
        if x.endswith('\''):
            Mp.relations[x[:-1]] = r
    for x, c in M.constants.items():
        if x.endswith('\''):
            Mp.constants[x[:-1]] = c
    for x, f in M.functions.items():
        if x.endswith('\''):
            Mp.functions[x[:-1]] = f
    assert model_is_partial_wrt_sig(Mp, Mp.sig)
    return Mp

def generalize_model(M: Model, formula: Formula, two_state: bool = False, label:str = '') -> Model:

    ctx = z3.Context()
    s = z3.Solver(ctx=ctx)

    sig = M.sig
    env = Environment(sig)
    _sorts_to_z3: Dict[str, z3.SortRef] = {}
    _z3_rel_func: Dict[str, z3.FuncDeclRef] = {}

    for sort in sig.sorts:
        _sorts_to_z3[sort] = z3.DeclareSort(sort, ctx = ctx)
    for const, sort in sig.constants.items():
        z3.Const(const, _sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        _z3_rel_func[rel] = z3.Function(rel, *[_sorts_to_z3[x] for x in sorts], z3.BoolSort(ctx= ctx))
    for fun, (sorts, ret) in sig.functions.items():
        _z3_rel_func[fun] = z3.Function(fun, *[_sorts_to_z3[x] for x in sorts], _sorts_to_z3[ret])

    s.set("unsat_core", True, "core.minimize", True)
    elems = []
    elems_by_sort: DefaultDict[str, List[z3.ExprRef]] = defaultdict(list)
    for n, sort in zip(M.names, M.sorts):
        constant = z3.Const(n, _sorts_to_z3[sort])
        elems.append(constant)
        elems_by_sort[sort].append(constant)
    
    # Bound each sort and ensure constants are distinct
    for sort in M.sig.sorts:
        consts = elems_by_sort[sort]
        x = z3.Const(f"__x_{sort}", _sorts_to_z3[sort])
        s.add(z3.Distinct(*consts))
        s.add(z3.ForAll(x, z3.Or(*[x == c for c in consts])))

    
    Mp = Model(M.sig)
    for name, sort in zip(M.names, M.sorts):
        Mp.add_elem(name, sort)
    
    class Fact(object):
        def __init__(self, kind:str, ident: Tuple[str,...], desc: str = '') -> None:
            self.z3_var: z3.ExprRef = z3.BoolVal(True)
            self.desc = desc
            self.kind = kind
            self.ident = ident
            self.applied = False
            self.index = -1

    # fact_vars: List[z3.ExprRef] = []
    # facts: List[Callable] = []
    # fact_desc: List[str] = []
    # fact_size_factor: List[int] = []

    facts: List[Fact] = []
    normal_facts_by_id: Dict[Tuple[str, ...], Fact] = {}

    def make_facts() -> None:
        next_var_index = 0
        def next_var() -> z3.ExprRef:
            nonlocal next_var_index
            v = z3.Bool(f"__iv_{next_var_index}", ctx=ctx)
            next_var_index += 1
            return v
        def add_fact(f: Fact) -> Fact:
            f.z3_var = next_var()
            f.index = len(facts)
            facts.append(f)
            if not f.kind.endswith('='):
                normal_facts_by_id[f.ident] = f
            return f
        
        
        for c, e in M.constants.items():
            assert e is not None
            n = M.names[e]
            f = add_fact(Fact('constant', (c,), desc=f"{c} == {n}"))
            s.add(z3.Implies(f.z3_var, z3.Const(c, _sorts_to_z3[M.sig.constants[c]]) == elems[e]))
            
        for r, rel in M.relations.items():
            for args, val in rel.items():
                R = _z3_rel_func[r](*[elems[i] for i in args])
                f = add_fact(Fact('relation', (r, *(M.names[a] for a in args)), desc = f"{R} == {val}"))
                s.add(z3.Implies(f.z3_var, R if val else z3.Not(R)))
                
        for fn, func in M.functions.items():
            for args, result in func.items():
                F = _z3_rel_func[fn](*[elems[i] for i in args])
                n = M.names[result]
                f = add_fact(Fact('function', (fn, *(M.names[a] for a in args)), desc = f"{F} == {n}"))
                s.add(z3.Implies(f.z3_var, F == elems[result]))

        # now add all the two-state equalities:
        if two_state:
            for c, e in M.constants.items():
                if c.endswith('\'') and c[:-1] in M.constants and M.constants[c] == M.constants[c[:-1]]:
                    c_pre = c[:-1]
                    sort = _sorts_to_z3[M.sig.constants[c]]
                    f = add_fact(Fact('constant=', (c_pre,), desc=f"{c_pre} == {c}"))
                    s.add(z3.Implies(f.z3_var, z3.Const(c_pre, sort) == z3.Const(c, sort)))
        
            for r, rel in M.relations.items():
                for args, val in rel.items():
                    if r.endswith('\'') and r[:-1] in M.relations and rel[args] == M.relations[r[:-1]][args]:
                        r_pre = r[:-1]
                        R = _z3_rel_func[r](*[elems[i] for i in args])
                        R_pre = _z3_rel_func[r_pre](*[elems[i] for i in args])
                        f = add_fact(Fact('relation=', (r_pre, *(M.names[a] for a in args)), desc = f"{R_pre} == {R}"))
                        s.add(z3.Implies(f.z3_var, R_pre == R))
                        

                        # fact_vars.append(v)
                        # constraint = Iff(Relation(r_pre, [Var(M.names[e]) for e in args]), Relation(r, [Var(M.names[e]) for e in args]))
                        # facts.append(lambda constraint=constraint: Mp.constraints.append(constraint))
                        # fact_size_factor.append(1)
                        # fact_desc.append(f"{R_pre} == {R}")

            for fn, func in M.functions.items():
                for args, result in func.items():
                    if fn.endswith('\'') and fn[:-1] in M.functions and func[args] == M.functions[fn[:-1]][args]:
                        fn_pre = fn[:-1]
                        F_pre = _z3_rel_func[fn_pre](*[elems[i] for i in args])
                        F = _z3_rel_func[fn](*[elems[i] for i in args])
                        f = add_fact(Fact('function=', (fn_pre, *(M.names[a] for a in args)), desc=f"{F_pre} == {F}"))
                        s.add(z3.Implies(f.z3_var, F_pre == F))
                        # fact_vars.append(v)
                        # constraint = Equal(Func(f_pre, [Var(M.names[e]) for e in args]), Func(f, [Var(M.names[e]) for e in args]))
                        # facts.append(lambda constraint=constraint: Mp.constraints.append(constraint))
                        # fact_size_factor.append(1)
                        # fact_desc.append(f"{F_pre} == {F}")

        
    make_facts()
    
    s.add(toZ32(Not(formula), env, _sorts_to_z3, _z3_rel_func, ctx))

    core = list(range(len(facts)))
    
    # minimize the core
    result = s.check(*[facts[i].z3_var for i in core])
    if result == z3.sat:
        print("Unexpected sat in generalize_model():")
        print(s.model())
        for xx in s.assertions():
            print(xx)
        print(M)
        print(formula)
        print(check(formula, M))
    
    assert result == z3.unsat
    
    final_core: List[int] = []
    while len(core) > 0:
        result = s.check(*[facts[i].z3_var for i in core[1:]], *[facts[i].z3_var for i in final_core])
        if result == z3.unsat:
            pass
        else:
            final_core.append(core[0])
        core = core[1:]
        
    core = final_core

    # Use z3 to find the unsat core
    # solver_core = s.unsat_core()
    # solver_int_core: Set[int] = set()
    # for x in solver_core:
    #     n = str(x)
    #     assert n.startswith("__iv_")
    #     solver_int_core.add(int(n[5:]))

    # core = list(solver_int_core)
    
    completions = 1

    # construct the final result in Mp
    for i,f in enumerate(facts):
        if not f.kind.endswith('='):
            continue
        f_pre = normal_facts_by_id[f.ident]
        f_post = normal_facts_by_id[(f.ident[0]+'\'', *f.ident[1:])]
        
        size = 2 # for relation=
        if f.kind == 'constant=':
            size = len([*M.universe(M.sig.constants[f.ident[0]])])
        if f.kind == 'function=':
            size = len([*M.universe(M.sig.functions[f.ident[0]][1])])
        
        f.applied = True

        # If we have x = a and x = x', then we should also have x' = a
        if i in core and f_pre.index in core and f_post.index not in core: 
            core.append(f_post.index)
        # The reverse: if we have x' = a and x = x', then we should also have x = a
        if i in core and f_post.index in core and f_pre.index not in core: 
            core.append(f_pre.index)

        # If this is true, then the equality is used
        if size > 1 and i in core and f_pre.index not in core and f_post.index not in core:
            completions *= size
            # Prevent us from multiplying by these values again
            f_pre.applied = True
            f_post.applied = True

            # Add the constraint to the model
            name = f.ident[0]
            args = f.ident[1:]
            if f.kind == 'constant=':
                Mp.constraints.append(Equal(Var(name), Var(name+'\'')))
            elif f.kind == 'relation=':
                Mp.constraints.append(Iff(Relation(name, [Var(e) for e in args]), Relation(name+'\'', [Var(e) for e in args])))
            elif f.kind == 'function=':
                Mp.constraints.append(Equal(Func(name, [Var(e) for e in args]), Func(name+'\'', [Var(e) for e in args])))
            else: assert False


    for i,f in enumerate(facts):
        if f.applied:
            continue
        if f.kind == 'constant':
            c = f.ident[0]
            if i in core:
                e = M.constants[c]
                assert e is not None
                Mp.add_constant(c, M.names[e])
            else:
                completions *= len([*M.universe(M.sig.constants[c])])
        elif f.kind == 'relation':
            r = f.ident[0]
            args = f.ident[1:]
            args_int = tuple(M.elems[x] for x in args)
            if i in core:
                Mp.add_relation(r, list(args), M.relations[r][args_int])
            else:
                completions *= 2
        elif f.kind == 'function':
            fn = f.ident[0]
            args = f.ident[1:]
            args_int = tuple(M.elems[x] for x in args)
            if i in core:
                Mp.add_function(fn, list(args), M.names[M.functions[fn][args_int]])
            else:
                completions *= len([*M.universe(M.sig.functions[fn][1])])
        else: assert False

    # for i, fact in enumerate(facts):
    #     if i in core:
    #         print(f"CORE {fact.desc}")
    #     else:
    #         print(f"---- {fact.desc}")

    print(f"Generalized to {completions} completions{'' if label == '' else ' ('+label+')'}!")
    return Mp


def fm(a: Formula, b: Formula, env: Environment, solver: z3.Solver, timer: Timer) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
    solver.push()
    solver.add(toZ3(a, env))
    solver.add(z3.Not(toZ3(b, env)))
    r = timer.solver_check(solver)
    m = solver.model() if r == z3.sat else None
    solver.pop()
    return (r, m)

def bound_sort_counts(solver: z3.Solver, bounds: Dict[str, int]) -> None:
    for sort, K in bounds.items():
        S = sorts_to_z3[sort]
        bv = z3.Const("elem_{}".format(sort), S)
        solver.add(z3.ForAll(bv, z3.Or(*[z3.Const("elem_{}_{}".format(sort, i), S) == bv for i in range(K)])))            

def find_model_or_equivalence(current: Formula, formula: Formula, axioms: List[Formula], env: Environment, s: z3.Solver, t: Timer) -> Optional[Model]:
    (r1, m) = fm(current, formula, env, s, t)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(current, formula, env, s, t)
            s.pop()
            if m is not None:
                M = extract_model(m, env.sig, "-")
                print("Original: ", M)
                Mp = generalize_model(M, And(axioms + [Not(formula)]))
                print("Generalized: ", Mp)
                return M
        assert False
    (r2, m) = fm(formula, current, env, s, t)
    if m is not None:
        for k in range(1, 100000):
            s.push()
            bound_sort_counts(s, dict((s,k) for s in env.sig.sorts))
            (_, m) = fm(formula, current, env, s, t)
            s.pop()
            if m is not None:
                M = extract_model(m, env.sig, "+")
                print("Original: ", M)
                Mp = generalize_model(M, And([formula] + axioms))
                print("Generalized: ", Mp)
                return M
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

def find_model_or_equivalence_cvc4(current: Formula, formula: Formula, env: Environment, s: z3.Solver, t: Timer) -> Optional[Model]:

    # Check current => formula
    s.push()
    s.add(toZ3(current, env))
    s.add(z3.Not(toZ3(formula, env)))
    (r1, m) = solve_with_cvc4(s, env.sig, timeout=t.remaining())
    s.pop()
    if m is not None:
        m.label = '-'
        return m
    
    # Check formula => current
    s.push()
    s.add(toZ3(formula, env))
    s.add(z3.Not(toZ3(current, env)))
    (r2, m) = solve_with_cvc4(s, env.sig, timeout=t.remaining())
    s.pop()
    if m is not None:
        m.label = '+'
        return m

    if r1 == z3.unsat and r2 == z3.unsat:
        return None
    raise RuntimeError("CVC4 did not produce equivalence or model")



class LearningResult(object):
    def __init__(self, success: bool, current: Formula, ct: Timer, st: Timer, mt: Timer):
        self.success = success
        self.current = current
        self.counterexample_timer = ct
        self.separation_timer = st
        self.matrix_timer = mt
        self.models: List[Model] = []
        self.reason = ""

def learn(sig: Signature, axioms: List[Formula], formula: Formula, timeout: float, args: Any) -> LearningResult:
    result = LearningResult(False, Or([]), Timer(timeout), Timer(timeout), UnlimitedTimer())
    
    S = HybridSeparator
        
    separator: Separator = S(sig, quiet=args.quiet, logic=args.logic, epr_wrt_formulas=axioms+[formula, Not(formula)], expt_flags=args.expt_flags, blocked_symbols=args.blocked_symbols) 

    env = Environment(sig)
    s = z3.Solver()
    for sort in sig.sorts:
        sorts_to_z3[sort] = z3.DeclareSort(sort)
    for const, sort in sig.constants.items():
        z3.Const(const, sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
    for fun, (sorts, ret) in sig.functions.items():
        z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])
    for ax in axioms:
        s.add(toZ3(ax, env))

    p_constraints: List[int] = []
    n_constraints: List[int] = []
    print("Learning formula with args", sys.argv)
    try:
        while True:
            with result.counterexample_timer:
                if not args.quiet:
                    print ("Checking formula")
                if not args.no_cvc4:
                    r = find_model_or_equivalence_cvc4(result.current, formula, env, s, result.counterexample_timer)
                else:
                    r = find_model_or_equivalence(result.current, formula, axioms, env, s, result.counterexample_timer)
                
                result.counterexample_timer.check_time()
                if r is None:
                    if not args.quiet:
                        print ("formula matches!")
                        print (result.current)
                        # f = open("/tmp/out.fol", "w")
                        # f.write(str(sig))
                        # for m in result.models:
                        #     f.write(str(m))
                        # f.close()
                    result.success = True
                    return result
            
            with result.separation_timer:
                ident = separator.add_model(r)
                result.models.append(r)
                if r.label.startswith("+"):
                    gr = generalize_model(r, And(axioms + [formula]), label='+')
                    p_constraints.append(ident)
                else:
                    gr = generalize_model(r, And(axioms + [Not(formula)]), label='+')
                    n_constraints.append(ident)
                if not args.quiet:
                    print ("New model is:")
                    print (r)
                    print("--- Generalized model is ---")
                    print(gr)
                    print("--- end generalized model ---")
                
                    print ("Have new model, now have", len(result.models), "models total")
                if True:
                    c = separator.separate(pos=p_constraints, neg=n_constraints, imp=[], max_clauses = args.max_clauses, max_depth= args.max_depth, timer = result.separation_timer, matrix_timer = result.matrix_timer)
                if c is None:
                    result.reason = "couldn't separate models under given restrictions"
                    break
                if not args.quiet:
                    print("Learned new possible formula: ", c)
                result.current = c
    except TimeoutException:
        result.reason = "timeout"
    except RuntimeError as e:
        print("Error:", e)
        #raise e
        result.reason = str(e)

    return result


def learn_partial(sig: Signature, axioms: List[Formula], formula: Formula, timeout: float, args: Any) -> LearningResult:
    result = LearningResult(False, Or([]), Timer(timeout), Timer(timeout), UnlimitedTimer())
    
    S = DiagonalPartialSeparator
        
    separator: DiagonalPartialSeparator = S(sig, logic=args.logic) 

    env = Environment(sig)
    s = z3.Solver()
    for sort in sig.sorts:
        sorts_to_z3[sort] = z3.DeclareSort(sort)
    for const, sort in sig.constants.items():
        z3.Const(const, sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
    for fun, (sorts, ret) in sig.functions.items():
        z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])
    for ax in axioms:
        s.add(toZ3(ax, env))

    p_constraints: List[int] = []
    n_constraints: List[int] = []
     
    try:
        while True:
            with result.counterexample_timer:
                if not args.quiet:
                    print ("Checking formula")
                if not args.no_cvc4:
                    r = find_model_or_equivalence_cvc4(result.current, formula, env, s, result.counterexample_timer)
                else:
                    r = find_model_or_equivalence(result.current, formula, axioms, env, s, result.counterexample_timer)
                
                result.counterexample_timer.check_time()
                if r is None:
                    if not args.quiet:
                        print ("formula matches!")
                        print (result.current)
                    result.success = True
                    return result
            
            if r.label == '+':
                print("Generalizing...")
                gr = generalize_model(r, And(axioms + [formula]), label='+')
                if 'generalize-both' in args.expt_flags:
                    separator.add_model(r, True)
                    separator.add_model(gr, True)
                    
                elif 'no-generalize' in args.expt_flags:
                    separator.add_model(r, True)
                else:
                    separator.add_model(gr, True)

            else:
                gr = generalize_model(r, And(axioms + [Not(formula)]), label='-')
                if 'generalize-both' in args.expt_flags:
                    separator.add_model(r, False)
                    separator.add_model(gr, False)
                    
                elif 'no-generalize' in args.expt_flags:
                    separator.add_model(r, False)
                else:
                    separator.add_model(gr, False)

            result.models.append(gr)

            with result.separation_timer:
                if not args.quiet:
                    print ("New model is:")
                    print (gr)
                    print ("Have new model, now have", len(result.models), "models total")
                if True:
                    c = separator.separate(timer = result.separation_timer)
                if c is None:
                    result.reason = "couldn't separate models under given restrictions"
                    break
                if not args.quiet:
                    print("Learned new possible formula: ", c)
                result.current = c
    except TimeoutException:
        result.reason = "timeout"
    except RuntimeError as e:
        print("Error:", e)
        #raise e
        result.reason = str(e)

    return result

def separate(f: FOLFile, timeout: float, args: Any) -> LearningResult:
    result = LearningResult(False, Or([]), Timer(timeout), Timer(timeout), UnlimitedTimer())
    
    S = HybridSeparator
        
    separator: Separator = S(f.sig, quiet=args.quiet, logic=args.logic, epr_wrt_formulas=f.axioms)

    result.models = f.models
    mapping: DefaultDict[str, List[int]] = defaultdict(list)
    for m in f.models:
        mapping[m.label].append(separator.add_model(m))

    try:
        with result.separation_timer:
            p_constraints = [x for a in f.constraint_pos for x in mapping[a]]
            n_constraints = [x for a in f.constraint_neg for x in mapping[a]]
            i_constraints = [(x, y) for a, b in f.constraint_imp for x in mapping[a] for y in mapping[b]]
            print(p_constraints, n_constraints, i_constraints)
            c = separator.separate(pos=p_constraints, neg=n_constraints, imp=i_constraints, \
                                   max_clauses = args.max_clauses, max_depth= args.max_depth, \
                                   timer = result.separation_timer, matrix_timer = result.matrix_timer)
            if c is None:
                result.reason = "couldn't separate models under given restrictions"
            else:
                result.current = c
                result.success = True
                for m in f.models:
                    print(m.label, check(c, m))
    except TimeoutException:
        result.reason = "timeout"
    
    return result
    