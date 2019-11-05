
from collections import defaultdict
import itertools, copy, time, sys, re
from typing import Tuple, TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, List, Dict, DefaultDict, Iterator, TypeVar, Any, Sequence

import z3

from .logic import Forall, Exists, Equal, Relation, And, Or, Not, Formula, Term, Var, Func, Model, Signature
from .check import check, resolve_term
from .matrix import infer_matrix, K_function_unrolling
from .timer import Timer, UnlimitedTimer

Quantifier = Tuple[bool, str]

def collapse(model: Model, sig: Signature, assignment: Iterable[int]) -> str:
    mapping: Dict[int,int] = {}
    sorts: List[str] = []
    def get_element(e: int) -> int:
        if e not in mapping:
            mapping[e] = len(mapping)
            sorts.append(model.sorts[e])
        return mapping[e]

    consts = []
    funcs = []
    rels = []

    for const in sorted(model.constants.keys()):
        consts.append(get_element(model.constants[const]))

    for e in assignment:
        consts.append(get_element(e))

    for _ in range(K_function_unrolling):
        # we need to iterate over elements of the collapsed model in a way
        # consistent with their collapsed identity, hence iterating over them
        # in the mapping value order
        reachable = list(sorted(mapping.keys(), key = lambda x: mapping[x]))
        for f in sorted(model.functions.keys()):
            (arg_sorts, _) = sig.functions[f]
            arg_tuples = itertools.product(*[[r for r in reachable if model.sorts[r] == sort] for sort in arg_sorts])
            f_repr = model.functions[f]
            for t in arg_tuples:
                funcs.append(get_element(f_repr[t]))

    for rel in sorted(model.relations.keys()):
        tuples = model.relations[rel]
        collapsed_tuples = []
        for t in tuples:
            if all([x in mapping for x in t]):
                collapsed_tuples.append(tuple([mapping[x] for x in t]))
        collapsed_tuples.sort()
        rels.append(collapsed_tuples)
    return repr((consts, funcs, rels, sorts))

InstId = Tuple[int, Tuple[int, ...]]
class CollapseCache(object):
    def __init__(self, sig: Signature):
        self.models: List[Model] = []
        self.sig = sig
        self.cache: Dict[InstId, int] = {}
        self.collapsed: Dict[str, int] = {}
        self.assignments: List[InstId] = []
        self.all_assignments: DefaultDict[int, List[InstId]] = defaultdict(list)
    def add_model(self, model: Model) -> None:
        self.models.append(model)
    def get(self, index: int, asgn: List[int]) -> int:
        N = len(self.models[index].sorts)
        assignment = tuple(asgn)
        # ensure elems are integers referring to elements of model index
        assert all(e < N for e in assignment)
        # fast path if assignment has been seen before
        if (index, assignment) in self.cache:
            return self.cache[(index, assignment)]
        # collapse model
        key = collapse(self.models[index], self.sig, assignment)
        if key not in self.collapsed:
            r = len(self.collapsed)
            self.collapsed[key] = r
            self.assignments.append((index, assignment))
        else:
            r = self.collapsed[key]
        self.all_assignments[r].append((index, assignment))
        self.cache[(index, assignment)] = r
        return r
    def get_concrete(self, i: int) -> Model:
        (index, assignment) = self.assignments[i]
        M = copy.deepcopy(self.models[index])
        for var_i, element in enumerate(assignment):
            M.add_constant("x_"+str(var_i), M.names[element])
        return M
    def get_example(self, i: int) -> Tuple[int, Tuple[int, ...]]:
        return self.assignments[i]
    def fo_type_count(self) -> int:
        return len(self.collapsed)
    def __len__(self) -> int:
        return len(self.assignments)

def prefix_is_redundant(prefix: List[Quantifier]) -> bool:
    if len(prefix) == 0: return False
    for i in range(len(prefix) - 1):
        a,b = prefix[i], prefix[i+1]
        if a[0] == b[0] and a[1] > b[1]:
            return True
    return False

def build_prefix_formula(prefix: List[Quantifier], f: Formula, n: int = 0) -> Formula:
    if len(prefix) == 0:
        return f
    (is_forall, sort) = prefix[0]
    if is_forall:
        return Forall("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))
    else:
        return Exists("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))

class VarSet(object):
    def __init__(self) -> None:
        self.vars: Set[int] = set()
        self.pos: Set[int] = set()
        self.neg: Set[int] = set()
    def add(self, v: int, polarity: bool) -> None:
        self.vars.add(v)
        if polarity:
            self.pos.add(v)
        else:
            self.neg.add(v)
    def __iter__(self) -> Iterator[int]: return iter(self.vars)

def formula_for_model(model_index: int, assignment: List[int], prefix_i: int, prefix: List[Quantifier], collapsed: CollapseCache, vars: VarSet, ignore_label:bool = False) -> z3.ExprRef:
    m = collapsed.models[model_index]
    if prefix_i == len(prefix):
        for i, (_, sort) in enumerate(prefix):
            assert(collapsed.models[model_index].sorts[assignment[i]] == sort)
        x = collapsed.get(model_index, assignment)
        v = z3.Bool("M"+str(x))
        polarity = m.label.startswith("+") or ignore_label
        vars.add(x, polarity)
        return v if polarity else z3.Not(v)
    else:
        (is_forall, sort) = prefix[prefix_i]
        formulas = []
        for elem in m.elems_of_sort[sort]:
            f = formula_for_model(model_index, assignment + [elem], prefix_i+1, prefix, collapsed, vars, ignore_label=ignore_label)
            formulas.append(f)
        if is_forall == (m.label.startswith("+") or ignore_label):
            return z3.And(*formulas)
        else:
            return z3.Or(*formulas)

def ae_edges_of(sig: Signature) -> Dict[str, Set[str]]:
    ae: Dict[str, Set[str]] = {sort: set() for sort in sig.sorts}
    for f, (arg_sorts, ret_sort) in sig.functions.items():
        for a in arg_sorts:
            ae[a].add(ret_sort)
    return ae

def update_ae_edges(ae: Dict[str, Set[str]], f: Formula, negate: bool = False, outer_universal_sorts: Set[str] = set()) -> None:
    if isinstance(f, (Equal, Relation)):
        return
    elif isinstance(f, (Or, And)):
        for subf in f.c:
            update_ae_edges(ae, subf, negate, outer_universal_sorts)
    elif isinstance(f, Not):
        update_ae_edges(ae, f.f, not negate, outer_universal_sorts)
    else:
        assert isinstance(f, (Exists, Forall))
        if isinstance(f, Forall) != negate:
            # A, or ~E
            update_ae_edges(ae, f.f, negate, outer_universal_sorts.union(set([f.sort])))
        else:
            # E, or ~A
            for s in outer_universal_sorts:
                ae[s].add(f.sort)
            update_ae_edges(ae, f.f, negate, outer_universal_sorts)

T = TypeVar('T')
def digraph_is_acyclic(edges: Dict[T, Set[T]]) -> bool:
    visited: Set[T] = set()
    time: Dict[T, int] = {}
    def visit(n: T) -> None:
        if n in visited: return
        visited.add(n)
        for m in edges[n]:
            visit(m)
        time[n] = len(time)
    for root in edges.keys():
        visit(root)
    for n, neighbors in edges.items():
        for m in neighbors:
            if time[n] <= time[m]:
                return False
    return True

class PrefixSolver(object):
    def __init__(self, depth: int, sort_indices: Dict[str, int], logic: str = "fol"):
        self.depth = depth
        self.sort_indices = sort_indices
        self.solver = z3.Optimize()
        for d in range(self.depth):
            self.solver.add(z3.PbEq([(self._V(q, d), 1) for q in self._all_quantifiers()], 1))
            if logic == "universal":
                self.solver.add(z3.And([z3.Not(self._V((False, i), d)) for i in sort_indices.keys()]))
            elif logic == "existential":
                self.solver.add(z3.And([z3.Not(self._V((True, i), d)) for i in sort_indices.keys()]))
            else:
                assert logic == "fol"

            if d + 1 < self.depth:
                for i in self.sort_indices.keys():
                    for j in self.sort_indices.keys():
                        if self.sort_indices[i] < self.sort_indices[j]:
                            A_i_dp1 = self._V((True, i), d+1)
                            A_j_d = self._V((True, j), d)
                            E_i_dp1 = self._V((False, i), d+1)
                            E_j_d = self._V((False, j), d)
                            self.solver.add(z3.Not(z3.And(A_j_d, A_i_dp1)))
                            self.solver.add(z3.Not(z3.And(E_j_d, E_i_dp1)))
        for d in range(self.depth):
            self.solver.add_soft(z3.Not(z3.Or([self._V(q, d)
                                                      for q in self._all_quantifiers() if not q[0]])), 2**(depth-d))
    def get(self) -> Optional[List[Quantifier]]:
        r = self.solver.check()
        if r == z3.unsat:
            return None
        m = self.solver.model()
        prefix = []
        for d in range(self.depth):
            for q in self._all_quantifiers():
                if m[self._V(q, d)]:
                    prefix.append(q)
                    break
        assert len(prefix) == self.depth
        return prefix
    def add(self, unsat_core_vars: List[z3.ExprRef]) -> None:
        self.solver.add(z3.Not(z3.And(unsat_core_vars)))
    def _all_quantifiers(self) -> List[Quantifier]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _V(self, quant: Quantifier, depth: int) -> z3.ExprRef:
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

class Separator(object):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        pass
    def add_model(self, model: Model) -> int: raise NotImplemented
    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 max_depth: int = 1000000, max_clauses: int = 10, conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        raise NotImplemented

class SeparatorNaive(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self.sig = sig
        self.collapsed = CollapseCache(sig)
        self.models: List[Model] = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges: Optional[Dict[str, Set[str]]] = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.prefixes: List[List[Quantifier]] = [[]]
        self.prefix_index = 0

    def add_model(self, model: Model) -> int:
        i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)
        return i

    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 max_depth: int = 1000000, max_clauses: int = 10, conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        self.timer = timer
        self.matrix_timer = matrix_timer
        self.max_clauses = max_clauses
        solver = z3.Solver()
        while True:
            if self.prefix_index == len(self.prefixes):
                # We have reached our maximum depth, don't generate larger prefixes
                if len(self.prefixes[0]) == max_depth:
                    return None
                self.prefixes = [[(is_forall, s)]+p for is_forall in [True, False]
                                 for p in self.prefixes for s in sorted(self.sig.sorts)]
                self.prefixes = [p for p in self.prefixes if self._filter_prefix(p)]
                self.prefix_index = 0
            p = self.prefixes[self.prefix_index]
            if not prefix_is_redundant(p):
                if not self.quiet:
                    print ("Prefix:", " ".join([("∀" if is_forall else "∃") + sort + "." for (is_forall, sort) in p]))
                c = self.check_prefix_build_matrix(pos, neg, imp, p, solver)
                if c is not None:
                    return c
            self.prefix_index += 1
    def _filter_prefix(self, p: List[Quantifier]) -> bool:
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            assert self.ae_edges is not None
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True
    def check_prefix_build_matrix(self, pos: Collection[int], neg: Collection[int], imp: Collection[Tuple[int, int]],
                                  prefix: List[Quantifier], solver: z3.Solver) -> Optional[Formula]:
        solver.push()
        vars = VarSet()
        formulas = []
        for m_index in range(len(self.models)):
            formulas.append(z3.Bool(f"v{m_index}") == formula_for_model(m_index, [], 0, prefix, self.collapsed, vars, ignore_label=True))
            self.timer.check_time()

        for po in pos:
            formulas.append(z3.Bool(f"v{po}"))
        for n in neg:
            formulas.append(z3.Not(z3.Bool(f"v{n}")))
        for (aa,bb) in imp:
            formulas.append(z3.Implies(z3.Bool(f"v{aa}"), z3.Bool(f"v{bb}")))

        sat_formula = z3.And(formulas)

        
        # formulas = []
        # for m_index in range(len(self.models)):
        #     formulas.append(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars))
        #     self.timer.check_time()
        # sat_formula = z3.And(formulas)
        # # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))
        
        solver.add(sat_formula)
        result = self.timer.solver_check(solver)
        if result == z3.unsat:
            solver.pop()
            return None
        elif result == z3.sat:
            #print(solver)
            #print(solver.model())
            solver.pop()
            with self.matrix_timer:
                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for x in vars:
                    concrete_models[x] = self.collapsed.get_concrete(x)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer, self.max_clauses)
                if matrix is None:
                    return None
                checker = z3.Solver()
                checker.add(sat_formula)
                for x, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
                    print(f"M{x} == {check(matrix, m)}")
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

class SeparatorReductionV1(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self.sig = sig
        self.sort_indices: Dict[str, int] = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models: List[Model] = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.prefixes = PrefixSolver(0, self.sort_indices)
        self.cached_solver_depth = -1
        self._setup_solver_for_depth()

    def add_model(self, model: Model) -> int:
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        v = self._construct_instantiation(model, model_i, [], self.cached_solver_depth, self.cached_solver)
        self.cached_solver.add(v if model.label.startswith("+") else z3.Not(v))
        return model_i

    def _all_quantifiers(self) -> List[Quantifier]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant: Quantifier, depth: int) -> z3.ExprRef:
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _construct_instantiation(self, model: Model, model_i: int, instantiation: List[int], depth: int, solver: z3.Solver) -> z3.ExprRef:
        current_depth = len(instantiation)
        if current_depth == depth:
            return z3.Bool(f"M{self.collapsed.get(model_i, instantiation)}")
        else:
            var = z3.Bool(f"v{self.next_var}")
            self.next_var += 1
            for sort in sorted(self.sort_indices.keys()):
                subvars = [self._construct_instantiation(model, model_i, instantiation + [elem], depth, solver)
                            for elem in model.elems_of_sort[sort]]
                for is_forall in [True, False]:
                    solver.add(z3.Implies(self._var_for_quantifier((is_forall, sort), current_depth),
                                      var == (z3.And(subvars) if is_forall else z3.Or(subvars))))
            return var

    def _setup_solver_for_depth(self) -> None:
        depth = self.prefixes.depth
        if self.cached_solver_depth != depth:
            print(f"rebuilding solver for depth {depth}")
            self.cached_solver = z3.Solver()
            self.cached_solver.set("unsat_core", True, "core.minimize", False)
            self.next_var = 0
            for model_i, model in enumerate(self.models):
                v = self._construct_instantiation(model, model_i, [], depth, self.cached_solver)
                self.cached_solver.add(v if model.label.startswith("+") else z3.Not(v))
                print(f"finished model {model_i}")
                self.timer.check_time()
            for d in range(depth):
                self.cached_solver.add(
                           z3.PbEq([(self._var_for_quantifier(q, d), 1) for q in self._all_quantifiers()], 1))
            self.cached_solver_depth = depth

            print(f"built solver using {self.next_var} variables")

    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 max_depth: int = 1000000, max_clauses: int = 10, conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        self.timer = timer
        self._setup_solver_for_depth()
        while True:
            p = self.prefixes.get()
            if p is None:
                if self.prefixes.depth == max_depth:
                    return None
                self.prefixes = PrefixSolver(self.prefixes.depth+1, self.sort_indices)
                self._setup_solver_for_depth()
                p = self.prefixes.get()
            assert p is not None
            if not self.quiet:
                print ("Prefix:", " ".join([("∀" if F else "∃") + sort + "." for (F, sort) in p]))
            c = self._check_prefix_build_matrix(p, matrix_timer)
            if c is not None:
                return c

    def _filter_prefix(self, p: List[Quantifier]) -> bool:
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            assert self.ae_edges is not None
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True

    def _check_prefix_build_matrix(self, prefix: List[Quantifier], matrix_timer: Timer) -> Optional[Formula]:
        start = time.time()
        result = self.timer.solver_check(self.cached_solver, *[self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])

        if result == z3.unsat:
            print("unsat core")
            core = self.cached_solver.unsat_core()
            print(result, f"{time.time() - start:0.3f}")
            prefix_core_vars = []
            for a in core:
                name = a.decl().name()
                match = re.match("^([AE])_(\d+)_(\d+)$", name)
                if match:
                    prefix_core_vars.append(z3.Bool(name))
            print(f"Core size {len(prefix)}-{len(prefix_core_vars)}")
            self.prefixes.add(prefix_core_vars)
            return None
        elif result == z3.sat:
            print(result, f"{time.time() - start:0.3f}")
            with matrix_timer:
                vars = VarSet()
                formulas = []
                for m_index in range(len(self.models)):
                    formulas.append(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars))
                    self.timer.check_time()
                sat_formula = z3.And(formulas)

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for x in vars:
                    concrete_models[x] = self.collapsed.get_concrete(x)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
                if matrix is None:
                    raise RuntimeError("Matrix with desired number of clauses not found")
                checker = z3.Solver()
                checker.add(sat_formula)
                for x, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

class InstantiationNode(object):
    __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i', 'expanded_sorts']
    def __init__(self, index: int, instantiation: List[int], fo_type: int, model_i: int):
        self.index = index
        self.instantiation = instantiation
        self.children: List[InstantiationNode] = []
        self.fo_type = fo_type
        self.model_i = model_i
        self.expanded_sorts = 0

class SortNode(object):
    def __init__(self) -> None:
        self.children: Dict[str, 'SortNode'] = {}
        self.fo_types: Set[int] = set()
    def get_child(self, sort: str) -> 'SortNode':
        if sort not in self.children:
            self.children[sort] = SortNode()
        return self.children[sort]
    def types_for(self, sorts: Sequence[Optional[str]], sorts_i: int = 0) -> Set[int]:
        if len(sorts) == sorts_i:
            return self.fo_types
        else:
            s = sorts[sorts_i]
            if s is None:
                return self.fo_types.union(*[c.types_for(sorts, sorts_i + 1) for c in self.children.values()])
            if s not in self.children:
                return self.fo_types
            return self.fo_types | self.get_child(s).types_for(sorts, sorts_i + 1)
    def add_type(self, sorts: List[str], fo_type: int, sorts_i: int = 0) -> None:
        if len(sorts) == sorts_i:
            self.fo_types.add(fo_type)
        else:
            self.get_child(sorts[sorts_i]).add_type(sorts, fo_type, sorts_i + 1)

class SeparatorReductionV2(Separator):    
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self.sig = sig
        self.sort_indices: Dict[str, int] = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models: List[Model] = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.model_nodes: List[InstantiationNode] = []
        self.expanded_fo_types: Set[int] = set()
        self.fo_type_depths: Dict[int,int] = {}
        self.nodes_by_index: Dict[int, InstantiationNode] = {}
        self.next_node_index = 0
        self.prefixes = PrefixSolver(0, self.sort_indices)
        # self.prefix_index = 0
        self.nodes_by_type: DefaultDict[int, List[InstantiationNode]] = defaultdict(list)
        self.sort_root = SortNode()
        self.solver = z3.Solver()
        self.solver.set("unsat_core", True, "core.minimize", False)
        self.solver_depth_assertions = 0

    def _new_node_index(self) -> int:
        v = self.next_node_index
        self.next_node_index += 1
        return v
    def add_model(self, model: Model) -> int:
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        new_root = InstantiationNode(self._new_node_index(), [], self.collapsed.get(model_i, []), model_i)
        self._register_node(new_root)
        self.model_nodes.append(new_root)
        self._expand_existing_fo_types(new_root)
        v = z3.Bool(f"v{new_root.index}")
        self.solver.add(v if model.label.startswith("+") else z3.Not(v))
        return model_i

    def _all_quantifiers(self) -> List[Quantifier]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant: Quantifier, depth: int) -> z3.ExprRef:
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _expand_node(self, node: InstantiationNode) -> None:
        model = self.models[node.model_i]
        for elem in range(len(model.elems)):
            es = node.instantiation + [elem]
            # print(es)
            fo_type = self.collapsed.get(node.model_i, es)
            child = InstantiationNode(self._new_node_index(), es, fo_type, node.model_i)
            node.children.append(child)
            self._register_node(child)

    def _register_node(self, node: InstantiationNode) -> None:
        self.nodes_by_type[node.fo_type].append(node)
        self.nodes_by_index[node.index] = node
        self.solver.add(z3.Implies(z3.Bool(f"T{node.fo_type}"), z3.Bool(f"M{node.fo_type}") == z3.Bool(f"v{node.index}")))
        if node.fo_type not in self.fo_type_depths:
            self.fo_type_depths[node.fo_type] = len(node.instantiation)
            m = self.models[node.model_i]
            self.sort_root.add_type([m.sorts[x] for x in node.instantiation], node.fo_type)
            self.solver.add(z3.Implies(z3.Bool(f"D{len(node.instantiation)}"), z3.Bool(f"T{node.fo_type}")))



    def _define_node(self, node: InstantiationNode) -> None:
        model = self.models[node.model_i]
        var = z3.Bool(f"v{node.index}")
        for sort in sorted(self.sort_indices.keys()):
            subvars = [z3.Bool(f"v{c.index}") for c in node.children if model.sorts[c.instantiation[-1]] == sort]
            for is_forall in [True, False]:
                self.solver.add(z3.Implies(self._var_for_quantifier((is_forall, sort), len(node.instantiation)),
                                      var == (z3.And(subvars) if is_forall else z3.Or(subvars))))

    def _expand_existing_fo_types(self, node: InstantiationNode) -> None:
        if node.fo_type not in self.expanded_fo_types:
            return
        assert len(node.children) == 0
        self._expand_node(node)
        self._define_node(node)

        for c in node.children:
            self._expand_existing_fo_types(c)
    def _expand_nodes_for_fo_type(self, fo_type: int) -> None:
        for node in self.nodes_by_type[fo_type]:
            self._expand_node(node)
            self._define_node(node)
        self.expanded_fo_types.add(fo_type)

    def _ensure_quantifier_definitions(self, max_depth: int) -> None:
        for d in range(self.solver_depth_assertions, max_depth):
            self.solver.add(z3.PbEq([(self._var_for_quantifier(q, d), 1) for q in self._all_quantifiers()], 1))
        self.solver_depth_assertions = max(self.solver_depth_assertions, max_depth)

    def separate(self,
            pos: Collection[int],
            neg: Collection[int],
            imp: Collection[Tuple[int, int]],
            max_depth: int = 1000000, max_clauses: int = 10, conjuncts: int = 1,
            timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        self.timer = timer
        self._ensure_quantifier_definitions(self.prefixes.depth)

        while True:
            p = self.prefixes.get()
            if p is None:
                if self.prefixes.depth == max_depth:
                    return None
                self.prefixes = PrefixSolver(self.prefixes.depth + 1, self.sort_indices)
                self._ensure_quantifier_definitions(self.prefixes.depth)
                p = self.prefixes.get()
            assert p is not None
            if not self.quiet:
                print("Prefix:", " ".join([("∀" if is_forall else "∃")+f"{sort}." for (is_forall, sort) in p]))
            c = self._check_prefix_build_matrix(p, matrix_timer)
            if c is not None:
                return c

    def _assert_equalities(self, sorts: Sequence[Optional[str]]) -> List[z3.ExprRef]:
        current_depth = len(sorts)
        a = []
        for fo_type in self.sort_root.types_for(sorts):
            if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < current_depth:
                a.append(z3.Bool(f"T{fo_type}"))
        return a

    def _print(self, *args: Any) -> None:
        if not self.quiet:
            print(*args)
    def _check_prefix_build_matrix(self, prefix: List[Quantifier], matrix_timer: Timer) -> Optional[Formula]:
        start = time.time()
        sorts_of_prefix = [s for (is_forall, s) in prefix]

        while True:
            # print("Attempting")
            assumptions = self._assert_equalities(sorts_of_prefix)
            assumptions.append(z3.Bool(f"D{len(prefix)}"))
            assumptions.extend([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])

            self._print("checking...")
            print(f"Used {len(assumptions)} assumptions")
            #print(self.solver)
            result = self.timer.solver_check(self.solver, *assumptions)

            if result == z3.unsat:
                self._print("constructing unsat core...")
                core = self.solver.unsat_core()

            if result == z3.sat:
                break
            elif result == z3.unsat:
                # if all FO types in the unsat core are at max depth, it is unsat
                # print("core:", core)
                possible_expansions = set()
                prefix_core_vars = []
                for a in core:
                    var = a.decl().name()
                    if var.startswith("T"):
                        fo_type = int(var[1:])
                        if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < len(prefix):
                            possible_expansions.add(fo_type)
                    elif re.match("^([AE])_(\d+)_(\d+)$", var):
                        prefix_core_vars.append(z3.Bool(var))
                if len(possible_expansions) == 0:
                    print("Generalizing prefix...")
                    #assumptions = self._assert_equalities(sorts_of_prefix)
                    # assumptions = self._assert_equalities([None] * len(prefix))
                    # assumptions.append(z3.Bool(f"D{len(prefix)}"))

                    final_core: List[z3.ExprRef] = []
                    initial_core = list(reversed(prefix_core_vars))
                    #initial_core = list(prefix_core_vars)
                    while len(initial_core) > 0:
                        print(final_core, [initial_core[0]], initial_core[1:])
                        assumptions = self._assert_equalities([s if False else None for i, s in enumerate(sorts_of_prefix)]) + [z3.Bool(f"D{len(prefix)}")]
                        print(len(assumptions))
                        r = self.timer.solver_check(self.solver, *(assumptions + final_core + initial_core[1:]))
                        if r == z3.sat:
                            final_core.append(initial_core[0])
                            #final_core.extend(initial_core)
                            #break
                            initial_core = initial_core[1:]
                        elif r == z3.unsat:
                            c = self.solver.unsat_core()
                            core_t_vars = [x.decl().name() for x in c if x.decl().name().startswith("T") ]
                            if len(core_t_vars) == 0:
                                # actual unsat result, we can drop the given term
                                initial_core = initial_core[1:]
                            if len(core_t_vars) < 10:
                                # one of the assumptions needs to have its node expanded.
                                # few enough to do this right now
                                for x in core_t_vars:
                                    self._expand_nodes_for_fo_type(int(x[1:]))
                            else:
                                print("couldn't generalize due to", len(core_t_vars), "unexpanded nodes")
                                final_core.extend(initial_core)
                                break


                    #print("Final core is", self.solver.unsat_core())
                    #for a in self.solver.assertions():
                    #    print(a)
                    print(f"Core size {len(prefix)} {len(final_core)} {len(prefix_core_vars)}")
                    print(f"Core depths {'+'.join(x.decl().name()[-1] for x in final_core)}")
                    print(final_core)
                    self.prefixes.add(final_core)
                    break
                else:
                    self._print("expanding", len(possible_expansions), "fo-types")
                    for t in possible_expansions:
                        if t not in self.expanded_fo_types:
                            self._expand_nodes_for_fo_type(t)
            else:
                assert False

        self._print(result, f"{time.time() - start:0.3f}",
                    f"nodes: {self.next_node_index}, fo_types: {self.collapsed.fo_type_count()}, expanded: {len(self.expanded_fo_types)}")
        self._print(f"|C| {len(self.sort_root.types_for([None]*len(prefix)))} {len(self.sort_root.types_for([None] * (max(0, len(prefix)-1))))}")

        if result == z3.unsat:
            return None
        elif result == z3.sat:
            with matrix_timer:
                vars = VarSet()
                formulas = []
                for m_index in range(len(self.models)):
                    formulas.append(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars))
                    self.timer.check_time()
                sat_formula = z3.And(formulas)
                # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models: Dict[int, Model] = {}
                for xx in vars:
                    concrete_models[xx] = self.collapsed.get_concrete(xx)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
                if matrix is None:
                    raise RuntimeError("Matrix with desired number of clauses not found")
                checker = z3.Solver()
                checker.add(sat_formula)
                for xx, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(xx)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(xx))))
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

class GeneralizedSeparator(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self.sig = sig
        self.sort_indices: Dict[str, int] = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models: List[Model] = []
        self.quiet = quiet
        self.logic = logic
        if logic == "epr":
            assert False # EPR unsupported
        self.model_nodes: List[InstantiationNode] = []
        self.expanded_fo_types: Set[int] = set()
        self.fo_type_depths: Dict[int, int] = {}
        self.nodes_by_index: Dict[int, InstantiationNode] = {}
        self.next_node_index = 0
        self.prefixes = PrefixSolver(0, self.sort_indices, logic=self.logic)
        # self.prefix_index = 0
        self.nodes_by_type: DefaultDict[int, List[InstantiationNode]] = defaultdict(list)
        self.sort_root = SortNode()
        self._cached_pos: Dict[int, int] = {}
        self._cached_neg: Dict[int, int] = {}
        self._cached_imp: Dict[Tuple[int, int], int] = {}
        
        self.solver = z3.Solver()
        self.solver.set("unsat_core", True, "core.minimize", False)
        self.solver_depth_assertions = 0

    def _new_node_index(self) -> int:
        v = self.next_node_index
        self.next_node_index += 1
        return v
    def add_model(self, model: Model) -> int:
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        new_root = InstantiationNode(self._new_node_index(), [], self.collapsed.get(model_i, []), model_i)
        self._register_node(new_root)
        self.model_nodes.append(new_root)
        self._expand_existing_fo_types(new_root)
        return new_root.index

    def _var_for_quantifier(self, quant: Quantifier, depth: int) -> z3.ExprRef:
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _expand_node(self, node: InstantiationNode) -> None:
        model = self.models[node.model_i]
        for elem in range(len(model.elems)):
            es = node.instantiation + [elem]
            # print(es)
            fo_type = self.collapsed.get(node.model_i, es)
            child = InstantiationNode(self._new_node_index(), es, fo_type, node.model_i)
            node.children.append(child)
            self._register_node(child)

    def _register_node(self, node: InstantiationNode) -> None:
        self.nodes_by_type[node.fo_type].append(node)
        self.nodes_by_index[node.index] = node
        self.solver.add(z3.Implies(z3.Bool(f"T{node.fo_type}"), z3.Bool(f"M{node.fo_type}") == z3.Bool(f"v{node.index}")))
        if node.fo_type not in self.fo_type_depths:
            self.fo_type_depths[node.fo_type] = len(node.instantiation)
            m = self.models[node.model_i]
            self.sort_root.add_type([m.sorts[x] for x in node.instantiation], node.fo_type)
            self.solver.add(z3.Implies(z3.Bool(f"D{len(node.instantiation)}"), z3.Bool(f"T{node.fo_type}")))



    def _define_node(self, node: InstantiationNode) -> None:
        model = self.models[node.model_i]
        var = z3.Bool(f"v{node.index}")
        for sort in sorted(self.sort_indices.keys()):
            subvars = [z3.Bool(f"v{c.index}") for c in node.children if model.sorts[c.instantiation[-1]] == sort]
            for is_forall in [True, False]:
                self.solver.add(z3.Implies(self._var_for_quantifier((is_forall, sort), len(node.instantiation)),
                                      var == (z3.And(subvars) if is_forall else z3.Or(subvars))))

    def _expand_existing_fo_types(self, node: InstantiationNode) -> None:
        if node.fo_type not in self.expanded_fo_types:
            return
        assert len(node.children) == 0
        self._expand_node(node)
        self._define_node(node)

        for c in node.children:
            self._expand_existing_fo_types(c)
    def _expand_nodes_for_fo_type(self, fo_type: int) -> None:
        for node in self.nodes_by_type[fo_type]:
            self._expand_node(node)
            self._define_node(node)
        self.expanded_fo_types.add(fo_type)

    def _ensure_quantifier_definitions(self, max_depth: int) -> None:
        all_quantifiers = [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
        for d in range(self.solver_depth_assertions, max_depth):
            self.solver.add(z3.PbEq([(self._var_for_quantifier(q, d), 1) for q in all_quantifiers], 1))
        self.solver_depth_assertions = max(self.solver_depth_assertions, max_depth)

    def separate(self,
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
                 max_depth: int = 1000000, max_clauses: int = 10, conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer(),
                 matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        self.prefixes = PrefixSolver(0, self.sort_indices, logic=self.logic)

        self.timer = timer

        # self.solver_depth_assertions = 0
        # self._ensure_quantifier_definitions(self.prefixes.depth)

        # add constraints
        constraints = []
        for po in pos:
            if po not in self._cached_pos:
                i = len(self._cached_pos)
                self.solver.add(z3.Implies(z3.Bool(f"CP{i}"), z3.Bool(f"v{po}")))
                self._cached_pos[po] = i
            constraints.append(z3.Bool(f"CP{self._cached_pos[po]}"))
        for n in neg:
            if n not in self._cached_neg:
                i = len(self._cached_neg)
                self.solver.add(z3.Implies(z3.Bool(f"CN{i}"), z3.Not(z3.Bool(f"v{n}"))))
                self._cached_neg[n] = i
            constraints.append(z3.Bool(f"CN{self._cached_neg[n]}"))
        for (a,b) in imp:
            if (a,b) not in self._cached_imp:
                i = len(self._cached_imp)
                self.solver.add(z3.Implies(z3.Bool(f"CI{i}"), z3.Implies(z3.Bool(f"v{a}"), z3.Bool(f"v{b}"))))
                self._cached_imp[(a,b)] = i
            constraints.append(z3.Bool(f"CI{self._cached_imp[(a,b)]}"))

        while True:
            p = self.prefixes.get()
            if p is None:
                if self.prefixes.depth == max_depth:
                    return None
                self.prefixes = PrefixSolver(self.prefixes.depth + 1, self.sort_indices, logic=self.logic)
                self._ensure_quantifier_definitions(self.prefixes.depth)
                p = self.prefixes.get()
            assert p is not None
            if True or not prefix_is_redundant(p):
                if not self.quiet:
                    print("Prefix:", " ".join([("∀" if is_forall else "∃")+f"{sort}." for (is_forall, sort) in p]))
                c = self._check_prefix_build_matrix(p, matrix_timer, constraints, pos, neg, imp)
                if c is not None:
                    return c


    def _assert_equalities(self, sorts: Sequence[Optional[str]]) -> List[z3.ExprRef]:
        current_depth = len(sorts)
        a = []
        for fo_type in self.sort_root.types_for(sorts):
            if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < current_depth:
                a.append(z3.Bool(f"T{fo_type}"))
        return a

    def _print(self, *args: Any) -> None:
        if not self.quiet:
            print(*args)
    def _check_prefix_build_matrix(self, prefix: List[Quantifier], matrix_timer: Timer, constraints: List[z3.ExprRef], pos: Collection[int], neg: Collection[int], imp: Collection[Tuple[int, int]]) -> Optional[Formula]:
        start = time.time()
        sorts_of_prefix = [s for (is_forall, s) in prefix]

        while True:
            # print("Attempting")
            assumptions = self._assert_equalities(sorts_of_prefix)
            assumptions.append(z3.Bool(f"D{len(prefix)}"))
            assumptions.extend([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
            assumptions.extend(constraints)

            self._print("checking...")
            self._print(f"Used {len(assumptions)} assumptions")
            result = self.timer.solver_check(self.solver, *assumptions)

            if result == z3.unsat:
                self._print("constructing unsat core...")
                core = self.solver.unsat_core()

            # self.solver.pop()

            if result == z3.sat:
                # print("Problem (main solver):", self.solver)
                # print(self.solver.model())
                break
            elif result == z3.unsat:
                # if all FO types in the unsat core are at max depth, it is unsat
                # print("core:", core)
                possible_expansions = set()
                prefix_core_vars = []
                for a in core:
                    var = a.decl().name()
                    if var.startswith("T"):
                        fo_type = int(var[1:])
                        if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < len(prefix):
                            possible_expansions.add(fo_type)
                    elif re.match("^([AE])_(\d+)_(\d+)$", var):
                        prefix_core_vars.append(z3.Bool(var))
                if len(possible_expansions) == 0:
                    self._print("Generalizing prefix...")
                    #assumptions = self._assert_equalities(sorts_of_prefix)
                    # assumptions = self._assert_equalities([None] * len(prefix))
                    # assumptions.append(z3.Bool(f"D{len(prefix)}"))

                    final_core: List[z3.ExprRef] = []
                    initial_core = list(reversed(prefix_core_vars))
                    #initial_core = list(prefix_core_vars)
                    while len(initial_core) > 0:
                        self._print(final_core, [initial_core[0]], initial_core[1:])
                        assumptions = self._assert_equalities([s if False else None for i, s in enumerate(sorts_of_prefix)]) + [z3.Bool(f"D{len(prefix)}")] + constraints
                        r = self.timer.solver_check(self.solver, *(assumptions + final_core + initial_core[1:]))
                        if r == z3.sat:
                            final_core.append(initial_core[0])
                            #final_core.extend(initial_core)
                            #break
                            initial_core = initial_core[1:]
                        elif r == z3.unsat:
                            c = self.solver.unsat_core()
                            core_t_vars = [x.decl().name() for x in c if x.decl().name().startswith("T") ]
                            if len(core_t_vars) == 0:
                                # actual unsat result, we can drop the given term
                                initial_core = initial_core[1:]
                            if len(core_t_vars) < 10:
                                # one of the assumptions needs to have its node expanded.
                                # few enough to do this right now
                                for x in core_t_vars:
                                    self._expand_nodes_for_fo_type(int(x[1:]))
                            else:
                                self._print("couldn't generalize due to", len(core_t_vars), "unexpanded nodes")
                                final_core.extend(initial_core)
                                break


                    #print("Final core is", self.solver.unsat_core())
                    #for a in self.solver.assertions():
                    #    print(a)
                    self._print(f"Core size {len(prefix)} {len(final_core)} {len(prefix_core_vars)}")
                    # print(f"Core depths {'+'.join(x.decl().name()[-1] for x in final_core)}")
                    self._print(final_core)
                    self.prefixes.add(final_core)
                    break
                else:
                    self._print("expanding",  len(possible_expansions), "fo-types")
                    for t in possible_expansions:
                        if t not in self.expanded_fo_types:
                            self._expand_nodes_for_fo_type(t)
            else:
                assert False

        self._print(result, f"{time.time() - start:0.3f}",
                    f"nodes: {self.next_node_index}, fo_types: {self.collapsed.fo_type_count()}, expanded: {len(self.expanded_fo_types)}")
        self._print(f"|C| {len(self.sort_root.types_for([None]*len(prefix)))} {len(self.sort_root.types_for([None] * (max(0, len(prefix)-1))))}")
        # print("(result == z3.sat)", (result == z3.sat))
        # print("check_prefix", check_prefix(self.models, prefix, self.sig, self.collapsed, z3.Solver()))
        # assert ((result == z3.sat) == check_prefix(self.models, prefix, self.sig, self.collapsed, z3.Solver()))

        if result == z3.unsat:
            return None
        elif result == z3.sat:
            with matrix_timer:
                vars = VarSet()
                formulas = []
                for m_index in range(len(self.models)):
                    i = self.model_nodes[m_index].index
                    formulas.append(z3.Bool(f"v{i}") == z3.Not(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars)))
                    self.timer.check_time()

                for po in pos:
                    formulas.append(z3.Bool(f"v{po}"))
                for n in neg:
                    formulas.append(z3.Not(z3.Bool(f"v{n}")))
                for (aa,bb) in imp:
                    formulas.append(z3.Implies(z3.Bool(f"v{aa}"), z3.Bool(f"v{bb}")))

                sat_formula = z3.And(formulas)
                # print("SAT Formula", sat_formula)
                # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for xx in vars:
                    concrete_models[xx] = self.collapsed.get_concrete(xx)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
                if matrix is None:
                    raise RuntimeError("Matrix with desired number of clauses not found")
                checker = z3.Solver()
                checker.add(sat_formula)
                for xx, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(xx)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(xx))))
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                # print("Checker model", checker.model())
                # print("Sat formula was", sat_formula)
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"


def atoms_of(sig: Signature, additional_vars: Sequence[Tuple[str, str]]) -> Iterable[Formula]:
    terms_by_sort: Dict[str, List[Term]] = dict([(s,[]) for s in sig.sorts])

    vars_used: Set[str] = set()
    # deeper variables should shadow shallower ones and constants
    for v, sort in reversed(additional_vars):
        if v not in vars_used:
            terms_by_sort[sort].append(Var(v))
            vars_used.add(v)
    for c, sort in sorted(sig.constants.items()):
        if c not in vars_used:
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
            if a < b:
                yield (Equal(a, b))

def prefix_var_names(sig: Signature, prefix: Iterable[int]) -> Sequence[str]:
    var_prefix = "x_"
    while any(c.startswith(var_prefix) for c in sig.all_names()):
        var_prefix = "_" + var_prefix
    next: DefaultDict[int, int] = defaultdict(int)
    ret = []
    for sort in prefix:
        n = next[sort]
        next[sort] += 1
        ret.append(f"{var_prefix}{sort}_{n}")
    return ret

class Constraint(object):
    pass
class Pos(Constraint):
    def __init__(self, i: int):
        self.i = i
class Neg(Constraint):
    def __init__(self, i: int):
        self.i = i
class Imp(Constraint):
    def __init__(self, i: int, j: int):
        self.i = i
        self.j = j
        

class HybridSeparator(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self._sig = sig
        self._logic = logic
        self.solver = z3.Solver()
        self._highest_depth_var = 0
        self._highest_prefix: DefaultDict[int, int] = defaultdict(int)

        self._models: List[Model] = []
        self._node_roots: Dict[Tuple[int,int], InstantiationNode] = {}
        self._nodes_by_index: Dict[int, InstantiationNode] = {}
        self._next_node_index = 0

        self._collapse_cache = CollapseCache(sig)
        self._fo_types_defined: Set[int] = set()

        self._atoms: List[Formula] = []
        self._atoms_cache: Dict[Formula, int] = {}
        self._atoms_by_sort: Dict[Tuple[int, ...], List[int]] = {}

        self._atoms_defined: Set[Tuple[int, int, int]] = set()

    def add_model(self, model:Model) -> int:
        l = len(self._models)
        self._models.append(model)
        self._collapse_cache.add_model(model)
        return l

    def _depth_var_assertion(self, conjunct: int, depth:int) -> None:
        while self._highest_depth_var < depth:
            d = self._highest_depth_var
            self.solver.add(z3.Implies(z3.Bool(f"D_{conjunct}_{d+1}"),z3.Bool(f"Dg_{conjunct}_{d}")))
            self.solver.add(z3.Implies(z3.Bool(f"Dg_{conjunct}_{d+1}"),z3.Bool(f"Dg_{conjunct}_{d}")))
            self._highest_depth_var += 1
    def _depth_var(self, conjunct: int, depth: int) -> z3.ExprRef:
        self._depth_var_assertion(conjunct, depth)
        return z3.Bool(f"D_{conjunct}_{depth}")
    def _depth_greater_var(self, conjunct: int, depth: int) -> z3.ExprRef:
        self._depth_var_assertion(conjunct, depth)
        return z3.Bool(f"Dg_{conjunct}_{depth}")

    def _prefix_sort_var(self, conjunct: int, sort: int, depth: int) -> z3.ExprRef:
        return z3.Bool(f"Q_{conjunct}_{sort}_{depth}")
    def _prefix_quant_var(self, conjunct: int, depth: int) -> z3.ExprRef:
        return z3.Bool(f"AE_{conjunct}_{depth}")

    def _prefix_var_definition(self, conjunct: int, depth: int) -> None:
        n_sorts = len(self._sig.sort_names)
        for d in range(self._highest_prefix[conjunct], depth):
            self.solver.add(z3.PbEq([(self._prefix_sort_var(conjunct, q, d), 1) for q in range(n_sorts)], 1))
            if 0 < d:
                for i,j in itertools.combinations(reversed(range(n_sorts)), 2):
                    A_i_dm1 = z3.And(self._prefix_sort_var(conjunct, i, d-1),  self._prefix_quant_var(conjunct, d-1))
                    A_j_d = z3.And(self._prefix_sort_var(conjunct, j, d), self._prefix_quant_var(conjunct, d))
                    E_i_dm1 = z3.And(self._prefix_sort_var(conjunct, i, d-1), z3.Not(self._prefix_quant_var(conjunct, d-1)))
                    E_j_d = z3.And(self._prefix_sort_var(conjunct, j, d), z3.Not(self._prefix_quant_var(conjunct, d)))
                    self.solver.add(z3.Not(z3.And(A_j_d, A_i_dm1)))
                    self.solver.add(z3.Not(z3.And(E_j_d, E_i_dm1)))
            if self._logic == "universal":
                self.solver.add(self._prefix_quant_var(conjunct, d))
                
            # for sort in range(len(self._sig.sort_names)):
                # self.solver.add_soft(z3.Not(self._prefix_var(conjunct, (False, sort), d)))
                # TODO: add other logic restrictions
        self._highest_prefix[conjunct] = max(self._highest_prefix[conjunct], depth)

    def _new_node_index(self) -> int:
        r = self._next_node_index
        self._next_node_index += 1
        return r
    def _root_var(self, model: int, conjunct: int) -> z3.ExprRef:
        if (model, conjunct) not in self._node_roots:
            new_root = InstantiationNode(self._new_node_index(), [], self._collapse_cache.get(model, []), model)
            self._nodes_by_index[new_root.index] = new_root
            var = z3.Bool(f"v_{new_root.index}")
            self.solver.add(z3.Implies(self._depth_var(conjunct, 0), var == self._fo_type_var(new_root.fo_type)))
            self.solver.add(z3.Implies(self._depth_greater_var(conjunct, 0),
                                       z3.Implies(self._fo_type_var(new_root.fo_type), var)))
            self._node_roots[(model, conjunct)] = new_root
        return z3.Bool(f"v_{self._node_roots[(model, conjunct)].index}")
    def _expand_node(self, conjunct:int, node: InstantiationNode, sort: str) -> None:
        m_i = node.model_i
        model = self._models[m_i]
        if any(model.sorts[c.instantiation[-1]] == sort for c in node.children):
            return # don't expand twice
        new_children = []
        for e in model.elems_of_sort[sort]:
            ins = node.instantiation + [e]
            c = InstantiationNode(self._new_node_index(), ins, self._collapse_cache.get(m_i, ins), m_i)
            # print(f"made new node v_{c.index}. fo-type is {c.fo_type}")
            self._nodes_by_index[c.index] = c
            var = z3.Bool(f"v_{c.index}")
            d = len(c.instantiation)
            self.solver.add(z3.Implies(self._depth_var(conjunct, d), var == self._fo_type_var(c.fo_type)))
            self.solver.add(z3.Implies(self._depth_greater_var(conjunct, d),
                                       z3.Implies(self._fo_type_var(c.fo_type), var)))
            new_children.append(c)
            node.children.append(c)
        d = len(node.instantiation)
        var = z3.Bool(f"v_{node.index}")
        sort_index = self._sig.sort_indices[sort]
        self.solver.add(
            z3.Implies(z3.And(self._depth_greater_var(conjunct, d), self._prefix_quant_var(conjunct, d), self._prefix_sort_var(conjunct, sort_index, d)),
                       var == z3.And([z3.Bool(f"v_{c.index}") for c in new_children])))
        self.solver.add(
            z3.Implies(z3.And(self._depth_greater_var(conjunct, d), z3.Not(self._prefix_quant_var(conjunct, d)), self._prefix_sort_var(conjunct, sort_index, d)),
                       var == z3.Or([z3.Bool(f"v_{c.index}") for c in new_children])))

    def _literal_var(self, conjunct: int, clause: int, atom: int, polarity: bool) -> z3.ExprRef:
        i = (conjunct, clause, atom)
        if i not in self._atoms_defined:
            self.solver.add(z3.Or(z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1}")),
                                  z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{0}"))))
            # self.solver.add_soft(z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1}")))
            # self.solver.add_soft(z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{0}")))
            self._atoms_defined.add(i)
        return z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1 if polarity else 0}")
    
    def _atom_id(self, a: Formula) -> int:
        if a not in self._atoms_cache:
            i = len(self._atoms)
            self._atoms.append(a)
            self._atoms_cache[a] = i
        return self._atoms_cache[a]
    def _all_atoms(self, sort_list: Iterable[int]) -> List[int]:
        key = tuple(sort_list)
        if key not in self._atoms_by_sort:
            atms = list(atoms_of(self._sig, list(zip(prefix_var_names(self._sig, sort_list), (self._sig.sort_names[i] for i in sort_list)))))
            self._atoms_by_sort[key] = [self._atom_id(a) for a in atms]
        return self._atoms_by_sort[key]
    
    def _fo_type_var(self, fo_type: int) -> z3.ExprRef:
        if fo_type not in self._fo_types_defined:
            atoms_with_polarity = []
            (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
            model = self._models[model_i]
            sort_list = [self._sig.sort_indices[model.sorts[i]] for i in assignment]
            extra_vars = {v: e for v,e in zip(prefix_var_names(self._sig, sort_list), assignment)}
            
            for i, a in enumerate(self._all_atoms(sort_list)):
                polarity = check(self._atoms[a], model, extra_vars)
                atoms_with_polarity.append((a, polarity))
            
            self.solver.add(z3.Bool(f"M_{fo_type}") ==
                z3.And([z3.Or([self._literal_var(0, cl, a, p) for (a,p) in atoms_with_polarity]) for cl in range(1)]))

            self._fo_types_defined.add(fo_type)
        return z3.Bool(f"M_{fo_type}")

    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 max_depth: int = 0,
                 max_clauses: int = 1,
                 max_conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        for depth in range(max_depth+1):
            for clauses in range(1, max_clauses+1):
                r = self.separate_exact(pos, neg, imp, depth, clauses, conjuncts = 1, timer = timer)
                if r is not None:
                    return r
        return None
    def separate_exact(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 depth: int = 0,
                 clauses: int = 1,
                 conjuncts: int = 1,
                 timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        assert conjuncts == 1 # only support one formula for now

        assumptions: List[z3.ExprRef] = []
        assumptions.append(self._depth_var(0, depth))
        self._prefix_var_definition(0, depth)
        for positive_model in pos:
            assumptions.append(self._root_var(positive_model, 0))
        for negative_model in neg:
            assumptions.append(z3.Not(self._root_var(negative_model, 0)))
        for (a_model, b_model) in imp:
            assumptions.append(z3.Implies(self._root_var(a_model, 0), self._root_var(b_model, 0)))

        constraints: List[Constraint] = [Pos(x) for x in pos]
        constraints.extend(Neg(y) for y in neg)
        constraints.extend(Imp(a,b) for (a,b) in imp)

        prefix_assumptions: List[z3.ExprRef] = []
        
        while True:
            print(f"Separating depth {depth} clauses {clauses}")
            # print(assumptions)
            # print(self.solver.assertions())

            res = timer.solver_check(self.solver, *(assumptions + prefix_assumptions))
            if res == z3.unsat:
                if len(prefix_assumptions) == 0:
                    print("UNSAT")
                    # print("assumptions", z3.And(assumptions).to_smt2())
                    # self.solver.push()
                    # self.solver.add(z3.And(assumptions))
                    # print("solver\n\n\n", self.solver.to_smt2())
                    # self.solver.pop()
                    # for a_i, atm in enumerate(self._atoms):
                    #     print(";", self._literal_var(0, 0, a_i, True), atm)
                    # if depth == 1:
                    #     (model_i, inst) = self._collapse_cache.get_example(8)
                    #     model = self._models[model_i]
                    #     print(model)
                    #     print(model.names[inst[0]])
                        
                    # because assumptions does not include any v_i, if we get unsat here we know there is no separator
                    return None
                else:
                    print("Prefix assumption was not satisfiable")
                    prefix_assumptions = []
            elif res == z3.sat:
                m = self.solver.model()
                fix_formula_assumptions = []
                prefix = []
                all_quantifiers = [(f, sort) for f in [True, False] for sort in range(len(self._sig.sort_names))]
                for d in range(depth):
                    for q in range(len(self._sig.sort_names)):
                        if z3.is_true(m[self._prefix_sort_var(0, q, d)]):
                            is_forall = z3.is_true(m[self._prefix_quant_var(0, d)])
                            prefix.append((is_forall, q))
                            fix_formula_assumptions.append(self._prefix_sort_var(0, q, d))
                            fix_formula_assumptions.append(self._prefix_quant_var(0, d) if is_forall \
                                                           else z3.Not(self._prefix_quant_var(0, d)))
                            break
                assert(len(prefix) == depth)
                sort_list = [q[1] for q in prefix]
                prefix_quantifiers = [(f, self._sig.sort_names[s]) for (f,s) in prefix]
                atom_possiblities = self._all_atoms(sort_list)
                matrix_list: List[List[Formula]] = []
                for cl in range(clauses):
                    matrix_list.append([])
                    for a in atom_possiblities:
                        a_true, a_false = self._literal_var(0, cl, a, True), self._literal_var(0, cl, a, False)
                        m_a_true, m_a_false = z3.is_true(m[a_true]), z3.is_true(m[a_false])
                        fix_formula_assumptions.append(a_true if m_a_true else z3.Not(a_true))
                        fix_formula_assumptions.append(a_false if m_a_false else z3.Not(a_false))
                        if m_a_true:
                            matrix_list[-1].append(self._atoms[a])
                        elif m_a_false:
                            matrix_list[-1].append(Not(self._atoms[a]))
                matrix = And([Or(cl) for cl in matrix_list])
                prefix_vars = prefix_var_names(self._sig, sort_list)
                
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{sort}" \
                                           for name, (pol, sort) in zip(prefix_vars, prefix_quantifiers)]), "matrix", matrix)
                # print(prefix_vars)

                def check_node(n: InstantiationNode, model:Model) -> Tuple[bool, Set[Tuple[int, bool]]]:
                    expected = z3.is_true(m[z3.Bool(f"v_{n.index}")]) # what the solver thinks the value is
                    if len(n.instantiation) == len(prefix_quantifiers):
                        truth = check_assignment(n.instantiation, model)
                        # print(f"v_{n.index} and M_{n.fo_type}")
                        assert truth == expected
                        return (truth, set())
                    else:
                        (is_forall, relevant_sort) = prefix_quantifiers[len(n.instantiation)]
                        children_of_sort = [c for c in n.children if model.sorts[c.instantiation[-1]] == relevant_sort]
                        if len(children_of_sort) == 0:
                            # node has not been expanded
                            truth = check_assignment(n.instantiation, model)
                            return (truth, set([(n.index, truth)]))
                        else:
                            # node has been expanded.
                            results = [check_node(c, model) for c in children_of_sort]
                            truth = all(r[0] for r in results) if is_forall else any(r[0] for r in results)
                            sub_vars: Set[Tuple[int, bool]] = set()
                            return (truth, sub_vars.union(*(r[1] for r in results)))
                
                def vars_of_t(t: Term) -> Iterator[str]:
                    if isinstance(t, Var):
                        yield t.var
                    elif isinstance(f, Func):
                        for c in f.args:
                            yield from vars_of_t(c)
                def vars_of(f: Formula) -> Iterator[str]:
                    if isinstance(f, Not):
                        yield from vars_of(f.f)
                    elif isinstance(f, Relation):
                        for t in f.args:
                            yield from vars_of_t(t)
                    elif isinstance(f, Equal):
                        for t in f.args:
                            yield from vars_of_t(t)
                    
                _matrix_value_cache: Dict[int, Optional[bool]] = {}
                def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
                    """Returns `True` or `False` if the matrix's value is determined on the FO type, or `None`
                    if it is not determined"""
                    if fo_type not in _matrix_value_cache:
                        (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                        model = self._models[model_i]
                        mapping = {v: e for v,e in zip(prefix_vars, assignment)}
                        all_clause_true = True
                        any_clause_unk = False
                        #print(mapping, matrix_list)
                        for clause in matrix_list:
                            cl_true = False
                            cl_unk = False
                            for atom in clause:
                                if all((v in mapping or v in model.constants) for v in vars_of(atom)):
                                    if check(atom, model, mapping):
                                        cl_true = True # atom is defined and is true
                                        break # clause is true, we don't need to keep looking
                                    else:
                                        pass # atom was defined but false so we can't conclude anything
                                else:
                                    cl_unk = True # atom was unknown
                            all_clause_true = all_clause_true and cl_true
                            any_clause_unk = any_clause_unk or cl_unk
                        if all_clause_true:
                            _matrix_value_cache[fo_type] = True
                        elif not any_clause_unk:
                            _matrix_value_cache[fo_type] = False
                        else:
                            _matrix_value_cache[fo_type] = None
                    return _matrix_value_cache[fo_type]

                def check_assignment(assignment: List[int], model: Model) -> bool:
                    if len(assignment) == len(prefix_quantifiers):
                        return check(matrix, model, {v: e for v,e in zip(prefix_vars, assignment)})
                    else:
                        (is_forall, sort) = prefix_quantifiers[len(assignment)]
                        univ = model.elems_of_sort[sort]
                        if is_forall:
                            return all(check_assignment(assignment+[e], model) for e in univ)
                        else:
                            return any(check_assignment(assignment+[e], model) for e in univ)


                def expand_to_prove(n: InstantiationNode, expected: bool) -> bool:
                    matrix_value = matrix_value_fo_type(n.fo_type)
                    if not expected and matrix_value is True:
                        return False # early out when we need false and the matrix has been determined already
                                     # this corresponds to the solver knowing that M_i => v_i.
                                     # we don't need to keep expanding to show the solver that this thing is
                                     # not true
                    
                    if len(n.instantiation) == depth:
                        assert matrix_value is not None
                        return expected is matrix_value

                    # we aren't at the base, but check the rest of the quantifiers and return if they match
                    if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                        return True

                    # the value of the formula and what the solver thinks are not the same
                    is_forall, sort = prefix[len(n.instantiation)]
                    if 0 == n.expanded_sorts & (1 << sort):
                        self._expand_node(0, n, self._sig.sort_names[sort])
                        n.expanded_sorts |= 1 << sort
                    for c in n.children:
                        if self._models[n.model_i].sorts[c.instantiation[-1]] == self._sig.sort_names[sort]:
                            expand_to_prove(c, expected)
                    return False

                if True:
                    _root_node_cache: Dict[int, bool] = {}
                    def root_node_value(n: int) -> bool:
                        if n not in _root_node_cache:
                            _root_node_cache[n] = check_assignment([], self._models[n])
                        return _root_node_cache[n]
                    def swap_to_front(c: int) -> None:
                        nonlocal constraints
                        x = constraints[c]
                        constraints = [x] + constraints[:c] + constraints[c+1:]

                    #print("checking constraints", constraints)
                    for c_i in range(len(constraints)):
                        c = constraints[c_i]
                        if isinstance(c, Pos):
                            if not root_node_value(c.i):
                                swap_to_front(c_i)
                                expand_to_prove(self._node_roots[(c.i, 0)], True)
                                break
                        elif isinstance(c, Neg):
                            if root_node_value(c.i):
                                swap_to_front(c_i)
                                expand_to_prove(self._node_roots[(c.i,0)], False)
                                break
                        elif isinstance(c, Imp):
                            if root_node_value(c.i) and not root_node_value(c.j):
                                swap_to_front(c_i)
                                expand_to_prove(self._node_roots[(c.i,0)], False)
                                expand_to_prove(self._node_roots[(c.j,0)], True)
                                break
                    else:
                        fff: Formula = matrix
                        for varname, (is_forall, sort) in reversed(list(zip(prefix_vars, prefix_quantifiers))):
                            fff = Forall(varname, sort, fff) if is_forall else Exists(varname, sort, fff)
                        return fff
                    print(f"expanded and now have {self._next_node_index} nodes of {sum(len(model.elems) ** d for model in self._models for d in range(depth+1))} possible")
                    prefix_assumptions = [self._prefix_sort_var(0, q, d) for (d,(i,q)) in enumerate(prefix)] + \
                                            [(self._prefix_quant_var(0, d) if i else z3.Not(self._prefix_quant_var(0,d))) for (d,(i,q)) in enumerate(prefix)]
                    continue

                    root_nodes_agree = True
                    for (model_i, conjunct), root in self._node_roots.items():
                        expected = z3.is_true(m[z3.Bool(f"v_{root.index}")])
                        if not expand_to_prove(root, expected):
                            print(f"expanded in model {model_i}")
                            root_nodes_agree = False
                            break
                    if root_nodes_agree:
                        f: Formula = matrix
                        for varname, (is_forall, sort) in reversed(list(zip(prefix_vars, prefix_quantifiers))):
                            f = Forall(varname, sort, f) if is_forall else Exists(varname, sort, f)
                        return f
                    else:
                        print(f"now have {self._next_node_index} nodes {sum(len(model.elems) ** d for model in self._models for d in range(depth+1))}")
                        prefix_assumptions = [self._prefix_sort_var(0, q, d) for (d,(i,q)) in enumerate(prefix)] + \
                                             [(self._prefix_quant_var(0, d) if i else z3.Not(self._prefix_quant_var(0,d))) for (d,(i,q)) in enumerate(prefix)]
                        continue


                root_nodes_agree = True
                nodes_to_add: Set[Tuple[int, bool]] = set()
                for (model_i, conjunct), root in self._node_roots.items():
                    (truth, additional_assumptions) = check_node(root, self._models[model_i])
                    nodes_to_add.update(additional_assumptions)
                    if (truth != z3.is_true(m[self._root_var(model_i, conjunct)])):
                        #print(f"!Failed in {model_i} {self._root_var(model_i, conjunct)}, {truth} != {z3.is_true(m[self._root_var(model_i, conjunct)])}")
                        root_nodes_agree = False
                
                new_assumptions = []
                for (v_i, polarity) in nodes_to_add:
                    new_assumptions.append(z3.Bool(f"v_{v_i}") if polarity else z3.Not(z3.Bool(f"v_{v_i}")))
                
                res = timer.solver_check(self.solver, *(assumptions + fix_formula_assumptions + new_assumptions))
                if res == z3.sat:
                    print("Formula was correct")
                    # if not root_nodes_agree: # this doesn't work with implication constraints
                    #     print(self.solver)
                    #     print("assumptions", assumptions)
                    #     print("fix_formula_assumptions", fix_formula_assumptions)
                    #     print("new_assumptions", new_assumptions)
                    #     print("nodes_to_add", nodes_to_add)
                    #     print("z3 model", m)
                    #     print(matrix)
                    #     assert False

                    # after all that, if we are still SAT then the formula is actually correct
                    ff: Formula = matrix
                    for varname, (is_forall, sort) in reversed(list(zip(prefix_vars, prefix_quantifiers))):
                        ff = Forall(varname, sort, ff) if is_forall else Exists(varname, sort, ff)
                    return ff
                elif res == z3.unsat:
                    core = self.solver.unsat_core()
                    print("Formula was incorrect")
                    #print(core)
                    def expand_expr(var: z3.ExprRef) -> None:
                        if not z3.is_const(var): return
                        varname = var.decl().name()
                        match = re.match("v_(\d+)", varname)
                        if match:
                            i = int(match.group(1))
                            node = self._nodes_by_index[i]
                            #print(f"expanding v_{i}")
                            self._expand_node(0, node, prefix_quantifiers[len(node.instantiation)][1])
                    for term in core:
                        if z3.is_not(term):
                            expand_expr(term.children()[0])
                        elif z3.is_implies(term):
                            expand_expr(term.children()[0])
                            expand_expr(term.children()[1])
                        else:
                            expand_expr(term)
                    print(f"now have {self._next_node_index} nodes {sum(len(model.elems) ** d for model in self._models for d in range(depth+1))}")
                    prefix_assumptions = [self._prefix_sort_var(0, q, d) for (d,(i,q)) in enumerate(prefix)] + \
                                         [(self._prefix_quant_var(0, d) if i else z3.Not(self._prefix_quant_var(0,d))) for (d,(i,q)) in enumerate(prefix)]
                else:
                    print(self.solver)
                    assert False # z3 should always return a result
            else:
                print(self.solver)
                assert False # z3 should always return a result
        
