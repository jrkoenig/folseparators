
from collections import defaultdict, Counter
import itertools, copy, time, sys, re, random
from typing import Tuple, TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, List, Dict, DefaultDict, Iterator, TypeVar, Any, Sequence

import z3

from .logic import Forall, Exists, Equal, Relation, And, Or, Not, Formula, Term, Var, Func, Model, Signature, rename_free_vars
from .check import check, resolve_term
from .matrix import infer_matrix, K_function_unrolling
from .timer import Timer, UnlimitedTimer

QuantifierStr = Tuple[bool, str]

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

def prefix_is_redundant(prefix: List[QuantifierStr]) -> bool:
    if len(prefix) == 0: return False
    for i in range(len(prefix) - 1):
        a,b = prefix[i], prefix[i+1]
        if a[0] == b[0] and a[1] > b[1]:
            return True
    return False

def build_prefix_formula(prefix: List[QuantifierStr], f: Formula, n: int = 0) -> Formula:
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

def formula_for_model(model_index: int, assignment: List[int], prefix_i: int, prefix: List[QuantifierStr], collapsed: CollapseCache, vars: VarSet, ignore_label:bool = False) -> z3.ExprRef:
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
    def get(self) -> Optional[List[QuantifierStr]]:
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
    def _all_quantifiers(self) -> List[QuantifierStr]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _V(self, quant: QuantifierStr, depth: int) -> z3.ExprRef:
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
                 max_depth: int = 1000000, max_clauses: int = 10, max_complexity: int = 10,
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
        self.prefixes: List[List[QuantifierStr]] = [[]]
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
                 max_depth: int = 1000000, max_clauses: int = 10, max_complexity: int = 1,
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
    def _filter_prefix(self, p: List[QuantifierStr]) -> bool:
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
                                  prefix: List[QuantifierStr], solver: z3.Solver) -> Optional[Formula]:
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

    def _all_quantifiers(self) -> List[QuantifierStr]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant: QuantifierStr, depth: int) -> z3.ExprRef:
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
                 max_depth: int = 1000000, max_clauses: int = 10, max_complexity: int = 1,
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

    def _filter_prefix(self, p: List[QuantifierStr]) -> bool:
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

    def _check_prefix_build_matrix(self, prefix: List[QuantifierStr], matrix_timer: Timer) -> Optional[Formula]:
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
    __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i']
    def __init__(self, index: int, instantiation: List[int], fo_type: int, model_i: int):
        self.index = index
        self.instantiation = instantiation
        self.children: List[InstantiationNode] = []
        self.fo_type = fo_type
        self.model_i = model_i

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

    def _all_quantifiers(self) -> List[QuantifierStr]:
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant: QuantifierStr, depth: int) -> z3.ExprRef:
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
    def _check_prefix_build_matrix(self, prefix: List[QuantifierStr], matrix_timer: Timer) -> Optional[Formula]:
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

    def _var_for_quantifier(self, quant: QuantifierStr, depth: int) -> z3.ExprRef:
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
    def _check_prefix_build_matrix(self, prefix: List[QuantifierStr], matrix_timer: Timer, constraints: List[z3.ExprRef], pos: Collection[int], neg: Collection[int], imp: Collection[Tuple[int, int]]) -> Optional[Formula]:
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

def pretty_prefix_var_names(sig: Signature, pre: Iterable[int]) -> List[str]:
    prefix = list(pre)
    used_names = set(sig.all_names())
    
    def name_options(sortname: str, k: int, skip:int) -> Iterator[List[str]]:
        def suffix(s: str) -> List[str]:
            if k == 1:
                return [s]
            else:
                return [f"{s}{i}" for i in range(1,k+1)]
        name_parts = re.split("[^a-zA-Z]+", sortname)
        if len(name_parts) == 0:
            yield suffix(f"V_{sortname}")
            yield from (suffix(f"V_{i}_{sortname}") for i in range(1, 1000000))
            return
        first_letter, initials = name_parts[0][0], "".join(np[0] for np in name_parts)
        first_word, last_word = name_parts[0], name_parts[-1]
        yield from (suffix(x) for x in [first_letter, initials, first_word, last_word])
        yield from (suffix("V_"+x) for x in [first_letter, initials, first_word, last_word])
        # we need skip because the generators are all incremented together when there
        # is a collision, and if we didn't advance them differently they could always
        # collide as they advance in lockstep
        yield from (suffix(f"V_{i}_"+initials) for i in range(1, 1000000, skip))
    
    c: Counter = Counter(prefix)
    options = dict((sort, name_options(sig.sort_names[sort].upper(), count, sort+1)) for sort, count in c.items())
    fixed = ["" for i in prefix]
    while len(options) > 0:
        possible = dict((sort, next(gen)) for sort, gen in options.items())
        # we need inv_map so that when a name collides, we can remember the first sort that needs
        # to be advanced, and not just advance the second when we find it. Otherwise if we have
        # quorum_a and quorum_b in the prefix, we could get vars q, qb, which wouldn't be symmetric
        # we instead want both to become qa and qb.
        inv_map: DefaultDict[str, List[int]] = defaultdict(list)
        bad_sorts: Set[int] = set()
        for sort, names in possible.items():
            for n in names:
                inv_map[n].append(sort)
                if len(inv_map[n]) > 1 or n in used_names:
                    bad_sorts.update(inv_map[n])
        for ind, sort in enumerate(prefix):
            if sort in possible and sort not in bad_sorts:
                n = possible[sort].pop(0)
                used_names.add(n)
                fixed[ind] = n
        options = dict((sort, gen) for (sort, gen) in options.items() if sort in bad_sorts)

    assert len(fixed) == len(prefix) == len(set(fixed))
    assert len(set(sig.all_names()).intersection(fixed)) == 0
    return fixed

def vars_of(t: Union[Term,Formula]) -> Iterator[str]:
    if isinstance(t, Var):
        yield t.var
    elif isinstance(t, Func):
        for c in t.args:
            yield from vars_of(c)
    elif isinstance(t, Not):
        yield from vars_of(t.f)
    elif isinstance(t, Relation):
        for c in t.args:
            yield from vars_of(c)
    elif isinstance(t, Equal):
        for c in t.args:
            yield from vars_of(c)


Quantifier = Tuple[bool, int] # is_forall, sort_index

class Constraint(object):
    """A separation constraint, one of `Pos(i)`, `Neg(i)`, or `Imp(i,j)`"""
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
        
class InstNode(object):
    """Represents an instantiated node in the tree of a particular model"""
    __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i']
    def __init__(self, index: int, instantiation: List[int], fo_type: int, model_i: int, n_sorts: int):
        self.index = index
        self.instantiation = instantiation
        self.children: List[List[InstNode]] = [[] for i in range(n_sorts)]
        self.fo_type = fo_type
        self.model_i = model_i

class HybridSeparator(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = []):
        self._sig = sig
        self._quiet = quiet
        self._logic = logic
        self._epr_wrt_formulas = epr_wrt_formulas
        self._separators: Dict[int, FixedHybridSeparator] = {}
        self._models: List[Model] = []

    def add_model(self, model:Model) -> int:
        l = len(self._models)
        self._models.append(model)
        for h in self._separators.values():
            h_l = h.add_model(model)
            assert h_l == l
        return l

    def _get_separator(self, clauses: int) -> 'FixedHybridSeparator':
        assert clauses > 0
        if clauses not in self._separators:
            h = FixedHybridSeparator(self._sig, clauses, self._quiet, self._logic, self._epr_wrt_formulas)
            for m in self._models:
                h.add_model(m)
            self._separators[clauses] = h
        return self._separators[clauses]
    def separate(self,
                 pos: Collection[int],
                 neg: Collection[int],
                 imp: Collection[Tuple[int, int]],
                 max_depth: int = 0,
                 max_clauses: int = 1000000,
                 max_complexity: int = 1000000,
                 timer: Timer = UnlimitedTimer(), matrix_timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        
        constraints: List[Constraint] = [Pos(x) for x in pos]
        constraints.extend(Neg(y) for y in neg)
        constraints.extend(Imp(a,b) for (a,b) in imp)
        
        assert max_clauses > 0

        max_depths = [0]
        while True:
            for i in range(len(max_depths)):
                # run clauses == i + 1 to depth max_depths[i]
                if max_depths[i] > max_depth or max_depths[i] + i > max_complexity:
                    continue
                r = self._get_separator(i + 1).separate_exact(constraints, max_depths[i], timer = timer)
                if r is not None:
                    return r
                max_depths[i] += 1
            if len(max_depths) < max_clauses:
                max_depths.append(0)
            if all(d > max_depth or d + i > max_complexity for i, d in enumerate(max_depths)):
                return None

        # for depth in range(max_depth+1):
        #     for clauses in range(1, max_clauses+1):
        #         r = self._get_separator(clauses).separate_exact(constraints, depth, timer = timer)
        #         if r is not None:
        #             return r
        # return None

class FixedHybridSeparator(object):
    def __init__(self, sig: Signature, clauses: int, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = [], seed:Optional[int] = None):
        self._sig = sig
        self._clauses = clauses
        self._logic = logic
        self.solver = z3.Solver()
        if seed is None:
            seed = random.randint(0, 2**32)
        self.solver.set("seed", seed)
        self._highest_depth_var = 0
        self._highest_prefix: DefaultDict[int, int] = defaultdict(int)

        self._models: List[Model] = []
        self._node_roots: Dict[Tuple[int,int], InstNode] = {}
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
    def _prefix_vars(self, conjunct: int, is_forall: bool, sort: int, depth: int) -> z3.ExprRef:
        return z3.And(self._prefix_sort_var(conjunct, sort, depth), 
                        self._prefix_quant_var(conjunct, depth) if is_forall else
                        z3.Not(self._prefix_quant_var(conjunct, depth)))

    def _prefix_var_definition(self, conjunct: int, depth: int) -> None:
        n_sorts = len(self._sig.sort_names)
        for d in range(self._highest_prefix[conjunct], depth):
            self.solver.add(z3.PbEq([(self._prefix_sort_var(conjunct, q, d), 1) for q in range(n_sorts)], 1))
            if 0 < d:
                for i,j in itertools.combinations(reversed(range(n_sorts)), 2):
                    # Prevent adjacent universals unless their sorts are in non-strict increasing order
                    A_i_dm1 = self._prefix_vars(conjunct, True, i, d-1)
                    A_j_d = self._prefix_vars(conjunct, True, j, d)
                    self.solver.add(z3.Not(z3.And(A_i_dm1, A_j_d)))
                    # Same for existentials
                    E_i_dm1 = self._prefix_vars(conjunct, False, i, d-1)
                    E_j_d = self._prefix_vars(conjunct, False, j, d)
                    self.solver.add(z3.Not(z3.And(E_i_dm1, E_j_d)))
            if self._logic == "universal":
                self.solver.add(self._prefix_quant_var(conjunct, d))
            # TODO: add other logic restrictions
        self._highest_prefix[conjunct] = max(self._highest_prefix[conjunct], depth)

    def _make_node(self, model_i: int, inst: List[int]) -> InstNode:
        fo_type = self._collapse_cache.get(model_i, inst)
        c = InstNode(self._next_node_index, inst, fo_type, model_i, len(self._sig.sort_names))
        self._next_node_index += 1
        var = z3.Bool(f"v_{c.index}")
        d = len(c.instantiation)
        self.solver.add(z3.Implies(self._depth_var(0, d), var == self._fo_type_var(c.fo_type)))
        self.solver.add(z3.Implies(self._depth_greater_var(0, d),
                                    z3.Implies(self._fo_type_var(c.fo_type), var)))
        return c

    def _root_var(self, model: int, conjunct: int) -> z3.ExprRef:
        if (model, conjunct) not in self._node_roots:
            self._node_roots[(model, conjunct)] = self._make_node(model, [])
        return z3.Bool(f"v_{self._node_roots[(model, conjunct)].index}")

    def _expand_node(self, conjunct:int, node: InstNode, sort: int) -> None:
        if len(node.children[sort]) > 0:
            return # don't expand twice
        m_i = node.model_i
        for e in self._models[m_i].elems_of_sort_index[sort]:
            ins = node.instantiation + [e]
            node.children[sort].append(self._make_node(node.model_i, node.instantiation + [e]))
        d = len(node.instantiation)
        var = z3.Bool(f"v_{node.index}")
        child_vars = [z3.Bool(f"v_{c.index}") for c in node.children[sort]]
        Dg_and_forall = z3.And(self._depth_greater_var(conjunct, d), self._prefix_vars(conjunct, True, sort, d))
        Dg_and_exists = z3.And(self._depth_greater_var(conjunct, d), self._prefix_vars(conjunct, False, sort, d))
        self.solver.add(z3.Implies(Dg_and_forall, var == z3.And(child_vars)))
        self.solver.add(z3.Implies(Dg_and_exists, var == z3.Or(child_vars)))

    def _literal_var(self, conjunct: int, clause: int, atom: int, polarity: bool) -> z3.ExprRef:
        i = (conjunct, clause, atom)
        if i not in self._atoms_defined:
            self.solver.add(z3.Or(z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1}")),
                                  z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{0}"))))
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
                z3.And([z3.Or([self._literal_var(0, cl, a, p) for (a,p) in atoms_with_polarity]) for cl in range(self._clauses)]))

            self._fo_types_defined.add(fo_type)
        return z3.Bool(f"M_{fo_type}")



    def _extract_cnf_formula(self, m: z3.ModelRef, conjunct: int, depth: int, clauses: int) \
                               -> Tuple[List[Tuple[bool, int]], List[List[Formula]]]:
        prefix = []
        for d in range(depth):
            for q in range(len(self._sig.sort_names)):
                if z3.is_true(m[self._prefix_sort_var(conjunct, q, d)]):
                    is_forall = z3.is_true(m[self._prefix_quant_var(conjunct, d)])
                    prefix.append((is_forall, q))
                    break
        assert(len(prefix) == depth) # This holds because each depth has exactly one prefix_sort_var true
        atom_possiblities = self._all_atoms([q[1] for q in prefix])
        matrix_list: List[List[Formula]] = []
        for cl in range(clauses):
            matrix_list.append([])
            for a in atom_possiblities:
                if z3.is_true(m[self._literal_var(conjunct, cl, a, True)]):
                    matrix_list[-1].append(self._atoms[a])
                elif z3.is_true(m[self._literal_var(conjunct, cl, a, False)]):
                    matrix_list[-1].append(Not(self._atoms[a]))
                # else atom doesn't appear either positively or negatively so do nothing
        return (prefix, matrix_list)

    def _constraint_assumptions(self, constraints: List[Constraint]) -> Iterator[z3.ExprRef]:
        for const in constraints:
            if isinstance(const, Pos):
                yield self._root_var(const.i, 0)
            if isinstance(const, Neg):
                yield z3.Not(self._root_var(const.i, 0))
            if isinstance(const, Imp):
                yield z3.Implies(self._root_var(const.i, 0), self._root_var(const.j, 0))
    def _prefix_assumptions(self, prefix: List[Quantifier]) -> List[z3.ExprRef]:
        return [self._prefix_sort_var(0, q, d) for (d,(i,q)) in enumerate(prefix)] + \
               [((lambda x: x) if is_fa else z3.Not)(self._prefix_quant_var(0,d))
                for (d,(is_fa,q)) in enumerate(prefix)]
    def _cnf_matrix_assumptions(self, prefix: List[Quantifier], matrix: List[List[Formula]]) -> List[z3.ExprRef]:
        atom_possiblities = self._all_atoms([q[1] for q in prefix])
        assumptions = []
        for i, cl in enumerate(matrix):
            contained_atoms: Dict[int, bool] = {}
            for literal in cl:
                if isinstance(literal, Not):
                    contained_atoms[self._atom_id(literal.f)] = False
                else:
                    contained_atoms[self._atom_id(literal)] = True
            for a in atom_possiblities:
                if a in contained_atoms:
                    assumptions.append(self._literal_var(0, i, a, contained_atoms[a]))
                else:
                    assumptions.append(z3.Not(self._literal_var(0, i, a, True)))
                    assumptions.append(z3.Not(self._literal_var(0, i, a, False)))
        return assumptions

    def _cnf_matrix_value(self, matrix_list: List[List[Formula]], model: Model, mapping: Dict[str, int] = {}) \
                            -> Optional[bool]:
        """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
        all_clause_true, any_clause_unk = True, False
        for clause in matrix_list:
            cl_true, cl_unk = False, False
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
            any_clause_unk = any_clause_unk or (cl_unk and not cl_true)
        if all_clause_true:
            return True
        elif not any_clause_unk:
            return False
        else:
            return None

    def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[Formula]],
                                constraints: List[Constraint]) -> bool:
        depth = len(prefix)
        matrix = And([Or(cl) for cl in matrix_list])
        prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])

        _matrix_value_cache: Dict[int, Optional[bool]] = {}
        def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
            if fo_type not in _matrix_value_cache:
                (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                mapping = {v: e for v,e in zip(prefix_vars, assignment)}
                _matrix_value_cache[fo_type] = self._cnf_matrix_value(matrix_list, self._models[model_i], mapping)
            return _matrix_value_cache[fo_type]

        def check_assignment(asgn: List[int], model: Model) -> bool:
            if len(asgn) == depth:
                return check(matrix, model, {v: e for v,e in zip(prefix_vars, asgn)})
            else:
                (is_forall, sort) = prefix[len(asgn)]
                univ = model.elems_of_sort[self._sig.sort_names[sort]]
                return (all if is_forall else any)(check_assignment(asgn + [e], model) for e in univ)

        def expand_to_prove(n: InstNode, expected: bool) -> bool:
            matrix_value = matrix_value_fo_type(n.fo_type)
            # Early out because the solver knows that M_i => v_j, so if we know M_i is True, so does the solver
            if not expected and matrix_value is True:
                return False            
            if len(n.instantiation) == depth:
                assert matrix_value is not None
                return expected is matrix_value
            # we aren't at the base, but check the rest of the quantifiers and return if they match
            if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                return True

            is_forall, sort = prefix[len(n.instantiation)]
            self._expand_node(0, n, sort)
            for c in n.children[sort]:
                expand_to_prove(c, expected)
            return False

        _root_node_cache: Dict[int, bool] = {}
        def root_node_value(n: int) -> bool:
            if n not in _root_node_cache:
                _root_node_cache[n] = check_assignment([], self._models[n])
            return _root_node_cache[n]

        def swap_to_front(c: int) -> None:
            constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
        
        for c_i in range(len(constraints)):
            c = constraints[c_i]
            if isinstance(c, Pos):
                if not root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[(c.i, 0)], True)
                    return False
            elif isinstance(c, Neg):
                if root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[(c.i,0)], False)
                    return False
            elif isinstance(c, Imp):
                if root_node_value(c.i) and not root_node_value(c.j):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[(c.i,0)], False)
                    expand_to_prove(self._node_roots[(c.j,0)], True)
                    return False
        return True

    
    def _local_optimize_matrix(self, prefix: List[Quantifier], matrix: List[List[Formula]],
                         constraints: List[Constraint], timer: Timer) -> Tuple[List[Quantifier], List[List[Formula]]]:
        assumptions = [self._depth_var(0, len(prefix))] + self._prefix_assumptions(prefix) + list(self._constraint_assumptions(constraints))
        def opt(matrix: List[List[Formula]]) -> List[List[Formula]]:
        
            final_matrix: List[List[Formula]] = [[] for cl in matrix]
            remaining_matrix = [list(cl) for cl in matrix] # shallow copy because we are going to mutate
            while any(len(cl) != 0 for cl in remaining_matrix):
                for i,cl in enumerate(remaining_matrix):
                    a = cl.pop()
                    a_clause = i
                # candidate matrix is final and remaining, which now lacks `a`
                candidate_matrix = [f+r for f,r in zip(final_matrix, remaining_matrix)]

                # todo: thread timer here
                asmp = assumptions + self._cnf_matrix_assumptions(prefix, candidate_matrix)
                if timer.solver_check(self.solver, *asmp) == z3.sat\
                   and self._check_formula_validity(prefix, candidate_matrix, constraints):
                    # candidate matrix is actually correct on the constraints
                    matrix = candidate_matrix
                else:
                    final_matrix[a_clause].append(a)
            return matrix
        while True:
            old_size = sum(len(cl) for cl in matrix)
            matrix = opt(matrix)
            if old_size == sum(len(cl) for cl in matrix):
                break
        return prefix, matrix

    def _global_optimize_matrix(self, prefix: List[Quantifier], matrix: List[List[Formula]],
                                constraints: List[Constraint], timer: Timer) -> Tuple[List[Quantifier], List[List[Formula]]]:
        
        assumptions = [self._depth_var(0, len(prefix))] + list(self._constraint_assumptions(constraints)) + self._prefix_assumptions(prefix)  
        atoms = self._all_atoms([q[1] for q in prefix])
        literal_vars = [(self._literal_var(0, cl, a, False), 1) for cl in range(len(matrix)) for a in atoms] +\
                       [(self._literal_var(0, cl, a, True), 1) for cl in range(len(matrix)) for a in atoms]
        upper = sum(len(cl) for cl in matrix)
        lower = 0

        while True:
            assert lower <= upper
            if lower == upper:
                break
            k = (upper+lower) // 2
            bound = z3.PbLe(literal_vars, k)
            print(f"Optimize checking if there is a formula of size <= {k} (lower {lower} upper {upper})")
            res = timer.solver_check(self.solver, *assumptions, bound)
            if res == z3.sat:
                _, candidate_matrix = self._extract_cnf_formula(self.solver.model(), 0, len(prefix), len(matrix))
                print("candidate", candidate_matrix)
                if self._check_formula_validity(prefix, candidate_matrix, constraints):
                    print("Found new matrix")
                    matrix = candidate_matrix
                    upper = k
                else:
                    print("Matrix wasn't valid")
                    pass # do nothing, because now the solver knows more and won't give us the same matrix
            else:
                print("Couldn't solve problem")
                lower = k + 1

        return (prefix, matrix)
        
    def separate_exact(self,
                 constraints: List[Constraint],
                 depth: int = 0,
                 timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        
        constraints = list(constraints)
        self._prefix_var_definition(0, depth)
        assumptions = list(self._constraint_assumptions(constraints)) + [self._depth_var(0, depth)]

        prefix_assumptions: List[z3.ExprRef] = []

        print(f"Separating depth {depth} clauses {self._clauses}")
        while True:
            res = timer.solver_check(self.solver, *(assumptions + prefix_assumptions))
            if res == z3.unsat:
                if len(prefix_assumptions) > 0:
                    prefix_assumptions = []
                else:
                    return None
            elif res == z3.sat:
                (prefix, matrix_list) = self._extract_cnf_formula(self.solver.model(), 0, depth, self._clauses)
                matrix = And([Or(cl) for cl in matrix_list])
                prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                       for name, (pol, sort) in zip(prefix_vars, prefix)]),
                       "matrix", And([Or(cl) for cl in matrix_list]))

                if self._check_formula_validity(prefix, matrix_list, constraints):
                    if True:
                        prefix, matrix_list = self._global_optimize_matrix(prefix, matrix_list, constraints, timer)
                    else:
                        prefix, matrix_list = self._local_optimize_matrix(prefix, matrix_list, constraints, timer)
                    prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])
                    pretty_vars = pretty_prefix_var_names(self._sig, (q[1] for q in prefix))
                    mapping = dict(zip(prefix_vars, pretty_vars))
                    fff: Formula = And([Or([rename_free_vars(a, mapping) for a in cl]) for cl in matrix_list])
                    for varname, (is_forall, sort) in reversed(list(zip(pretty_vars, prefix))):
                        fff = (Forall if is_forall else Exists)(varname, self._sig.sort_names[sort], fff) 
                    return fff
                
                # formula wasn't correct, but we expanded some nodes in the tree to show the solver why it was wrong. go back up and try again
                print(f"expanded nodes: {self._next_node_index}/{sum(len(model.elems) ** d for model in self._models for d in range(depth+1))}")
                # Assume the same prefix on the next iteration, to help by focusing the solver
                prefix_assumptions = self._prefix_assumptions(prefix)
            else:
                print(self.solver)
                assert False # z3 should always return SAT/UNSAT on propositional formula
        
