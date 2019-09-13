
from collections import defaultdict
import itertools, copy, time, sys, re
from typing import Tuple, TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, List, Dict

import z3

from .logic import Forall, Exists, Equal, Relation, And, Or, Not
from .check import check, resolve_term
from .matrix import infer_matrix, K_function_unrolling
from .timer import Timer, UnlimitedTimer


def collapse(model, sig, assignment):
    mapping = {}
    sorts = []
    def get_element(e):
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

class CollapseCache(object):
    def __init__(self, sig, models = []):
        self.models = models
        self.sig = sig
        self.cache = {}
        self.collapsed = {}
        self.assignments = []
        self.all_assignments = defaultdict(list)
    def add_model(self, model):
        self.models.append(model)
    def get(self, index, assignment):
        N = len(self.models[index].sorts)
        assignment = tuple(assignment)
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
    def get_concrete(self, i):
        (index, assignment) = self.assignments[i]
        M = copy.deepcopy(self.models[index])
        for var_i, element in enumerate(assignment):
            M.add_constant("x_"+str(var_i), M.names[element])
        return M
    def fo_type_count(self):
        return len(self.collapsed)
    def __len__(self):
        return len(self.assignments)

def prefix_is_redundant(prefix):
    if len(prefix) == 0: return False
    for i in range(len(prefix) - 1):
        a,b = prefix[i], prefix[i+1]
        if a[0] == b[0] and a[1] > b[1]:
            return True
    return False

def build_prefix_formula(prefix, f, n = 0):
    if len(prefix) == 0:
        return f
    (is_forall, sort) = prefix[0]
    if is_forall:
        return Forall("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))
    else:
        return Exists("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))

class VarSet(object):
    def __init__(self):
        self.vars = set()
        self.pos = set()
        self.neg = set()
    def add(self, v, polarity):
        self.vars.add(v)
        if polarity:
            self.pos.add(v)
        else:
            self.neg.add(v)
    def __iter__(self): return iter(self.vars)

def formula_for_model(model_index, assignment, prefix_i, prefix, collapsed, vars):
    m = collapsed.models[model_index]
    if prefix_i == len(prefix):
        for i, (_, sort) in enumerate(prefix):
            assert(collapsed.models[model_index].sorts[assignment[i]] == sort)
        x = collapsed.get(model_index, assignment)
        v = z3.Bool("M"+str(x))
        polarity = m.label.startswith("+")
        vars.add(x, polarity)
        return v if polarity else z3.Not(v)
    else:
        (is_forall, sort) = prefix[prefix_i]
        formulas = []
        for elem in m.elems_of_sort[sort]:
            f = formula_for_model(model_index, assignment + [elem], prefix_i+1, prefix, collapsed, vars)
            formulas.append(f)
        if is_forall == m.label.startswith("+"):
            return z3.And(formulas)
        else:
            return z3.Or(formulas)

def check_prefix(models, prefix, sig, collapsed, solver):
    solver.push()
    vars = VarSet()
    sat_formula = z3.And([formula_for_model(m_index, [], 0, prefix, collapsed, vars) for m_index in range(len(models))])
    solver.add(sat_formula)
    result = solver.check()
    solver.pop()
    if result == z3.unsat:
        return False
    elif result == z3.sat:
        return True
    else:
        assert False and "Error, z3 returned unknown"



def ae_edges_of(sig):
    ae = {sort: set() for sort in sig.sorts}
    for f, (arg_sorts, ret_sort) in sig.functions.items():
        for a in arg_sorts:
            ae[a].add(ret_sort)
    return ae

def update_ae_edges(ae, f, negate=False, outer_universal_sorts=set()):
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

def digraph_is_acyclic(edges):
    visited = set()
    time = {}
    def visit(n):
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
    def __init__(self, depth, sort_indices, logic="fol"):
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
    def get(self):
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
    def add(self, unsat_core_vars):
        self.solver.add(z3.Not(z3.And(unsat_core_vars)))
    def _all_quantifiers(self):
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _V(self, quant, depth):
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

class Separator(object):
    def __init__(self, sig, quiet=False, logic="fol", epr_wrt_formulas = []):
        self.sig = sig
        self.collapsed = CollapseCache(sig)
        self.models = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.forget_learned_facts()

    def add_model(self, model):
        self.models.append(model)
        self.collapsed.add_model(model)
    def forget_learned_facts(self):
        """Forgets all inferred facts (about prenex, etc) but keeps models"""
        self.prefixes = [[]]
        self.prefix_index = 0
    def separate(self, max_depth = 1000000, timer = UnlimitedTimer(), matrix_timer = UnlimitedTimer()):
        self.timer = timer
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
                c = self.check_prefix_build_matrix(p, solver)
                if c is not None:
                    return c
            self.prefix_index += 1
    def _filter_prefix(self, p):
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True
    def check_prefix_build_matrix(self, prefix, solver):
        solver.push()
        vars = VarSet()
        formulas = []
        for m_index in range(len(self.models)):
            formulas.append(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars))
            self.timer.check_time()
        sat_formula = z3.And(formulas)
        # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))
        solver.add(sat_formula)
        result = self.timer.solver_check(solver)
        solver.pop()
        if result == z3.unsat:
            return None
        elif result == z3.sat:
            sig_with_bv = copy.deepcopy(self.sig)
            for i,(_, sort) in enumerate(prefix):
                assert "x_"+str(i) not in sig_with_bv.constants
                sig_with_bv.constants["x_"+str(i)] = sort

            concrete_models = {}
            for x in vars:
                concrete_models[x] = self.collapsed.get_concrete(x)

            matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
            checker = z3.Solver()
            checker.add(sat_formula)
            for x, m in concrete_models.items():
                checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
            if checker.check() != z3.sat:
                raise RuntimeError("Incorrect matrix!")
            return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

class SeparatorReductionV1(object):
    def __init__(self, sig, quiet=False, logic="fol", epr_wrt_formulas = []):
        self.sig = sig
        self.sort_indices = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models = []
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

    def add_model(self, model):
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        v = self._construct_instantiation(model, model_i, [], self.cached_solver_depth, self.cached_solver)
        self.cached_solver.add(v if model.label.startswith("+") else z3.Not(v))
    # def forget_learned_facts(self):
    #     """Forgets all inferred facts (about prenex, etc) but keeps models"""
    #     self.prefixes = [[]]
    #     self.prefix_index = 0
    #     self.cached_solver_depth = -1

    def _all_quantifiers(self):
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant, depth):
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _construct_instantiation(self, model, model_i, instantiation, depth, solver):
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

    def _setup_solver_for_depth(self):
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

    def separate(self, max_depth = 1000000, timer = UnlimitedTimer(), matrix_timer = UnlimitedTimer()):
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
            # if self.prefix_index == len(self.prefixes):
            #     # We have reached our maximum depth, don't generate larger prefixes
            #     if len(self.prefixes[0]) == max_depth:
            #         return None
            #     self.prefixes = [[(is_forall, s)]+p for is_forall in [True, False]
            #                      for p in self.prefixes for s in sorted(self.sig.sorts)]
            #     self.prefixes = [p for p in self.prefixes if self._filter_prefix(p)]
            #     self.prefix_index = 0
            #     self._setup_solver_for_depth()
            # p = self.prefixes[self.prefix_index]
            if True or not prefix_is_redundant(p): # TODO: put redundant constraints in the prefix searcher
                if not self.quiet:
                    print ("Prefix:", " ".join([("∀" if is_forall else "∃") + sort + "." for (is_forall, sort) in p]))
                c = self._check_prefix_build_matrix(p, matrix_timer)
                if c is not None:
                    return c
    def _filter_prefix(self, p):
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True

    def _check_prefix_build_matrix(self, prefix, matrix_timer):
        start = time.time()
        # self.cached_solver.push()
        # self.cached_solver.add([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
        result = self.timer.solver_check(self.cached_solver, [self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
        # print(self.cached_solver)
        # self.cached_solver.pop()
        # print(result, f"{time.time() - start:0.3f}")
        # print("(result == z3.sat)", (result == z3.sat))
        # print("check_prefix", check_prefix(self.models, prefix, self.sig, self.collapsed, z3.Solver()))
        # assert ((result == z3.sat) == check_prefix(self.models, prefix, self.sig, self.collapsed, z3.Solver()))

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
                # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for x in vars:
                    concrete_models[x] = self.collapsed.get_concrete(x)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
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
    index: int
    instantiation: List[int]
    children: List['InstantiationNode']
    fo_type: int
    model_i: int
    def __init__(self, index, instantiation, fo_type, model_i):
        self.index = index
        self.instantiation = instantiation
        self.children = []
        self.fo_type = fo_type
        self.model_i = model_i

class SortNode(object):
    children: Dict[str, 'SortNode']
    fo_types: Set[int]
    def __init__(self):
        self.children = {}
        self.fo_types = set()
    def get_child(self, sort):
        if sort not in self.children:
            self.children[sort] = SortNode()
        return self.children[sort]
    def types_for(self, sorts, sorts_i = 0):
        if len(sorts) == sorts_i:
            return self.fo_types
        else:
            if sorts[sorts_i] is None:
                return self.fo_types.union(*[c.types_for(sorts, sorts_i + 1) for c in self.children.values()])
            if sorts[sorts_i] not in self.children:
                return self.fo_types
            return self.fo_types | self.get_child(sorts[sorts_i]).types_for(sorts, sorts_i + 1)
    def add_type(self, sorts, fo_type, sorts_i = 0):
        if len(sorts) == sorts_i:
            self.fo_types.add(fo_type)
        else:
            self.get_child(sorts[sorts_i]).add_type(sorts, fo_type, sorts_i + 1)

class SeparatorReductionV2(object):
    def __init__(self, sig, quiet=False, logic="fol", epr_wrt_formulas = []):
        self.sig = sig
        self.sort_indices = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.solver = None
        self.model_nodes = []
        self.expanded_fo_types = set()
        self.asserted_depth_fo_types = set()
        self.fo_type_depths = {}
        self.nodes_by_index = {}
        self.next_node_index = 0
        self.prefixes = PrefixSolver(0, self.sort_indices)
        # self.prefix_index = 0
        self.nodes_by_type = defaultdict(list)
        self.sort_root = SortNode()
        self._rebuild_solver()

    def _new_node_index(self):
        v = self.next_node_index
        self.next_node_index += 1
        return v
    def add_model(self, model):
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        new_root = InstantiationNode(self._new_node_index(), [], self.collapsed.get(model_i, []), model_i)
        self._register_node(new_root)
        self.model_nodes.append(new_root)
        self._expand_existing_fo_types(new_root)
        v = z3.Bool(f"v{new_root.index}")
        self.solver.add(v if model.label.startswith("+") else z3.Not(v))

    def _all_quantifiers(self):
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant, depth):
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _expand_node(self, node):
        model = self.models[node.model_i]
        for elem in range(len(model.elems)):
            es = node.instantiation + [elem]
            # print(es)
            fo_type = self.collapsed.get(node.model_i, es)
            child = InstantiationNode(self._new_node_index(), es, fo_type, node.model_i)
            node.children.append(child)
            self._register_node(child)

    def _register_node(self, node):
        self.nodes_by_type[node.fo_type].append(node)
        self.nodes_by_index[node.index] = node
        self.solver.add(z3.Implies(z3.Bool(f"T{node.fo_type}"), z3.Bool(f"M{node.fo_type}") == z3.Bool(f"v{node.index}")))
        if node.fo_type not in self.fo_type_depths:
            self.fo_type_depths[node.fo_type] = len(node.instantiation)
            m = self.models[node.model_i]
            self.sort_root.add_type([m.sorts[x] for x in node.instantiation], node.fo_type)
            self.solver.add(z3.Implies(z3.Bool(f"D{len(node.instantiation)}"), z3.Bool(f"T{node.fo_type}")))



    def _define_node(self, node):
        model = self.models[node.model_i]
        var = z3.Bool(f"v{node.index}")
        for sort in sorted(self.sort_indices.keys()):
            subvars = [z3.Bool(f"v{c.index}") for c in node.children if model.sorts[c.instantiation[-1]] == sort]
            for is_forall in [True, False]:
                self.solver.add(z3.Implies(self._var_for_quantifier((is_forall, sort), len(node.instantiation)),
                                      var == (z3.And(subvars) if is_forall else z3.Or(subvars))))

    def _expand_existing_fo_types(self, node):
        if node.fo_type not in self.expanded_fo_types:
            return
        assert len(node.children) == 0
        self._expand_node(node)
        self._define_node(node)

        for c in node.children:
            self._expand_existing_fo_types(c)
    def _expand_nodes_for_fo_type(self, fo_type):
        for node in self.nodes_by_type[fo_type]:
            self._expand_node(node)
            self._define_node(node)
        self.expanded_fo_types.add(fo_type)

    def _rebuild_solver(self):
        self.solver = z3.Solver()
        self.solver.set("unsat_core", True, "core.minimize", False)
        self.solver_depth_assertions = 0

    def _ensure_quantifier_definitions(self, max_depth):
        for d in range(self.solver_depth_assertions, max_depth):
            self.solver.add(z3.PbEq([(self._var_for_quantifier(q, d), 1) for q in self._all_quantifiers()], 1))
        self.solver_depth_assertions = max(self.solver_depth_assertions, max_depth)

    def separate(self, max_depth = 1000000, timer = UnlimitedTimer(), matrix_timer = UnlimitedTimer()):
        self.timer = timer
        self._ensure_quantifier_definitions(self.prefixes.depth)
        self._begin_equalities()

        try:
            while True:
                p = self.prefixes.get()

                if p is None:
                    if self.prefixes.depth == max_depth:
                        return None
                    self.prefixes = PrefixSolver(self.prefixes.depth + 1, self.sort_indices)
                    self._end_equalities()
                    self._ensure_quantifier_definitions(self.prefixes.depth)
                    self._begin_equalities()
                    p = self.prefixes.get()

                # if self.prefix_index == len(self.prefixes):
                #     # We have reached our maximum depth, don't generate larger prefixes
                #     if len(self.prefixes[0]) == max_depth:
                #         return None
                #     self.prefixes = [[(is_forall, s)]+p for is_forall in [True, False]
                #                     for p in self.prefixes for s in sorted(self.sig.sorts)]
                #     self.prefixes = [p for p in self.prefixes if self._filter_prefix(p)]
                #     self.prefix_index = 0
                #     # reset equalities, because depth increase means that the lowest depth ones
                #     # must be reasserted so they are in the UNSAT core. Also take this opportunity
                #     # to make sure the right definitions for quantifiers are there
                #     self._end_equalities()
                #     self._ensure_quantifier_definitions(len(self.prefixes[0]))
                #     self._begin_equalities()
                # p = self.prefixes[self.prefix_index]

                if True or not prefix_is_redundant(p):
                    if not self.quiet:
                        # print("Prefix:", " ".join([("∀" if is_forall else "∃")+f"{sort}." for (is_forall, sort) in p]), f"{self.prefix_index+1}/{len(self.prefixes)}")
                        print("Prefix:", " ".join([("∀" if is_forall else "∃")+f"{sort}." for (is_forall, sort) in p]))
                    c = self._check_prefix_build_matrix(p, matrix_timer)
                    if c is not None:
                        return c
                # self.prefix_index += 1
        finally:
            self._end_equalities()
    def _filter_prefix(self, p):
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True

    def _begin_equalities(self):
        return
        self.solver.push()
        self.asserted_equality_fo_types = set()

    def _end_equalities(self):
        return
        self.solver.pop()
        self.asserted_equality_fo_types = set()

    # def _assert_equalities(self, sorts):
    #     current_depth = len(sorts)
    #     x = 0
    #     for fo_type in self.sort_root.types_for([s if i < current_depth/2 else None for i,s in enumerate(sorts)]):
    #         if fo_type in self.expanded_fo_types or fo_type in self.asserted_equality_fo_types:
    #             continue
    #         nodes = self.nodes_by_type[fo_type]
    #         if self.fo_type_depths[fo_type] < current_depth:
    #             self.solver.assert_and_track(z3.And([z3.Bool(f"M{fo_type}") == z3.Bool(f"v{n.index}")
    #                                                 for n in nodes]), f"T{fo_type}")
    #         else:
    #             self.solver.add(z3.And([z3.Bool(f"M{fo_type}") == z3.Bool(f"v{n.index}")
    #                                                 for n in nodes]))
    #         self.asserted_equality_fo_types.add(fo_type)
    #         x += 1
    #     print("Added", x, "fo type assertions")

    def _assert_equalities(self, sorts):
        current_depth = len(sorts)
        a = []
        for fo_type in self.sort_root.types_for(sorts):
            if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < current_depth:
                a.append(z3.Bool(f"T{fo_type}"))
        return a

    def _print(self, *args):
        if not self.quiet:
            print(*args)
    def _check_prefix_build_matrix(self, prefix, matrix_timer):
        start = time.time()
        sorts_of_prefix = [s for (is_forall, s) in prefix]

        while True:
            # print("Attempting")
            assumptions = self._assert_equalities(sorts_of_prefix)
            assumptions.append(z3.Bool(f"D{len(prefix)}"))
            assumptions.extend([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])

            # self.solver.push()
            # self.solver.add(z3.Bool(f"D{len(prefix)}"))
            # self.solver.push()
            # self.solver.add([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
            # print(self.solver)
            self._print("checking...")
            print(f"Used {len(assumptions)} assumptions")
            #print(self.solver)
            result = self.timer.solver_check(self.solver, assumptions)

            if result == z3.unsat:
                self._print("constructing unsat core...")
                core = self.solver.unsat_core()

            # self.solver.pop()

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

                    final_core = []
                    initial_core = list(reversed(prefix_core_vars))
                    #initial_core = list(prefix_core_vars)
                    while len(initial_core) > 0:
                        print(final_core, [initial_core[0]], initial_core[1:])
                        assumptions = self._assert_equalities([s if False else None for i, s in enumerate(sorts_of_prefix)]) + [z3.Bool(f"D{len(prefix)}")]
                        print(len(assumptions))
                        r = self.timer.solver_check(self.solver, assumptions + final_core + initial_core[1:])
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
                    c = len(possible_expansions)
                    self._print("expanding", c, "fo-types")
                    self._end_equalities()
                    for t in possible_expansions:
                        if t not in self.expanded_fo_types:
                            self._expand_nodes_for_fo_type(t)
                    self._begin_equalities()
                    self._assert_equalities(sorts_of_prefix)
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
                    formulas.append(formula_for_model(m_index, [], 0, prefix, self.collapsed, vars))
                    self.timer.check_time()
                sat_formula = z3.And(formulas)
                # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for x in vars:
                    concrete_models[x] = self.collapsed.get_concrete(x)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
                checker = z3.Solver()
                checker.add(sat_formula)
                for x, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

class GeneralizedSeparator(object):
    def __init__(self, sig, quiet=False, logic="fol", epr_wrt_formulas = []):
        self.sig = sig
        self.sort_indices = {}
        for sort in sorted(sig.sorts):
            self.sort_indices[sort] = len(self.sort_indices)
        self.collapsed = CollapseCache(sig)
        self.models = []
        self.quiet = quiet
        self.logic = logic
        self.ae_edges = None
        if logic == "epr":
            assert False # EPR unsupported
        self.solver = None
        self.model_nodes = []
        self.expanded_fo_types = set()
        self.asserted_depth_fo_types = set()
        self.fo_type_depths = {}
        self.nodes_by_index = {}
        self.next_node_index = 0
        self.prefixes = PrefixSolver(0, self.sort_indices, logic=self.logic)
        # self.prefix_index = 0
        self.nodes_by_type = defaultdict(list)
        self.sort_root = SortNode()
        self._cached_pos = {}
        self._cached_neg = {}
        self._cached_imp = {}
        
        self._rebuild_solver()

    def _new_node_index(self):
        v = self.next_node_index
        self.next_node_index += 1
        return v
    def add_model(self, model):
        model_i = len(self.models)
        self.models.append(model)
        self.collapsed.add_model(model)

        new_root = InstantiationNode(self._new_node_index(), [], self.collapsed.get(model_i, []), model_i)
        self._register_node(new_root)
        self.model_nodes.append(new_root)
        self._expand_existing_fo_types(new_root)
        return new_root.index

    def _all_quantifiers(self):
        return [(is_forall, sort) for is_forall in [True, False] for sort in sorted(self.sort_indices.keys())]
    def _var_for_quantifier(self, quant, depth):
        (is_forall, sort) = quant
        return z3.Bool("{}_{}_{}".format("A" if is_forall else "E", self.sort_indices[sort], depth))

    def _expand_node(self, node):
        model = self.models[node.model_i]
        for elem in range(len(model.elems)):
            es = node.instantiation + [elem]
            # print(es)
            fo_type = self.collapsed.get(node.model_i, es)
            child = InstantiationNode(self._new_node_index(), es, fo_type, node.model_i)
            node.children.append(child)
            self._register_node(child)

    def _register_node(self, node):
        self.nodes_by_type[node.fo_type].append(node)
        self.nodes_by_index[node.index] = node
        self.solver.add(z3.Implies(z3.Bool(f"T{node.fo_type}"), z3.Bool(f"M{node.fo_type}") == z3.Bool(f"v{node.index}")))
        if node.fo_type not in self.fo_type_depths:
            self.fo_type_depths[node.fo_type] = len(node.instantiation)
            m = self.models[node.model_i]
            self.sort_root.add_type([m.sorts[x] for x in node.instantiation], node.fo_type)
            self.solver.add(z3.Implies(z3.Bool(f"D{len(node.instantiation)}"), z3.Bool(f"T{node.fo_type}")))



    def _define_node(self, node):
        model = self.models[node.model_i]
        var = z3.Bool(f"v{node.index}")
        for sort in sorted(self.sort_indices.keys()):
            subvars = [z3.Bool(f"v{c.index}") for c in node.children if model.sorts[c.instantiation[-1]] == sort]
            for is_forall in [True, False]:
                self.solver.add(z3.Implies(self._var_for_quantifier((is_forall, sort), len(node.instantiation)),
                                      var == (z3.And(subvars) if is_forall else z3.Or(subvars))))

    def _expand_existing_fo_types(self, node):
        if node.fo_type not in self.expanded_fo_types:
            return
        assert len(node.children) == 0
        self._expand_node(node)
        self._define_node(node)

        for c in node.children:
            self._expand_existing_fo_types(c)
    def _expand_nodes_for_fo_type(self, fo_type):
        for node in self.nodes_by_type[fo_type]:
            self._expand_node(node)
            self._define_node(node)
        self.expanded_fo_types.add(fo_type)

    def _rebuild_solver(self):
        self.solver = z3.Solver()
        self.solver.set("unsat_core", True, "core.minimize", False)
        self.solver_depth_assertions = 0

    def _ensure_quantifier_definitions(self, max_depth):
        for d in range(self.solver_depth_assertions, max_depth):
            self.solver.add(z3.PbEq([(self._var_for_quantifier(q, d), 1) for q in self._all_quantifiers()], 1))
        self.solver_depth_assertions = max(self.solver_depth_assertions, max_depth)

    def separate(self,
                 pos: Collection[int] = (),
                 neg: Collection[int] = (),
                 imp: Collection[Tuple[int, int]] = (),
                 soft_pos: Collection[int] = (),
                 soft_neg: Collection[int] = (),
                 soft_imp: Collection[Tuple[int, int]] = (),
                 max_depth = 1000000,
                 timer = UnlimitedTimer(),
                 matrix_timer = UnlimitedTimer(),
    ):
        self.prefixes = PrefixSolver(0, self.sort_indices, logic=self.logic)

        self.timer = timer
        #self.solver.push()

        self.solver_depth_assertions = 0
        self._ensure_quantifier_definitions(self.prefixes.depth)

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

        # we do not support soft constraints
        assert len(soft_pos + soft_neg + soft_imp) == 0
        # add soft constraints
        # for po in soft_pos:
        #     self.solver.add_soft(z3.Bool(f"v{po}"))
        # for n in soft_neg:
        #     self.solver.add_soft(z3.Not(z3.Bool(f"v{n}")))
        # for (a,b) in soft_imp:
        #     self.solver.add_soft(z3.Implies(z3.Bool(f"v{a}"), z3.Bool(f"v{b}")))

        try:
            while True:
                p = self.prefixes.get()
                if p is None:
                    if self.prefixes.depth == max_depth:
                        return None
                    self.prefixes = PrefixSolver(self.prefixes.depth + 1, self.sort_indices, logic=self.logic)
                    self._ensure_quantifier_definitions(self.prefixes.depth)
                    p = self.prefixes.get()
                if True or not prefix_is_redundant(p):
                    if not self.quiet:
                        print("Prefix:", " ".join([("∀" if is_forall else "∃")+f"{sort}." for (is_forall, sort) in p]))
                    c = self._check_prefix_build_matrix(p, matrix_timer, constraints, pos, neg, imp)
                    if c is not None:
                        # print(self.solver)
                        # print("Solution is",c)
                        return c
        finally:
            pass
            #self.solver.pop()

    def _filter_prefix(self, p):
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True

    def _assert_equalities(self, sorts):
        current_depth = len(sorts)
        a = []
        for fo_type in self.sort_root.types_for(sorts):
            if fo_type not in self.expanded_fo_types and self.fo_type_depths[fo_type] < current_depth:
                a.append(z3.Bool(f"T{fo_type}"))
        return a

    def _print(self, *args):
        if not self.quiet:
            print(*args)
    def _check_prefix_build_matrix(self, prefix, matrix_timer, constraints, pos, neg, imp):
        start = time.time()
        sorts_of_prefix = [s for (is_forall, s) in prefix]

        while True:
            # print("Attempting")
            assumptions = self._assert_equalities(sorts_of_prefix)
            assumptions.append(z3.Bool(f"D{len(prefix)}"))
            assumptions.extend([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
            assumptions.extend(constraints)

            # self.solver.push()
            # self.solver.add(z3.Bool(f"D{len(prefix)}"))
            # self.solver.push()
            # self.solver.add([self._var_for_quantifier(q,i) for i,q in enumerate(prefix)])
            # print(self.solver)
            self._print("checking...")
            print(f"Used {len(assumptions)} assumptions")
            #print(self.solver)
            result = self.timer.solver_check(self.solver, assumptions)

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
                    print("Generalizing prefix...")
                    #assumptions = self._assert_equalities(sorts_of_prefix)
                    # assumptions = self._assert_equalities([None] * len(prefix))
                    # assumptions.append(z3.Bool(f"D{len(prefix)}"))

                    final_core = []
                    initial_core = list(reversed(prefix_core_vars))
                    #initial_core = list(prefix_core_vars)
                    while len(initial_core) > 0:
                        print(final_core, [initial_core[0]], initial_core[1:])
                        assumptions = self._assert_equalities([s if False else None for i, s in enumerate(sorts_of_prefix)]) + [z3.Bool(f"D{len(prefix)}")] + constraints
                        r = self.timer.solver_check(self.solver, assumptions + final_core + initial_core[1:])
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
                    # print(f"Core depths {'+'.join(x.decl().name()[-1] for x in final_core)}")
                    print(final_core)
                    self.prefixes.add(final_core)
                    break
                else:
                    c = len(possible_expansions)
                    self._print("expanding", c, "fo-types")
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
                for (a,b) in imp:
                    formulas.append(z3.Implies(z3.Bool(f"v{a}"), z3.Bool(f"v{b}")))

                sat_formula = z3.And(formulas)
                # print("SAT Formula", sat_formula)
                # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))

                sig_with_bv = copy.deepcopy(self.sig)
                for i,(_, sort) in enumerate(prefix):
                    assert "x_"+str(i) not in sig_with_bv.constants
                    sig_with_bv.constants["x_"+str(i)] = sort

                concrete_models = {}
                for x in vars:
                    concrete_models[x] = self.collapsed.get_concrete(x)

                matrix = infer_matrix(concrete_models, sig_with_bv, sat_formula, self.quiet, self.timer)
                checker = z3.Solver()
                checker.add(sat_formula)
                for x, m in concrete_models.items():
                    checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
                if checker.check() != z3.sat:
                    raise RuntimeError("Incorrect matrix!")
                # print("Checker model", checker.model())
                # print("Sat formula was", sat_formula)
                return build_prefix_formula(prefix, matrix)
        else:
            assert False and "Error, z3 returned unknown"

# This has not been updated for the new interface
# if __name__ == "__main__":
#     from interpret import interpret
#     from parse import parse
#     import sys

#     if len(sys.argv) not in [1,2]:
#         print("Usage: python3 separate.py [file.fol]")
#         exit(1)

#     file = "problems/node_has_edge.fol" if len(sys.argv) == 1 else sys.argv[1]
#     (sig, axioms, conjectures, models) = interpret(parse(open(file).read()))

#     f = separate(models, sig, 6)
#     if f is not None:
#         print("Formula is:", f)
#     else:
#         print("No formula found.")
