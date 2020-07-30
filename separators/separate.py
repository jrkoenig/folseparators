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

from collections import defaultdict, Counter
import itertools, copy, time, sys, re, random, statistics, typing
from typing import Tuple, TypeVar, Iterable, FrozenSet, Union, Callable, Generator, Set, Optional, cast, Type, Collection, List, Dict, DefaultDict, Iterator, Any, Sequence

import z3

from .logic import Forall, Exists, Equal, Relation, And, Or, Not, Formula, Term, Var, Func, Model, Signature, rename_free_vars, free_vars, symbols
from .check import check, resolve_term
from .matrix import infer_matrix, K_function_unrolling
from .timer import Timer, UnlimitedTimer

QuantifierStr = Tuple[bool, str]

def collapse(model: Model, sig: Signature, assignment: Iterable[int]) -> str:
    mapping: Dict[int, int] = {}
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
        c = model.constants[const]
        assert c is not None
        consts.append(get_element(c))

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
        interp = model.relations[rel]
        collapsed_tuples = []
        for t, val in interp.items():
            if all(x in mapping for x in t) and val:
                collapsed_tuples.append(tuple(mapping[x] for x in t))
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
    def get_example(self, i: int) -> Tuple[int, Tuple[int, ...]]:
        return self.assignments[i]
    def __len__(self) -> int:
        return len(self.assignments)

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
        name_parts = [np for np in name_parts if np != '']
        first_letter, initials = name_parts[0][0], "".join(np[0] for np in name_parts)
        first_word, last_word = name_parts[0], name_parts[-1]
        yield from (suffix(x) for x in [first_letter, initials, first_word, last_word])
        yield from (suffix("V_"+x) for x in [first_letter, initials, first_word, last_word])
        # we need skip because the generators are all incremented together when there
        # is a collision, and if we didn't advance them differently they could always
        # collide as they advance in lockstep
        yield from (suffix(f"V_{i}_"+initials) for i in range(1, 1000000, skip))
    
    c: typing.Counter[int] = Counter(prefix)
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
    def size(self) -> int:
        return 1 + sum(c.size() for x in self.children for c in x)

class HybridSeparator(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = [], expt_flags: Set[str] = set()):
        self._sig = sig
        self._quiet = quiet
        self._logic = logic
        self._epr_wrt_formulas = epr_wrt_formulas
        self._separators: Dict[int, FixedHybridSeparator] = {}
        self._models: List[Model] = []
        self._expt_flags = expt_flags

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
            seed = random.randint(0,2 ** 64 - 1)
            h = FixedHybridSeparator(self._sig, clauses, self._quiet, self._logic, self._epr_wrt_formulas, seed, self._expt_flags)
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
    def __init__(self, sig: Signature, clauses: int, quiet: bool = False, logic: str = "fol", epr_wrt_formulas: List[Formula] = [], seed:Optional[int] = None, expt_flags: Set[str] = set()):
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

        self._var_presence_assertions_cache: Set[Tuple[int, ...]] = set()

        self._literal_upper_bound_vars: Dict[Tuple[Tuple[int, ...], int], int] = {}

        self._imp_constraint_cache: Set[Tuple[int, int]] = set()

        self._expt_flags = expt_flags

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
    def _var_less_var(self, sort: int, index: int) -> z3.ExprRef:
        return z3.Bool(f"L_{sort}_{index}")

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
            # TODO: add other logic restrictions here
            
            if 'limitquantifier2' in self._expt_flags:
                # Limit to two instances of any sort
                for sort in range(n_sorts):
                    self.solver.add(z3.Implies(self._depth_var(0, depth), z3.PbLe([(self._prefix_sort_var(0, sort, d),1) for d in range(depth)], 2)))
        self._highest_prefix[conjunct] = max(self._highest_prefix[conjunct], depth)

    def _make_node(self, model_i: int, inst: List[int]) -> InstNode:
        fo_type = self._collapse_cache.get(model_i, inst)
        c = InstNode(self._next_node_index, inst, fo_type, model_i, len(self._sig.sort_names))
        self._next_node_index += 1
        var = z3.Bool(f"v_{c.index}")
        d = len(c.instantiation)
        # At the right depth, this node is exactly the FO type
        self.solver.add(z3.Implies(self._depth_var(0, d), var == self._fo_type_var(c.fo_type)))
        # If the depth is greater, then (FO type) => node
        self.solver.add(z3.Implies(self._depth_greater_var(0, d),
                                    z3.Implies(self._fo_type_var(c.fo_type), var)))
        # If the depth is greater, and there are no literals with deeper variables, then !(FO type) => !node
        if 'neglookahead' in self._expt_flags:
            model = self._models[model_i]
            sort_list = [self._sig.sort_indices[model.sorts[e]] for e in c.instantiation]
            L_requirements = [self._var_less_var(sort, len([x for x in sort_list if x == sort])) for sort in range(len(self._sig.sort_names))]
            self.solver.add(z3.Implies(z3.And(self._depth_greater_var(0, d), *L_requirements, z3.Not(self._fo_type_var(c.fo_type))), z3.Not(var)))
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
            if 'nodecisionquorum' in self._expt_flags:
                # require the atom to not be used
                if 'decision_quorum' in symbols(self._atoms[atom]) or 'none' in symbols(self._atoms[atom]):
                   self.solver.add(z3.And(z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1}")),
                                          z3.Not(z3.Bool(f"y_{conjunct}_{clause}_{atom}_{0}"))))

        return z3.Bool(f"y_{conjunct}_{clause}_{atom}_{1 if polarity else 0}")


    def _var_presence_assertions(self, sort_list: List[int]) -> None:
        key = tuple(sort_list)
        if key in self._var_presence_assertions_cache:
            return
        else:
            self._var_presence_assertions_cache.add(key)

        depth = len(sort_list)
        assump = z3.And(self._depth_var(0, depth), *(self._prefix_sort_var(0, s, d) for d, s in enumerate(sort_list)))
        def literal_vars(atms: Iterable[int]) -> Iterable[z3.ExprRef]:
            return [self._literal_var(0, c, a, p) for c in range(self._clauses) for a in atms for p in [True, False]]
        atoms = self._all_atoms(sort_list)
            
        if 'neglookahead' in self._expt_flags:
            vs = prefix_var_names(self._sig, sort_list)
            atoms = self._all_atoms(sort_list)
            var_max: Dict[Tuple[str, int], int] = {}
            sort_max: List[int] = [1]*len(self._sig.sort_names)
            for v, sort in zip(vs, sort_list):
                var_max[(v, sort)] = sort_max[sort]
                sort_max[sort] += 1
            # Now var_max tells us ordinal of a variable for a sort. So x_0_1 should have value 2, etc.
            
            for sort in range(len(self._sig.sort_names)):
                atoms_by_slot: List[List[int]] = [[] for d in range(depth + 1)]
                for atom_index in atoms:
                    max_slot = 0
                    for v in free_vars(self._atoms[atom_index]):
                        max_slot = max(max_slot, var_max.get((v,sort), 0))
                    atoms_by_slot[max_slot].append(atom_index)
                for d in range(depth + 1):
                    higher_atoms = [a for dd in range(d+1, depth + 1) for a in atoms_by_slot[dd]]
                    self.solver.add(z3.Implies(z3.And(assump, *(z3.Not(x) for x in literal_vars(higher_atoms))), self._var_less_var(sort, d)))

        # also add constraint that there are at most 4 literals
        if 'matrixsize4' in self._expt_flags:
            self.solver.add(z3.Implies(assump, z3.PbLe([(x,1) for x in literal_vars(atoms)], 4)))
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

    def _literal_upper_bound_var(self, prefix: List[int], bound: int) -> z3.ExprRef:
        k = (tuple(prefix), bound)
        if k not in self._literal_upper_bound_vars:
            v = len(self._literal_upper_bound_vars)
            prefix_vars = [self._prefix_sort_var(0, sort, d) for (d, sort) in enumerate(prefix)]
            atoms = self._all_atoms(prefix)
            literal_vars = [(self._literal_var(0, cl, a, False), 1) for cl in range(self._clauses) for a in atoms] +\
                           [(self._literal_var(0, cl, a, True), 1) for cl in range(self._clauses) for a in atoms]
            b = z3.PbLe(literal_vars, bound)
            self.solver.add(z3.Implies(z3.And(z3.Bool(f"PbLe_{v}"), *prefix_vars), b))
            self._literal_upper_bound_vars[k] = v
        return z3.Bool(f"PbLe_{self._literal_upper_bound_vars[k]}")

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

    def _imp_constraint_var(self, i: int, j:int) -> z3.ExprRef:
        v = z3.Bool(f"Imp_{i}_{j}")
        if (i,j) not in self._imp_constraint_cache:
            self.solver.add(z3.Implies(v, z3.Implies(self._root_var(i, 0), self._root_var(j, 0))))
            self._imp_constraint_cache.add((i,j))
        return v
    def _constraint_assumptions(self, constraints: List[Constraint]) -> Iterator[z3.ExprRef]:
        for const in constraints:
            if isinstance(const, Pos):
                yield self._root_var(const.i, 0)
            if isinstance(const, Neg):
                yield z3.Not(self._root_var(const.i, 0))
            if isinstance(const, Imp):
                yield self._imp_constraint_var(const.i, const.j)
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
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[(c.i, 0)].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded + in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Neg):
                if root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[(c.i,0)], False)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[(c.i, 0)].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded - in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Imp):
                if root_node_value(c.i) and not root_node_value(c.j):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[(c.i,0)], False)
                    expand_to_prove(self._node_roots[(c.j,0)], True)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[(c.i, 0)].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded x-> in {c.i}, {s}/{max}")
                        s = self._node_roots[(c.j, 0)].size()
                        max = sum(len(self._models[c.j].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded ->x in {c.j}, {s}/{max}")
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
                    break
                else: assert False
                # candidate matrix is final and remaining, which now lacks `a`
                candidate_matrix = [f+r for f,r in zip(final_matrix, remaining_matrix)]

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
        upper = sum(len(cl) for cl in matrix)
        lower = 0

        while True:
            assert lower <= upper
            if lower == upper:
                break
            k = (upper+lower) // 2
            bound = self._literal_upper_bound_var([sort for (is_forall, sort) in prefix], k)
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
                    print(f"Matrix wasn't valid; expanded nodes: {self._next_node_index}/{sum(len(model.elems) ** d for model in self._models for d in range(len(prefix)+1))}")
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
        if 'showconstraints' in self._expt_flags:
            s = ', '.join([(f"+{c.i}" if isinstance(c, Pos) else f"-{c.i}" if isinstance(c, Neg) else f"{c.i}->{c.j}" if isinstance(c, Imp) else '') for c in constraints])
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
                
                self._var_presence_assertions([q[1] for q in prefix])
                # formula wasn't correct, but we expanded some nodes in the tree to show the solver why it was wrong. go back up and try again
                print(f"expanded nodes: {self._next_node_index}/{sum(len(model.elems) ** d for model in self._models for d in range(depth+1))}")
                # Assume the same prefix on the next iteration, to help by focusing the solver
                prefix_assumptions = self._prefix_assumptions(prefix)
            else:
                print(self.solver)
                assert False # z3 should always return SAT/UNSAT on propositional formula
        
def _decompose(f: Formula) -> Tuple[List[Tuple[bool, str, str]], List[List[Formula]]]:
    prefix: List[Tuple[bool, str, str]] = []
    while isinstance(f, (Forall, Exists)):
        is_forall = isinstance(f, Forall)
        prefix.append((is_forall, f.sort, f.var))
        f = f.f
    clauses: List[List[Formula]] = []
    if isinstance(f, And):
        for c in f.c:
            if isinstance(c, Or):
                clauses.append(c.c)
            else:
                clauses.append([c])
    elif isinstance(f, Or):
        clauses.append(f.c)
    else:
        clauses.append([f])
    return prefix, clauses

def successor_formula(s: Signature, f: Formula) -> Iterable[Formula]:
    prefix, clauses = _decompose(f)

    def with_prefix(matrix: Formula) -> Formula:
        f = matrix
        for (is_forall, sort, var) in reversed(prefix):
            f = (Forall if is_forall else Exists)(var, sort, f)
        return f

    atoms = atoms_of(s, [(var, sort) for (is_forall, sort, var) in prefix])

    for atom in atoms:
        for clause_ind in range(len(clauses)):
            if atom in clauses[clause_ind] or Not(atom) in clauses[clause_ind]:
                continue
            new_clauses_p = And([Or(cl if i != clause_ind else cl + [atom]) for i, cl in enumerate(clauses)])
            new_clauses_n = And([Or(cl if i != clause_ind else cl + [Not(atom)]) for i, cl in enumerate(clauses)])
            yield with_prefix(new_clauses_p)
            yield with_prefix(new_clauses_n)
            
def predecessor_formula(s: Signature, f: Formula) -> Iterable[Formula]:
    prefix, clauses = _decompose(f)
    
    def with_prefix(matrix: Formula) -> Formula:
        f = matrix
        for (is_forall, sort, var) in reversed(prefix):
            f = (Forall if is_forall else Exists)(var, sort, f)
        return f
    
    for clause_ind in range(len(clauses)):
        for literal_ind in range(len(clauses[clause_ind])):
            new_clauses = And([Or(cl if i != clause_ind else cl[:literal_ind] + cl[literal_ind+1:]) for i, cl in enumerate(clauses)])
            yield with_prefix(new_clauses)

### PARTIAL SEPARATION: ###

Assumptions = Dict[int, int]
class PartialModel(object):
    '''Represents additional information about a (possibly) partial model.
    
    In a judgement M,\sigma |- p, the partial model represents the M,\sigma part. Thus
    it captures both the uncertainty in the partial model as well as the quantified
    variables. Each uncertainity is a 'fact'. We have facts for constants, relations and
    functions applied to specific arugments, and quantified variables. Each fact gets an
    index. The `rels`, `funcs` and `consts` fields give the fact index for a specific
    combination of relation/function/const/var and arguments (if applicable).'''
    def __init__(self, m: Model, i: int = -1):
        self.index = i
        self.model = m
        self.model.relations
        self.n_facts = 0
        self.consts: Dict[str, int] = {}
        self.rels: Dict[Tuple[Any, ...], int] = {} # keys are relation with element ids, i.e. ('r', 2, 4)
        self.funcs: Dict[Tuple[Any, ...], int] = {} # keys are same as above ('f', 4)
        self.qvar_sorts: Dict[str, int] = {}
        self.fact_domains: Dict[int, List[int]] = {}
        self.base_facts = -1
        self._compute_facts()
    def _next_fact(self, domain: List[int]) -> int:
        v = self.n_facts
        self.fact_domains[v] = domain
        self.n_facts += 1
        return v
    def _compute_facts(self) -> None:
        m = self.model
        sig = self.model.sig
        for (c, c_interp) in m.constants.items():
            if c_interp is None:
                sort = sig.constants[c]
                self.consts[c] = self._next_fact(m.elems_of_sort[sort])
        for (r, r_interp) in m.relations.items():
            for t in itertools.product(*(m.elems_of_sort[sort] for sort in sig.relations[r])):
                if t not in r_interp:
                    self.rels[(r, *t)] = self._next_fact([0,1])
        for (f, f_interp) in m.functions.items():
            result_sort = sig.functions[f][1]
            for t in itertools.product(*(m.elems_of_sort[sort] for sort in sig.functions[f][0])):
                if t not in f_interp:
                    self.funcs[(f, *t)] = self._next_fact(m.elems_of_sort[result_sort])
        self.base_facts = self.n_facts

    def add_qvar(self, name: str, sort: int) -> None:
        assert name not in self.consts and self.model.sig.is_free_name(name)
        self.qvar_sorts[name] = sort
        self.consts[name] = self._next_fact(self.model.elems_of_sort_index[sort])
        
    def domain(self, fact: int) -> List[int]:
        return self.fact_domains.get(fact, [])

    def eval_atomic(self, atomic: Formula, assumptions: Assumptions) -> Union[bool, Tuple[Assumptions, Assumptions]]:
        '''Given an atomic formula (r(_,_) or _=_), return whether the value is definitely True, False or uncertain.
        
        If `atomic` has a uniform value in all completions described by `assumptions`, return that value. Otherwise,
        return a tuple consisting of assumptions that make it true, and assumptions that make it false. These
        are not necessarily guaranteed to be minimal. The always represent subsets of the assumptions completion set
        (i.e. they always include all of the provided assumptions, and add more). Neither will never be exactly
        the given assumptions as this would mean the value is definite.'''
        can_be_false = False
        false_assumptions = {}
        can_be_true = False
        true_assumptions = {}
        def definite(asmpt: Assumptions, value: bool) -> None:
            '''Under `asmpt`, the atomic formula definitely has truth `value`.'''
            nonlocal can_be_false, can_be_true, true_assumptions, false_assumptions
            if value:
                can_be_true = True
                true_assumptions = asmpt
            else:
                can_be_false = True
                false_assumptions = asmpt

        if isinstance(atomic, Relation):
            rinterp = self.model.relations[atomic.rel]
            for (vs, asmpt) in self._eval_term_tuple(tuple(atomic.args), assumptions):
                if (atomic.rel, *vs) in self.rels:
                    # value of relation could be uncertain
                    fact = self.rels[(atomic.rel, *vs)]
                    if fact in asmpt:
                        # it isn't uncertain
                        definite(asmpt, asmpt[fact] != 0)
                    else:
                        return ({**asmpt, fact: 1}, {**asmpt, fact: 0})
                else:
                    # the model has a definite value for this relation
                    definite(asmpt, rinterp[vs])
                # early out if we find both values
                if can_be_true and can_be_false: 
                    return (true_assumptions, false_assumptions)
            # we now filled in can_be_T/F, see below
        elif isinstance(atomic, Equal):
            for ((a, b), asmpt) in self._eval_term_tuple(tuple(atomic.args), assumptions):
                definite(asmpt, a == b)
                if can_be_true and can_be_false: 
                    return (true_assumptions, false_assumptions)
        else:
            assert False and "expected an atomic formula"
        # After either case, return the definite value
        assert can_be_true != can_be_false
        return can_be_true

    def _eval_term_tuple(self, ts: Tuple[Term, ...], a: Assumptions) ->  Iterator[Tuple[Tuple[int, ...], Assumptions]]:
        if len(ts) == 0:
            yield ((), a)
        else:
            t, rest = ts[0], ts[1:]
            for (v, new_a) in self._eval_term(t, a):
                for (vs, result_a) in self._eval_term_tuple(rest, new_a):
                    yield ((v, *vs), result_a)

    def _eval_term(self, t: Term, a: Assumptions) -> Iterator[Tuple[int, Assumptions]]:
        if isinstance(t, Var):
            if t.var in self.consts:
                fact_index = self.consts[t.var]
                if fact_index in a and a[fact_index] != -1:
                    yield (a[fact_index], a) # assumptions define the var
                else:
                    if t.var in self.qvar_sorts:
                        sort = self.qvar_sorts[t.var]
                    else:
                        sort = self.model.sig.sort_indices[self.model.sig.constants[t.var]]
                    elems = self.model.elems_of_sort_index[sort]
                    for e in elems:
                        yield (e, {**a, fact_index: e})
            else:
                v = self.model.constants[t.var] 
                assert v is not None # if the model doesn't define t.var, it should be in self.consts
                yield (v, a)
        elif isinstance(t, Func):
            for (args, new_a) in self._eval_term_tuple(tuple(t.args), a):
                if (t.f, *args) in self.funcs:
                    fact_index = self.funcs[(t.f, *args)]
                    if fact_index in a:
                        yield (a[fact_index], a)
                    else:
                        sort = self.model.sig.sort_indices[self.model.sig.functions[t.f][1]]
                        elems = self.model.elems_of_sort_index[sort]
                        for e in elems:
                            yield (e, {**a, fact_index: e})
                else:
                    finterp = self.model.functions[t.f]
                    assert args in finterp # expect the model to define f(*args)
                    yield (finterp[args], new_a)
        else:
            assert False
    
class Completion(object):
    '''Represents a completion of a particular partial model via a set of assumptions.
    
    Each entry in `self.assumptions` maps a fact to a particular value for that fact. For 
    relations, this is 0 or 1 for false or true. For constants or functions, this is the
    model element id. `validate()` can be used to check well-sortedness of the assumptions.'''
    __slots__ = ['model', 'assumptions']
    def __init__(self, pm: PartialModel, assumptions: Assumptions = {}):
        '''Constructs a completion for a partial model. By default, the completion represents
        the entire set of all completions in `pm`.'''
        self.model = pm
        self.assumptions: Assumptions = assumptions if len(assumptions) > 0 else {}
    def with_fact(self, fact: int, value: int) -> 'Completion':
        c = Completion(self.model)
        c.assumptions = {**self.assumptions, fact: value}
        return c
    # wrapper around the method from `PartialModel`
    def eval_atomic(self, f:Formula) -> Union[bool, Tuple[Assumptions, Assumptions]]:
        return self.model.eval_atomic(f, self.assumptions)


    def __str__(self) -> str:
        res = f"@{self.model.index}["
        def N(i: int) -> str: return self.model.model.names[i]
        for (fact, value) in self.assumptions.items():
            for (c, f) in self.model.consts.items():
                if f == fact:
                    res += f"{c}={self.model.model.names[value] if value != -1 else '?'} "
                    break
            for (r, f) in self.model.rels.items():
                if f == fact:
                    res += f"{r[0]}({','.join(map(N, r[1:]))})={'true' if value else 'false'} "
                    break
            for (fn, f) in self.model.funcs.items():
                if f == fact:
                    res += f"{fn[0]}({','.join(map(N, fn[1:]))})={N(value)} "
                    break
        return res+ "]"

    def validate(self) -> None:
        '''Raises an exception if the assumptions are not well formed wrt the underlying model.'''
        for (fact, val) in self.assumptions.items():
            if fact >= self.model.n_facts:
                raise RuntimeError("Fact is out of bounds")
        for (const, fact) in self.model.consts.items():
            if fact in self.assumptions:
                if self.assumptions[fact] == -1: continue
                sort: str = self.model.model.sig.sort_names[self.model.qvar_sorts[const]] if const in self.model.qvar_sorts else self.model.model.sig.constants[const]
                if self.model.model.sorts[self.assumptions[fact]] != sort:
                    raise RuntimeError("Const/var fact does not have correct sort")
        for (rel_w_args, fact) in self.model.rels.items():
            if fact in self.assumptions:
                if self.assumptions[fact] not in [0,1]:
                    raise RuntimeError("Relation fact is not boolean")
        for ((f, *args), fact) in self.model.funcs.items():
            if fact in self.assumptions:
                sort = self.model.model.sig.functions[f][1]
                if self.model.model.sorts[self.assumptions[fact]] != sort:
                    raise RuntimeError("Function fact does not have correct sort")

def _assumptions_without(a: Assumptions, fact: int) -> Assumptions:
    if fact in a:
        aa = a.copy()
        del aa[fact]
        return aa
    return a
def _assumptions_opt_without(a: Optional[Assumptions], fact: int) -> Optional[Assumptions]:
    return _assumptions_without(a, fact) if a is not None else None

def _choose_split_fact_mode(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    options: typing.Counter[int] = Counter()
    for a in choices:
        for k, v in a.items():
            if k not in base or base[k] == -1:
                options[k] += 1
    for k, count in sorted(options.items(), key = lambda x: x[1], reverse=True):
        return k
    return None

def _choose_split_fact_anti_mode(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    options: typing.Counter[int] = Counter()
    for a in choices:
        for k, v in a.items():
            if k not in base or base[k] == -1:
                options[k] += 1
    for k, count in sorted(options.items(), key = lambda x: x[1]):
        return k
    return None

def _choose_split_domain(base_completion: Completion, split_fact: int, choices: Sequence[Assumptions]) -> List[int]:
    base = base_completion.assumptions
    value_options: typing.Counter[int] = Counter()
    for a in choices:
        if split_fact in a and a[split_fact] != -1:
            value_options[a[split_fact]] += 1
    
    domain = [v for v, count in sorted(value_options.items(), key = lambda x: x[1], reverse = True)]
    for v in base_completion.model.domain(split_fact):
        if v not in domain:
            domain.append(v)
    #domain.reverse()
    return domain
    


def _choose_split_fact_orig(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    for a in choices:
        for k, v in a.items():
            if k not in base or base[k] == -1:
                return k
    return None


def _choose_split_fact_smallest(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    sets: List[List[int]] = []
    for a in choices:
        sets.append([])
        for k, v in a.items():
            if k not in base or base[k] == -1:
                sets[-1].append(k)
    sets.sort(key = len)
    for s in sets:
        if len(s) > 0:
            return s[0]
    return None


def _choose_split_fact_largest(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    sets: List[List[int]] = []
    for a in choices:
        sets.append([])
        for k, v in a.items():
            if k not in base or base[k] == -1:
                sets[-1].append(k)
    sets.sort(key = len)
    for s in reversed(sets):
        if len(s) > 0:
            return s[0]
    return None

def _choose_split_fact_reverse(base: Assumptions, choices: Sequence[Assumptions]) -> Optional[int]:
    for a in reversed(choices):
        for k, v in a.items():
            if k not in base or base[k] == -1:
                return k
    return None

_choose_split_fact = _choose_split_fact_mode

def _random_completion(M: Completion, qvars: Sequence[int], R: random.Random) -> Completion:
    a = dict(M.assumptions)
    for f in itertools.chain(range(M.model.base_facts), qvars):
        if f not in M.assumptions or M.assumptions[f] == -1:
            a[f] = R.choice(M.model.domain(f))
    return Completion(M.model, a)

def _F_eval_existential(M: Completion, qvar: int, domain: Sequence[int], p: Formula, inner_polarity: bool) -> Optional[Assumptions]:
    # First try each element in order. If any work, we're done.
    assumptions = []
    for v in domain:
        assert qvar not in M.assumptions
        r = _F_eval(M.with_fact(qvar, v), p, inner_polarity)
        if r is None:
            return None
        assumptions.append(_assumptions_without(r, qvar))
    domain_next = []
    for v in domain:
        assert qvar not in M.assumptions
        r = _F_eval(M.with_fact(qvar, v), p, not inner_polarity)
        if r is not None:
            assumptions.append(_assumptions_without(r, qvar))
            domain_next.append(v)
        # else, this choice of qvar is always false, so we can drop it from further consideration
    if len(domain_next) == 0:
        return M.assumptions

    fact = _choose_split_fact(M.assumptions, assumptions)
    print(M, qvar, fact, domain_next, inner_polarity, assumptions)
    assert fact is not None and fact != qvar
    for v in M.model.domain(fact):
        r = _F_eval_existential(M.with_fact(fact, v), qvar, domain_next, p, inner_polarity)
        if r is not None:
            return r
    return None
    
def _F_eval_or(M: Completion, ps: Sequence[Formula], inner_polarity: bool) -> Optional[Assumptions]:
    # First try each disjunct in order. If any are true, we're done.
    assumptions = []
    for p in ps:
        r = _F_eval(M, p, inner_polarity)
        if r is None:
            return None
        assumptions.append(r)
    ps_next = []
    for p in ps:
        r = _F_eval(M, p, not inner_polarity)
        if r is not None:
            assumptions.append(r)
            ps_next.append(p)
        # else, this conjunct is always false, so we can drop it from further consideration
    
    if len(ps_next) == 0:
        return M.assumptions

    # Otherwise, choose a fact to split on and recuse
    fact = _choose_split_fact(M.assumptions, assumptions)
    assert fact is not None
    for v in M.model.domain(fact):
        r = _F_eval_or(M.with_fact(fact, v), ps_next, inner_polarity)
        if r is not None:
            return r
    return None

def _F_eval(M: Completion, p: Formula, polarity: bool) -> Optional[Assumptions]:
    '''Determine whether M |- p (if polarity) or M |- ~p (if !polarity). Return a witness otherwise.

    Evaluate a formula in a partial model, and determine if p (or ~p) satisfies M. If it doesn't satisfy,
    return a (possibly partial) completion that is a witness to the negation. So if _F_eval(M, p, True)
    returns a witness, it will be a completion M' such that M' |- ~p. Notice that the witness will be an
    underapproximation of the set of counterexample completions (i.e. every completion in the return value
    must be uniformly the opposite of the desired polarity).
    '''
    # For testing, first make sure we don't mess up
    #M.validate()
    #print("Trace: ", M,"+" if polarity else "-", p)
    if isinstance(p, Forall):
        # first ensure the q_var is known
        if p.var not in M.model.consts:
            M.model.add_qvar(p.var, M.model.model.sig.sort_indices[p.sort])
        qvar = M.model.consts[p.var]
        if polarity:
            # we need to remove any assumptions about the qvar that we implicitly
            # set to ? in this recursive call.
            return _assumptions_opt_without(_F_eval(M, p.f, True), qvar)
        else:
            return _F_eval_existential(M, qvar, M.model.domain(qvar), p.f, False)
    elif isinstance(p, Exists):
        # first ensure the q_var is known
        if p.var not in M.model.consts:
            M.model.add_qvar(p.var, M.model.model.sig.sort_indices[p.sort])
        qvar = M.model.consts[p.var]
        if polarity:
            return _F_eval_existential(M, qvar, M.model.domain(qvar), p.f, True)
        else:
            return _assumptions_opt_without(_F_eval(M, p.f, False), qvar)
    elif isinstance(p, And):
        if polarity:
            for c in p.c:
                r = _F_eval(M, c, True)
                if r is not None: return r
            return None
        else:
            return _F_eval_or(M, p.c, False)
    elif isinstance(p, Or):
        if polarity:
            return _F_eval_or(M, p.c, True)
        else:
            for c in p.c:
                r = _F_eval(M, c, False)
                if r is not None: return r
            return None
    elif isinstance(p, Not):
        return _F_eval(M, p.f, not polarity)
    else:
        # Assume it's atomic
        v = M.eval_atomic(p)
        if isinstance(v, bool):
            # If v doesn't match polarity, then we don't need to add any more assumptions
            return None if v == polarity else M.assumptions
        # Value is mixed: if we're looking for true return the false assumptions, and vice versa
        return v[1 if polarity else 0]

def check_partial(c: Completion, f: Formula) -> bool:
    #print("Beginning eval", f,"...")
    return _F_eval(c, f, True) is None

T = typing.TypeVar('T')
def shuffled(l: Sequence[T]) -> Sequence[T]: return random.sample(l, len(l))

class CNode(object):
    def __init__(self, loc: int, i: int, c: Completion, polarity: bool) -> None:
        self.location = loc
        self.index = i
        self.var = z3.Bool(f'v_{i}')
        self.comp = c
        self.polarity = polarity
    def __str__(self) -> str:
        return f"M + {self.comp} |- {'' if self.polarity else '~'}cl"

def _I(x: int) -> str: return "~" * (2*x)
SATUpdater = Callable[[int], None]
Witness = Tuple[Optional[Assumptions], SATUpdater]

class PartialSeparator(object):
    '''Partial separator for a given prefix length and number of clauses.
    
    API is add_model(Model, is_positive) and separate() -> Optional[Formula]. This
    class does not support removing constraints or changing the number of quantifiers
    or clauses after construction. For a more general separator, see
    `DiagonalPartialSeparator`.'''
    def __init__(self, sig: Signature, prefix_len: int, clauses: int, logic: str = 'fol'):
        self._sig = sig
        self._logic = logic
        assert self._logic in ['fol', 'universal']
        self.n_sorts = len(sig.sort_names)
        self.n_clauses = clauses
        self.n_quantifiers = prefix_len
        self.solver = z3.Solver()
        self.roots: List[CNode] = []
        self.polarities: List[bool] = []
        self.next_node_index = 0
        self.nodes: Dict[Tuple[int, ...], CNode] = {}
        self._random_gen = random.Random(47943452)
        
        
        # Caches
        self._splits: Set[Tuple[int, int]] = set() # (node_index, split_fact)
        self._cache_literal_var: Dict[Tuple[int, int, bool], z3.ExprRef] = {}
        self._defined_neg_clauses: Set[int] = set()
        # pretend we have a prefix big enough for up to N variables of each sort
        self.prefix_var_names = [prefix_var_names(self._sig, [s] * self.n_quantifiers) for s in range(self.n_sorts)]
        self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for sort, vs in enumerate(self.prefix_var_names) for v in vs]))
        self._atom_qvar_requirements: List[List[int]] = []
        self._cache_vars()
        self._constrain_vars()
        self.solver.check()
        self.solution = self.solver.model()
        self.solution_prefix, self.solution_formula = self._extract_formula()
        
    def add_model(self, m: Model, positive: bool) -> None:
        pm = PartialModel(m, len(self.roots))
        for (sort, vs) in enumerate(self.prefix_var_names):
            for v in vs:
                pm.add_qvar(v, sort)
        n = self._lookup(Completion(pm), -self.n_quantifiers, positive)
        self.roots.append(n)
        self.solver.add(n.var)

    def separate(self, timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        with timer:
            while True:
                # print("Checking hardcoded solution")
                # s = z3.Solver()
                # for constraint in self.solver.assertions():
                #     s.add(constraint)
                # assumptions = [self._prefix_quant_var(-2), self._prefix_sort_var(-2, 0),self._prefix_quant_var(-1), self._prefix_sort_var(-1, 1)]
                # for atom_id, atom in enumerate(self.atoms):
                #     for pol in [True, False]:
                #         if (atom_id, pol) in [(28, False), (9, True)]:
                #             assumptions += [self._literal_var(0, atom_id, pol)]
                #         else:
                #             assumptions += [z3.Not(self._literal_var(0, atom_id, pol))]
                # r = s.check(*assumptions)
                # print("Hardcoded? =", r)
                # if r == z3.unsat:
                #     for n in reversed(range(len(self.solver.assertions()) + 1)):
                #         s2 = z3.Solver()
                #         for constraint in self.solver.assertions()[:n]:
                #             s2.add(constraint)
                #         if s2.check(*assumptions) == z3.sat:
                #             print("didn't need", self.solver.assertions()[n])
                #             break
                #     for constraint in self.solver.assertions():
                #         print(constraint)
                #     assert False
                # print("Finished hardcoded.")
            
                # Force our hardcoded solution:
                # self.solver.add(z3.And(assumptions))
                
                result = timer.solver_check(self.solver)
                if result == z3.unsat:
                    return None
                assert result == z3.sat
                self.solution = self.solver.model()
                if self._check_validity():
                    f: Formula = And([Or([a if t else Not(a) for (t, a, i) in clause]) for clause in self.solution_formula[:]])
                    for is_forall, sort, name in reversed(self.solution_prefix):
                        f = (Forall if is_forall else Exists)(name, self._sig.sort_names[sort], f)
                    return f
                # otherwise, _check_validity has added constraints
    
    def _literal_var(self, clause: int, atom_index: int, polarity: bool) -> z3.ExprRef:
        '''Var represents atom with polarity is in a clause'''
        #assert 0 <= clause < self.n_clauses and 0 <= atom_index < len(self.atoms)
        return self._cache_literal_var[(clause, atom_index, polarity)]
    def _prefix_quant_var(self, loc: int) -> z3.ExprRef:
        '''Var represents whether loc (negative indexing) is a forall (true) or exists (false).'''
        assert 0 < -loc <= self.n_quantifiers
        return z3.Bool(f"AE_{-loc}")
    def _prefix_sort_var(self, loc: int, sort: int) -> z3.ExprRef:
        '''Var is true if loc (negative indexing) is sort. Exactly one is true per index.'''
        assert 0 < -loc <= self.n_quantifiers and 0 <= sort < len(self._sig.sort_names)
        return z3.Bool(f"Q_{-loc}_{sort}")
    def _prefix_qvar_var(self, sort: int, count: int) -> z3.ExprRef:
        '''Var is true whenever there are at least count qvars of sort'''
        assert 0 < count <= self.n_quantifiers and 0 <= sort < len(self._sig.sort_names)
        return z3.Bool(f"x_{sort}_{count}")
    
    def _cache_vars(self) -> None:
        for cl in range(self.n_clauses):
            for a in range(len(self.atoms)):
                for p in [True, False]:
                    self._cache_literal_var[(cl, a, p)] = z3.Bool(f"L_{cl}_{a}_{1 if p else 0}")

    def _constrain_vars(self) -> None:
        locs = range(-self.n_quantifiers, 0)
        # Each atom can appear positively or negatively but not both
        for j in range(self.n_clauses):
            for (i, a) in enumerate(self.atoms):
                self.solver.add(z3.Or(z3.Not(self._literal_var(j, i, True)),
                                      z3.Not(self._literal_var(j, i, False))))
                # print(a,"===", self._literal_var(j, i, True), f"({i})")
                # print(Not(a),"===", self._literal_var(j, i, False), f"({i})")
        # Exactly one sort per quantifier
        for d in locs:
            self.solver.add(z3.PbEq([(self._prefix_sort_var(d, s), 1) for s in range(self.n_sorts)], 1))
            if self._logic == 'universal':
                self.solver.add(self._prefix_quant_var(d))
            
        for d in range(-self.n_quantifiers, -1):
            for i,j in itertools.combinations(reversed(range(self.n_sorts)), 2):
                # Prevent adjacent universals unless their sorts are in non-strict increasing order
                A_i_d = z3.And(self._prefix_sort_var(d, i), self._prefix_quant_var(d))
                A_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), self._prefix_quant_var(d + 1))
                self.solver.add(z3.Not(z3.And(A_i_d, A_j_dp1)))
                # Same for existentials
                E_i_d = z3.And(self._prefix_sort_var(d, i), z3.Not(self._prefix_quant_var(d)))
                E_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), z3.Not(self._prefix_quant_var(d + 1)))
                self.solver.add(z3.Not(z3.And(E_i_d, E_j_dp1)))
                
        # Each x_{i}_{sort} is true when there are at least i quantified variables of sort
        for count in range(1, 1 + self.n_quantifiers):
            for s in range(self.n_sorts):
                self.solver.add(self._prefix_qvar_var(s, count) ==
                                  z3.PbGe([(self._prefix_sort_var(loc, s), 1) for loc in locs], count))
        # Each literal can only be present if there are a certain number of sorted quantified variables.
        # For example, r(__x_2_1, __x_0_0) requires 2 qvars of sort 2 and 1 qvar of sort 0, as otherwise
        # the variables such as __x_2_1 don't exist.
        prefix_var_lookup = {}
        for sort, vs in enumerate(self.prefix_var_names):
            for i, v in enumerate(vs):
                prefix_var_lookup[v] = (sort, i)
        for atom_id, atom in enumerate(self.atoms):
            requirements = [0] * self.n_sorts # what is the count of each sort required?
            for v in vars_of(atom):
                if v not in prefix_var_lookup: continue # skip constants from signature
                sort, i = prefix_var_lookup[v]
                requirements[sort] = max(requirements[sort], i + 1)
            self._atom_qvar_requirements.append(requirements)
            for cl in range(self.n_clauses):
                reqs = z3.And([self._prefix_qvar_var(s, c) for (s, c) in enumerate(requirements) if c > 0])
                for pol in [True, False]:
                    self.solver.add(z3.Implies(self._literal_var(cl, atom_id, pol), reqs))

    def _valid_atoms(self, sorts: Sequence[int]) -> Iterable[Tuple[int, Formula]]:
        var_counts = [0] * self.n_sorts
        for s in sorts:
            var_counts[s] += 1
        for atom_id, atom in enumerate(self.atoms):
            if all(i <= j for i,j in zip(self._atom_qvar_requirements[atom_id], var_counts)):
                yield atom_id, atom

    def _lookup(self, M: Completion, loc: int, polarity: bool) -> CNode:
        a = [x for kv in sorted(M.assumptions.items()) for x in kv]
        key = (loc, 1 if polarity else 0, M.model.index, *a)
        if key not in self.nodes:
            n = CNode(loc, self.next_node_index, M, polarity)
            self.next_node_index += 1
            self.nodes[key] = n
        return self.nodes[key]

    def _V(self, M: Completion, loc: int, polarity: bool) -> z3.ExprRef:
        return self._lookup(M, loc, polarity).var

    def _split(self, M: Completion, loc: int, polarity: bool, f: int) -> None:
        n = self._lookup(M, loc, polarity)
        if (n.index, f) not in self._splits:
            subterms = []
            for v in n.comp.model.domain(f):
                subterms.append(self._V(M.with_fact(f,v), loc, polarity))
            self.solver.add(n.var == z3.And(subterms))
            self._splits.add((n.index, f))
        
    def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[Tuple[bool, Formula, int]]]]:
        prefix = []
        next_var_index = [0] * self.n_sorts
        for loc in range(-self.n_quantifiers, 0):
            is_forall = True if self.solution[self._prefix_quant_var(loc)] else False
            for s in range(self.n_sorts):
                if z3.is_true(self.solution.eval(self._prefix_sort_var(loc, s))):
                    sort = s
                    break
            else: assert False # should be exactly one var true!
            name = self.prefix_var_names[sort][next_var_index[sort]]
            next_var_index[sort] += 1
            prefix.append((is_forall, sort, name))
        phi = []
        for j in range(self.n_clauses):
            cl = []
            for (i, a) in enumerate(self.atoms):
                for p in [True, False]:
                    if z3.is_true(self.solution.eval(self._literal_var(j, i, p))):
                        cl.append((p, a, i))
            phi.append(cl)
        return (prefix,phi)

    def _check_validity(self) -> bool:
        self.solution_prefix, self.solution_formula = self._extract_formula()
        pp_matrix = " & ".join("(" + " | ".join(str(l) if p else str(Not(l)) for (p, l, i) in cl) + ")" for cl in self.solution_formula)
        print("Checking candidate", " ".join(f"{'A' if is_forall else 'E'}{var}." for (is_forall, sort, var) in self.solution_prefix), pp_matrix)
        #print("Solution: ", self.solution)
        for i, root in enumerate(self.roots):
            r = self._E(root.comp, root.location, root.polarity)
            if r[0] is not None:
                r[1](0)
                print(f"Elaborated in a {root.polarity} structure")
                # print("Finished updating constraints, which are now:\n  ---  \n")
                # for c in self.solver.assertions():
                #     print(c)
                # print("\n  ---  \n")
                # swap constraint to front
                self.roots = [root] + self.roots[:i] + self.roots[i+1:]
                # print("New solver is", self.solver)
                return False
        return True

    
    def _E(self, M: Completion, loc: int, polarity: bool) -> Witness:
        if loc > 0:
            literals = [(i, t, (a if t else Not(a))) for (t, a, i) in self.solution_formula[loc - 1]]
            return self._E_cl_v2(M, loc, polarity, literals)
        elif loc == 0:
            return self._E_phi_v2(M, loc, polarity, list(range(1, 1+self.n_clauses)), [])
        elif loc < 0:
            qvar = M.model.consts[self.solution_prefix[loc + self.n_quantifiers][2]]
            return self._E_ae_v2(M, loc, polarity, M.model.domain(qvar), [])
        else: assert False

    def _E_cl(self, M: Completion, loc: int, polarity: bool, literals: List[Tuple[int, bool, Formula]]) -> Witness:
        M.validate()
        if polarity:
            assumptions = []
            for (p_i, p_pol, p) in literals:
                r_literal = _F_eval(M, p, polarity)
                if r_literal is None:
                    def prove_literal(i: int) -> None:
                        v = self._V(M, loc, polarity)
                        self.solver.add(z3.Implies(self._literal_var(loc - 1, p_i, p_pol), v))
                        print(f"{_I(i)} Proving {M} {loc} {polarity} with literal {p}")
                        print(f"{_I(i)}   (i.e. {z3.Implies(self._literal_var(loc - 1, p_i, p_pol), v)}")
                    return (None, prove_literal)
                # print(f"Got {r_literal} from {M.assumptions} ({M})")
                assumptions.append(r_literal)
            ps_next = []
            for (p_i, p_pol, p) in literals:
                r_literal = _F_eval(M, p, not polarity)
                if r_literal is not None:
                    assumptions.append(r_literal)
                    ps_next.append((p_i, p_pol, p))
            if len(ps_next) == 0:
                # This means that all of the literals are false.
                def prove_neg(i: int) -> None:
                    v = self._V(M, loc, polarity)
                    ante = []
                    # (~L[0] \/ M |- ~l[0]) /\
                    # ...
                    # (~L[n] \/ M |- ~l[n]) -> ~(M |- cl)
                    for (atom_id, atom) in enumerate(self.atoms):
                        for pol in [True, False]:
                            truth = _F_eval(M, atom, not pol)
                            if truth is not None:
                                ante.append(z3.Not(self._literal_var(loc - 1, atom_id, pol)))
                    self.solver.add(z3.Implies(z3.And(*ante), z3.Not(v)))
                    print(f"{_I(i)} Adding proof of negative {M}, -> {z3.Not(v)}")
                return (M.assumptions, prove_neg)
            
            f = _choose_split_fact(M.assumptions, assumptions)
            # print(f"{literals}")
            # print(f"fact={f} choose={_choose_split_fact(M.assumptions, assumptions)}, M = {M.assumptions} assumptions={assumptions}")
            assert f is not None and f != -1
            fact = f
            proofs = []
            for i, v in enumerate(M.model.domain(fact)):
                r = self._E_cl(M.with_fact(fact, v), loc, polarity, ps_next)
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i:int) -> None:
                        self._split(M, loc, polarity, fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M}, using proof of {M.with_fact(fact, v)} for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, fact)
                for proof in proofs:
                    proof(i+1)
                print(f"{_I(i)} Splitting {M}, using all proofs for {self._V(M, loc, polarity)}")
            return (None, prove_splits)
        else:
            assert not polarity
            def define_neg_clause(i: int) -> None:
                v_index = self._lookup(M, loc, polarity).index
                if v_index in self._defined_neg_clauses:
                    print(f"{_I(i)} Already added definition for ~cl {self._V(M, loc, polarity)}")
                    return
                self._defined_neg_clauses.add(v_index)

                # M |- ~cl <-> And_i (L_i -> (M |- ~l_i))
                v = self._V(M, loc, polarity) # v = (M |- ~cl)
                vs = []
                for atom_id, atom in self._valid_atoms([sort for (_, sort, _) in self.solution_prefix]):
                    for pol in [True, False]:
                        truth_value = _F_eval(M, atom, not pol)
                        if truth_value is not None:
                            vs.append(z3.Not(self._literal_var(loc - 1, atom_id, pol)))
                self.solver.add(v == z3.And(*vs))
                print(f"{_I(i)} Adding definition for ~cl {v}")
                pass

            for (l_i, l_pol, l) in literals:
                re = _F_eval(M, l, False)
                if re is not None:
                    # def prove_pos(i: int) -> None:
                    #     v = self._V(M, loc, polarity)
                    #     self.solver.add(z3.Implies(self._literal_var(loc - 1, l_i, l_pol), z3.Not(v)))
                    #     print(f"{_I(i)} Adding proof of positive for {M}, -> {z3.Not(v)}")
                    # def prove_pos(i: int) -> None:
                    #     v = self._V(M, loc, polarity)
                    #     ante = []
                    #     for (atom_id, atom) in enumerate(self.atoms):
                    #         for pol in [True, False]:
                    #             truth = _F_eval(M, atom, not pol)
                    #             if truth is not None:
                    #                 ante.append(self._literal_var(loc - 1, atom_id, pol))
                    #     self.solver.add(z3.Implies(z3.Or(*ante), z3.Not(v)))
                    #     print(f"{_I(i)} Adding proof of positive for {M}, -> {z3.Not(v)}")
                    # return (re, prove_pos)
                    return (re, define_neg_clause)
                    
            # def prove_neg(i:int) -> None:
            #     v = self._V(M, loc, polarity)
            #     ante = []
            #     # (~L[0] \/ M |- ~l[0]) /\
            #     # ...
            #     # (~L[n] \/ M |- ~l[n]) -> (M |- ~cl)
            #     for (atom_id, atom) in enumerate(self.atoms):
            #         for pol in [True, False]:
            #             truth = _F_eval(M, atom, not pol)
            #             if truth is not None:
            #                 ante.append(z3.Not(self._literal_var(loc - 1, atom_id, pol)))
            #     self.solver.add(z3.Implies(z3.And(*ante), v))
            #     print(f"{_I(i)} Adding proof of negative {M}, -> {v}")
            
            return (None, define_neg_clause)



    def _E_cl_v2(self, M: Completion, loc: int, polarity: bool, literals: List[Tuple[int, bool, Formula]]) -> Witness:
        M.validate()
        if polarity:
            assumptions = []
            for (p_i, p_pol, p) in literals:
                r_literal = _F_eval(M, p, polarity)
                if r_literal is None:
                    def prove_literals(i: int) -> None:
                        v = self._V(M, loc, polarity)
                        vs = []
                        for atom_id, atom in self._valid_atoms([sort for (_, sort, _) in self.solution_prefix]):
                            for pol in [True, False]:
                                truth_value = _F_eval(M, atom, pol)
                                if truth_value is None:
                                    vs.append(self._literal_var(loc - 1, atom_id, pol))
                
                        self.solver.add(z3.Implies(z3.Or(*vs), v))
                        print(f"{_I(i)} Proving {M} {loc} {polarity} with literal {p} and {len(vs)-1} others")
                        # print(f"{_I(i)}   (i.e. {z3.Implies(self._literal_var(loc - 1, p_i, p_pol), v)}")
                    return (None, prove_literals)
                # print(f"Got {r_literal} from {M.assumptions} ({M})")
                assumptions.append(r_literal)
            
            # split_fact: Optional[int] = _choose_split_fact(M.assumptions, assumptions)
            split_fact: Optional[int] = _choose_split_fact(M.assumptions, assumptions)
            if split_fact is None:
                def deferred_proof(i:int) -> None:
                    # split M until it is a single completion M' (wrt the variables defined so far)
                    qvars_defined = [M.model.consts[qvar_name] for (_, _, qvar_name) in self.solution_prefix]
                    M_prime = _random_completion(M, qvars_defined, self._random_gen)
                    # get proofs that ~(M' |- A_i) (which is equivalent to M' |- ~A_i because M' is complete), for each A_i = p[x=e_i]
                    subvars: List[z3.ExprRef] = []
                    subproofs: List[SATUpdater] = []
                    for atom_id, atom in self._valid_atoms([sort for (_, sort, _) in self.solution_prefix]):
                        for pol in [True, False]:
                            truth_value = _F_eval(M_prime, atom, pol)
                            # print(M_prime, atom, pol, truth_value)
                            if truth_value is None:
                                subvars.append(self._literal_var(loc - 1, atom_id, pol))

                    self.solver.add(z3.Implies(self._V(M, loc, polarity), z3.Or(subvars)))
                    print(f"{_I(i)} Proving cl ~{self._V(M, loc, polarity)}")

                    # Add constraint M' |- ~A_i 
                return (M.assumptions, deferred_proof)
            
            assert split_fact is not None and split_fact != -1
            definite_split_fact = split_fact # this resets the type from Optional[int] to int
            split_domain = _choose_split_domain(M, definite_split_fact, assumptions)
            split_proofs = []
            
            for v in split_domain:
                M_prime = M.with_fact(definite_split_fact, v)
                r = self._E_cl_v2(M_prime, loc, polarity, literals)
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i: int) -> None:
                        self._split(M, loc, polarity, definite_split_fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M} (cl), using proof of {M.with_fact(definite_split_fact, v)} ({self._V(M_prime, loc, polarity)}) for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                split_proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, definite_split_fact)
                for proof in split_proofs:
                    proof(i+1)
                print(f"{_I(i)} Using all subproofs for split (cl) with {self._V(M, loc, polarity)}")
            return (None, prove_splits)
        else:
            assert not polarity
            def define_neg_clause(i: int) -> None:
                v_index = self._lookup(M, loc, polarity).index
                if v_index in self._defined_neg_clauses:
                    print(f"{_I(i)} Already added definition for ~cl {self._V(M, loc, polarity)}")
                    return
                self._defined_neg_clauses.add(v_index)

                # M |- ~cl <-> And_i (L_i -> (M |- ~l_i))
                v = self._V(M, loc, polarity) # v = (M |- ~cl)
                vs = []
                for atom_id, atom in self._valid_atoms([sort for (_, sort, _) in self.solution_prefix]):
                    for pol in [True, False]:
                        truth_value = _F_eval(M, atom, not pol)
                        if truth_value is not None:
                            vs.append(z3.Not(self._literal_var(loc - 1, atom_id, pol)))
                self.solver.add(v == z3.And(*vs))
                print(f"{_I(i)} Adding definition for ~cl {v}")
                pass

            for (l_i, l_pol, l) in literals:
                re = _F_eval(M, l, False)
                if re is not None:
                    return (re, define_neg_clause)
            return (None, define_neg_clause)

    
    def _E_phi(self, M: Completion, loc: int, polarity: bool, clauses: List[int], missing_clause_proofs: List[Tuple[int, SATUpdater]]) -> Witness:
        assert loc == 0
        if polarity:
            assert len(missing_clause_proofs) == 0
            proofs = []
            for cl in clauses:
                r = self._E(M, cl, polarity)
                if r[0] is not None:
                    assumpt, subproof = r
                    def proof(i:int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(self._V(M, loc, polarity), self._V(M, cl, polarity)))
                        print(f"{_I(i)} Proving matrix false with clause {cl}: {z3.Implies(self._V(M, loc, polarity), self._V(M, cl, polarity))}")
                        print(f"{_I(i)}   (i.e. {M} {loc} {polarity} -> {M} {cl} {polarity})")
                    return (assumpt, proof)
                proofs.append(r[1])
            def prove_all(i: int) -> None:
                for proof in proofs:
                    proof(i+1)
                ante = [self._V(M, cl, polarity) for cl in range(1, 1 + self.n_clauses)]
                self.solver.add(z3.Implies(z3.And(ante), self._V(M, loc, polarity)))
                print(f"{_I(i)} Proving matrix true with all clauses: {z3.Implies(z3.And(ante), self._V(M, loc, polarity))}")
                print(f"{_I(i)}   (i.e. {M} {loc} {polarity}")
            return (None, prove_all)
        else:
            # M |- ~phi = M |- ~(cl1 /\ cl2)
            # M |- ~phi = M |- ~cl1 \/ ~cl2
            assert (not polarity)
            assert len(missing_clause_proofs) + len(clauses) == self.n_clauses
            assumptions = []
            for cl in clauses:
                # RULE: M |- ~cl1 -> M |- ~phi
                r = self._E(M, cl, polarity)
                if r[0] is None:
                    (assumpt, subproof) = r
                    def prove_individual(i: int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(self._V(M, cl, polarity), self._V(M, loc, polarity)))
                        print(f"{_I(i)} Proving matrix false with clause {cl}: {z3.Implies(self._V(M, cl, polarity), self._V(M, loc, polarity))}")
                        print(f"{_I(i)}   (i.e. {M} {cl} {polarity} -> {M} {loc} {polarity})")
                    return (None, prove_individual)
                assumptions.append(r[0])
            cl_next = []
            cl_proofs = list(missing_clause_proofs)
            for cl in clauses:
                r = self._E(M, cl, not polarity)
                if r[0] is not None:
                    assumptions.append(r[0])
                    cl_next.append(cl)
                else:
                    cl_proofs.append((cl, r[1]))
            
            assert len(cl_proofs) + len(cl_next) == self.n_clauses
            if len(cl_next) == 0:
                # cl_proofs shows (M |- cl_1), ..., (M |- cl_n), so (M |- phi), so ~(M |- ~phi)
                def prove_neg(i: int) -> None:
                    ante = []
                    for subclause, proof in cl_proofs:
                        proof(i+1)
                        ante.append(self._V(M, subclause, not polarity))
                    self.solver.add(z3.Implies(z3.And(ante), z3.Not(self._V(M, loc, polarity))))
                    print(f"{_I(i)} Proving ~(M |- ~phi) =: {z3.Not(self._V(M, loc, polarity))} == {M} {loc} {polarity}")
                    print(f"{_I(i)}   (i.e. {z3.Implies(z3.And(ante), z3.Not(self._V(M, loc, polarity)))}")
                return (M.assumptions, prove_neg)
            
            f = _choose_split_fact(M.assumptions, assumptions)
            assert f is not None and f != -1
            fact = f

            split_proofs = []
            def add_implication(cl: int, pf: Callable[[int], None], M_prime: Completion) -> Tuple[int, Callable[[int], None]]:
                def ff(i: int) -> None:
                    pf(i+1)
                    self.solver.add(z3.Implies(self._V(M, cl, not polarity), self._V(M_prime, cl, not polarity)))
                    print(f"{_I(i+1)} Adding implication between {M} {M_prime} for {cl} {not polarity}")
                    print(f"{_I(i+1)}   (i.e. {z3.Implies(self._V(M, cl, not polarity), self._V(M_prime, cl, not polarity))})")
                return (cl, ff)

            for i, v in enumerate(M.model.domain(fact)):
                M_prime = M.with_fact(fact, v)
                augmented = [add_implication(cl, pf, M_prime) for (cl, pf) in cl_proofs]
                assert len(augmented) + len(cl_next) == self.n_clauses
                r = self._E_phi(M_prime, loc, polarity, cl_next, augmented)
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i: int) -> None:
                        self._split(M, loc, polarity, fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M} (phi), using proof of {M.with_fact(fact, v)} ({self._V(M_prime, loc, polarity)}) for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                split_proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, fact)
                for proof in split_proofs:
                    proof(i+1)
                print(f"{_I(i)} Using all subproofs for split (phi) with {self._V(M, loc, polarity)}")
            return (None, prove_splits)
    def _E_phi_v2(self, M: Completion, loc: int, polarity: bool, clauses: List[int], missing_clause_proofs: List[Tuple[int, SATUpdater]]) -> Witness:
        assert loc == 0
        if polarity:
            assert len(missing_clause_proofs) == 0
            proofs = []
            for cl in clauses:
                r = self._E(M, cl, polarity)
                if r[0] is not None:
                    assumpt, subproof = r
                    def proof(i:int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(self._V(M, loc, polarity), self._V(M, cl, polarity)))
                        print(f"{_I(i)} Proving matrix false with clause {cl}: {z3.Implies(self._V(M, loc, polarity), self._V(M, cl, polarity))}")
                        print(f"{_I(i)}   (i.e. {M} {loc} {polarity} -> {M} {cl} {polarity})")
                    return (assumpt, proof)
                proofs.append(r[1])
            def prove_all(i: int) -> None:
                for proof in proofs:
                    proof(i+1)
                ante = [self._V(M, cl, polarity) for cl in range(1, 1 + self.n_clauses)]
                self.solver.add(z3.Implies(z3.And(ante), self._V(M, loc, polarity)))
                print(f"{_I(i)} Proving matrix true with all clauses: {z3.Implies(z3.And(ante), self._V(M, loc, polarity))}")
                print(f"{_I(i)}   (i.e. {M} {loc} {polarity}")
            return (None, prove_all)
        else:
            # M |- ~phi = M |- ~(cl1 /\ cl2)
            # M |- ~phi = M |- ~cl1 \/ ~cl2
            assert (not polarity)
            assert len(missing_clause_proofs) + len(clauses) == self.n_clauses
            assumptions = []
            for cl in clauses:
                # RULE: M |- ~cl1 -> M |- ~phi
                r = self._E(M, cl, polarity)
                if r[0] is None:
                    (assumpt, subproof) = r
                    def prove_individual(i: int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(self._V(M, cl, polarity), self._V(M, loc, polarity)))
                        print(f"{_I(i)} Proving matrix false with clause {cl}: {z3.Implies(self._V(M, cl, polarity), self._V(M, loc, polarity))}")
                        print(f"{_I(i)}   (i.e. {M} {cl} {polarity} -> {M} {loc} {polarity})")
                    return (None, prove_individual)
                assumptions.append(r[0])
            split_fact: Optional[int] = _choose_split_fact(M.assumptions, assumptions)
            if split_fact is None:
                def deferred_proof(i:int) -> None:
                    # split M until it is a single completion M' (wrt the variables defined so far)
                    qvars_defined = [M.model.consts[qvar_name] for (_, _, qvar_name) in self.solution_prefix]
                    M_prime = _random_completion(M, qvars_defined, self._random_gen)
                    # get proofs that ~(M' |- A_i) (which is equivalent to M' |- ~A_i because M' is complete), for each A_i = p[x=e_i]
                    subvars: List[z3.ExprRef] = []
                    subproofs: List[SATUpdater] = []
                    for cl in clauses:
                        r = self._E(M_prime, cl, polarity)
                        assert r[0] is not None
                        subvars.append(self._V(M_prime, cl, polarity))
                        subproofs.append(r[1])
                    for pf in subproofs:
                        pf(i+1)
                    self.solver.add(z3.Implies(self._V(M, loc, polarity), z3.Or(subvars)))
                    print(f"{_I(i)} Proving phi ~{self._V(M, loc, polarity)} via {z3.Implies(self._V(M, loc, polarity), z3.Or(subvars))}")

                    # Add constraint M' |- ~A_i 
                return (M.assumptions, deferred_proof)
            
            assert split_fact is not None and split_fact != -1
            definite_split_fact = split_fact # this resets the type from Optional[int] to int
            split_domain = _choose_split_domain(M, definite_split_fact, assumptions)
            split_proofs = []
            
            for v in split_domain:
                M_prime = M.with_fact(definite_split_fact, v)
                r = self._E_phi_v2(M_prime, loc, polarity, clauses, [])
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i: int) -> None:
                        self._split(M, loc, polarity, definite_split_fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M} (phi), using proof of {M.with_fact(definite_split_fact, v)} ({self._V(M_prime, loc, polarity)}) for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                split_proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, definite_split_fact)
                for proof in split_proofs:
                    proof(i+1)
                print(f"{_I(i)} Using all subproofs for split (phi) with {self._V(M, loc, polarity)}")
            return (None, prove_splits)

    def _E_ae(self, M: Completion, loc: int, polarity: bool, domain: List[int], missing_domain_proofs: List[Tuple[int, SATUpdater]]) -> Witness:
        assert loc < 0
        
        is_forall, sort, qvar_name = self.solution_prefix[loc+self.n_quantifiers]
        qvar = M.model.consts[qvar_name]
        # print(f"_E_ae {loc} {polarity}: {M}")
        if is_forall == polarity:
            # simple case, M |- Ax. p or M |- ~Ex. p
            assert len(missing_domain_proofs) == 0
            cond_is_forall = z3.And(self._prefix_sort_var(loc, sort), self._prefix_quant_var(loc) if polarity else z3.Not(self._prefix_quant_var(loc)))
            (assumpt, pf) = self._E(M.with_fact(qvar, -1), loc + 1, polarity)
            if assumpt is not None:
                assumpt = _assumptions_without(assumpt, qvar)
            def proof(i:int) -> None:
                pf(i+1)
                self.solver.add(z3.Implies(cond_is_forall, self._V(M, loc, polarity) ==
                                                           self._V(M.with_fact(qvar, -1), loc + 1, polarity)))
                print(f"{_I(i)} Adding universal constraint: {M} {loc}: {z3.Implies(cond_is_forall, self._V(M, loc, polarity) == self._V(M.with_fact(qvar, -1), loc + 1, polarity))}")
            return (assumpt, proof)
        else:
            # The complex case, an effective existential
            # First, try each element of the same polarity. If any are found, we
            # can exit immediatly

            # Then try each element with the opposite polarity. If all are satisfied, we
            # are done.

            # Otherwise, we need to split
            
            assert len(missing_domain_proofs) + len(domain) == len(M.model.model.elems_of_sort_index[sort])
            cond_exists = z3.And(self._prefix_quant_var(loc) if not polarity else z3.Not(self._prefix_quant_var(loc)),
                                 self._prefix_sort_var(loc, sort))
            
            assumptions = []
            for v in domain:
                M_prime = M.with_fact(qvar, v)
                r = self._E(M_prime, loc + 1, polarity)
                if r[0] is None:
                    (assumpt, subproof) = r
                    def prove_individual(i:int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(cond_exists, 
                                                   z3.Implies(self._V(M_prime, loc + 1, polarity),
                                                              self._V(M, loc, polarity))))
                        print(f"{_I(i)} Proving existential with individual (cond & {self._V(M_prime, loc + 1, polarity)}) -> {self._V(M, loc, polarity)}")
                        print(f"{_I(i)}   (i.e. {M_prime} {loc + 1} {polarity}) -> {M_prime} {loc} {polarity})")
                    return (None, prove_individual)
                assumptions.append(_assumptions_without(r[0], qvar))
            # print(f"_E_ae {loc} {polarity}: (no true elements)")
            # print(f"_E_ae {loc} {polarity}: There are {len(missing_domain_proofs)} existing proofs")
            dom_next = []
            dom_proofs = list(missing_domain_proofs)
            for v in domain:
                M_prime = M.with_fact(qvar, v)
                r = self._E(M_prime, loc + 1, not polarity)
                if r[0] is not None:
                    assumptions.append(_assumptions_without(r[0], qvar))
                    dom_next.append(v)
                else:
                    dom_proofs.append((v, r[1]))
            
            assert len(dom_proofs) + len(dom_next) == len(M.model.model.elems_of_sort_index[sort])
            if len(dom_next) == 0:
                # This means that all of the clauses are false
                def prove_neg(i: int) -> None:
                    ante = []
                    for v, proof in dom_proofs:
                        v_i = self._V(M.with_fact(qvar, v), loc + 1, not polarity)
                        ante.append(v_i)
                        proof(i+1)
                    ante.append(cond_exists)
                    self.solver.add(z3.Implies(z3.And(ante), z3.Not(self._V(M, loc, polarity))))
                    print(f"{_I(i)} Proving disjuntion (ae) negative with antecedent: {ante} -> {z3.Not(self._V(M, loc, polarity))}")
                    print(f"{_I(i)}   (i.e. ... -> Not({M} {loc} {polarity})")
                return (M.assumptions, prove_neg)
            
            # print(f"_E_ae {loc} {polarity}: (not all elements false)")
            f = _choose_split_fact(M.assumptions, assumptions)
            assert f is not None and f != -1 and f != qvar
            fact = f

            split_proofs = []
            def add_implication(value: int, pf: Callable[[int], None], M: Completion, M_prime: Completion) -> Tuple[int, Callable[[int], None]]:
                def ff(i: int) -> None:
                    pf(i+1)
                    self.solver.add(z3.Implies(cond_exists, # TODO: should this be cond_exists??
                                               z3.Implies(self._V(M, loc + 1, not polarity),
                                                          self._V(M_prime, loc + 1, not polarity))))
                    print(f"{_I(i)} Adding prrof of {z3.Implies(cond_exists,z3.Implies(self._V(M, loc + 1, not polarity),self._V(M_prime, loc + 1, not polarity)))}")
                    print(f"{_I(i)}   (i.e. ({M} {loc + 1} {not polarity}) -> ({M_prime} {loc + 1} {not polarity})")
                return (value, ff)

            for i, v in enumerate(M.model.domain(fact)):
                M_prime = M.with_fact(fact, v)
                augmented = [add_implication(value, pf, M.with_fact(qvar, value), M.with_fact(qvar, value).with_fact(fact, v)) for (value, pf) in dom_proofs]
                r = self._E_ae(M_prime, loc, polarity, dom_next, augmented)
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i: int) -> None:
                        self._split(M, loc, polarity, fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M} (ae), using proof of {M_prime} for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                split_proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, fact)
                for proof in split_proofs:
                    proof(i+1)
                print(f"{_I(i)} Using all subproofs for split (ae) with {self._V(M, loc, polarity)}")
                
            return (None, prove_splits)

    def _E_ae_v2(self, M: Completion, loc: int, polarity: bool, domain: List[int], missing_domain_proofs: List[Tuple[int, SATUpdater]]) -> Witness:
        assert loc < 0
        
        is_forall, sort, qvar_name = self.solution_prefix[loc+self.n_quantifiers]
        qvar = M.model.consts[qvar_name]
        # print(f"_E_ae {loc} {polarity}: {M}")
        if is_forall == polarity:
            # simple case, M |- Ax. p or M |- ~Ex. p
            assert len(missing_domain_proofs) == 0
            cond_is_forall = z3.And(self._prefix_sort_var(loc, sort), self._prefix_quant_var(loc) if polarity else z3.Not(self._prefix_quant_var(loc)))
            (assumpt, pf) = self._E(M.with_fact(qvar, -1), loc + 1, polarity)
            if assumpt is not None:
                assumpt = _assumptions_without(assumpt, qvar)
            def proof(i:int) -> None:
                pf(i+1)
                self.solver.add(z3.Implies(cond_is_forall, self._V(M, loc, polarity) ==
                                                           self._V(M.with_fact(qvar, -1), loc + 1, polarity)))
                print(f"{_I(i)} Adding universal constraint: {M} {loc}: {z3.Implies(cond_is_forall, self._V(M, loc, polarity) == self._V(M.with_fact(qvar, -1), loc + 1, polarity))}")
            return (assumpt, proof)
        else:
            # The complex case, an effective existential
            # First, try each element of the same polarity. If any are found, we
            # can exit immediatly

            # Otherwise, we need to split
            
            #assert len(missing_domain_proofs) + len(domain) == len(M.model.model.elems_of_sort_index[sort])
            cond_exists = z3.And(self._prefix_quant_var(loc) if not polarity else z3.Not(self._prefix_quant_var(loc)),
                                 self._prefix_sort_var(loc, sort))
            
            assumptions = []
            for v in domain:
                # M |- A  Mcex <= M : Mcex |- ~A

                M_prime = M.with_fact(qvar, v)
                r = self._E(M_prime, loc + 1, polarity)
                if r[0] is None:
                    (assumpt, subproof) = r
                    def prove_individual(i:int) -> None:
                        subproof(i+1)
                        self.solver.add(z3.Implies(cond_exists, 
                                                   z3.Implies(self._V(M_prime, loc + 1, polarity),
                                                              self._V(M, loc, polarity))))
                        print(f"{_I(i)} Proving existential with individual (cond & {self._V(M_prime, loc + 1, polarity)}) -> {self._V(M, loc, polarity)}")
                        print(f"{_I(i)}   (i.e. {M_prime} {loc + 1} {polarity}) -> {M_prime} {loc} {polarity})")
                    return (None, prove_individual)
                assumptions.append(_assumptions_without(r[0], qvar))
            split_fact: Optional[int] = _choose_split_fact(M.assumptions, assumptions)
            if split_fact is None:
                # We have now that M[x = e] |- ~A_i for all e in dom(x).
                #for assumpt in assumptions:
                #    assert assumpt.contains(M)
                def deferred_proof(i:int) -> None:
                    # split M until it is a single completion M' (wrt the variables defined so far)
                    qvars_defined = [M.model.consts[qvar_name] for (_, _, qvar_name) in self.solution_prefix[:loc+self.n_quantifiers]]
                    M_prime = _random_completion(M, qvars_defined, self._random_gen)
                    # get proofs that ~(M' |- A_i) (which is equivalent to M' |- ~A_i because M' is complete), for each A_i = p[x=e_i]
                    subvars: List[z3.ExprRef] = []
                    subproofs: List[SATUpdater] = []
                    for v in M.model.domain(qvar):
                        r = self._E(M_prime.with_fact(qvar, v), loc + 1, polarity)
                        assert r[0] is not None
                        subvars.append(self._V(M_prime.with_fact(qvar, v), loc + 1, polarity))
                        subproofs.append(r[1])
                    for pf in subproofs:
                        pf(i+1)
                    self.solver.add(z3.Implies(z3.And(cond_exists, self._V(M, loc, polarity)), z3.Or(subvars)))
                    print(f"{_I(i)} Proving ~{self._V(M, loc, polarity)} via {z3.Implies(self._V(M, loc, polarity), z3.Or(subvars))}")

                    # Add constraint M' |- ~A_i 
                return (M.assumptions, deferred_proof)

            assert split_fact is not None and split_fact != -1 and split_fact != qvar
            definite_split_fact = split_fact # this resets the type from Optional[int] to int
            split_domain = _choose_split_domain(M, definite_split_fact, assumptions)
            split_proofs = []
            # for v in shuffled(M.model.domain(split_fact)):
            for v in split_domain:
                M_prime = M.with_fact(split_fact, v)
                r = self._E_ae_v2(M_prime, loc, polarity, domain, [])
                if r[0] is not None:
                    (assumpt, gen) = r
                    def add_splits(i: int) -> None:
                        self._split(M, loc, polarity, definite_split_fact)
                        gen(i+1)
                        print(f"{_I(i)} Splitting {M} (ae), using proof of {M_prime} for {self._V(M, loc, polarity)}")
                    return (assumpt, add_splits)
                split_proofs.append(r[1])
            def prove_splits(i: int) -> None:
                self._split(M, loc, polarity, definite_split_fact)
                for proof in split_proofs:
                    proof(i+1)
                print(f"{_I(i)} Using all subproofs for split (ae) with {self._V(M, loc, polarity)}")
                
            return (None, prove_splits)
class DiagonalPartialSeparator(object):
    def __init__(self, sig: Signature, logic: str = 'fol'):
        self._sig = sig
        self.cl = 1
        self.qs = 0
        self.logic = logic
        self.sep = PartialSeparator(self._sig, self.qs, self.cl, self.logic)
        self.models: List[Tuple[Model, bool]] = []
        
    def add_model(self, m: Model, positive: bool) -> None:
        self.models.append((m, positive))
        self.sep.add_model(m, positive)
    def _advance(self) -> None:
        if self.qs == 0:
            self.qs = self.cl
            self.cl = 1
        else:
            self.cl += 1
            self.qs -= 1
        self.sep = PartialSeparator(self._sig, self.qs, self.cl, self.logic)
        for (m, positive) in self.models:
            self.sep.add_model(m, positive)
    def separate(self, timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        while True:
            p = self.sep.separate(timer=timer)
            if p is not None:
                return p
            print(f"UNSEP for {self.qs} quantifiers, {self.cl} clauses")
            # if (self.qs == 3) and (self.cl == 1):
            #     for m, pol in self.models:
            #         m.label = "+" if pol else "-"
            #         print(m)
            self._advance()
