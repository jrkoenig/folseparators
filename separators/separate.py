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
import itertools, copy, re, random, typing
from typing import Tuple, Iterable, Union, Set, Optional, cast, Collection, List, Dict, DefaultDict, Iterator, Sequence
from dataclasses import dataclass, field
from enum import Enum
import z3

from .logic import Forall, Exists, Equal, Relation, And, Or, Not, Formula, Term, Var, Func, Model, Signature, rename_free_vars, free_vars, symbols
from .check import check
from .timer import Timer, UnlimitedTimer

# Unrolling constant
K_function_unrolling = 1

# Support things:
Quantifier = Tuple[bool, int] # (is_forall, sort_index)
QuantifierStr = Tuple[bool, str] # (is_forall, sort_name)

def NotUnless(x: z3.ExprRef, b: bool) -> z3.ExprRef: return x if b else z3.Not(x)

@dataclass(frozen=True, order=True)
class Constraint:
    """A separation constraint, one of `Pos(i)`, `Neg(i)`, or `Imp(i,j)`"""
    def map(self, m: Dict[int, int]) -> 'Constraint': ...
    def states(self) -> Iterable[int]: ...
@dataclass(frozen=True, order=True)
class Pos(Constraint):
    i: int
    def map(self, m: Dict[int, int]) -> 'Pos': return Pos(m.get(self.i, self.i))
    def states(self) -> Iterable[int]: return (self.i,)
@dataclass(frozen=True, order=True)
class Neg(Constraint):
    i: int
    def map(self, m: Dict[int, int]) -> 'Neg': return Neg(m.get(self.i, self.i))
    def states(self) -> Iterable[int]: return (self.i,)
@dataclass(frozen=True, order=True)
class Imp(Constraint):
    i: int
    j: int
    def map(self, m: Dict[int, int]) -> 'Imp': return Imp(m.get(self.i, self.i), m.get(self.j, self.j))
    def states(self) -> Iterable[int]: return (self.i,self.j)

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
    options: Dict[int, Iterator[List[str]]] = dict((sort, name_options(sig.sort_names[sort].upper(), count, sort+1)) for sort, count in c.items())
    fixed = ["" for _ in prefix]
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
    '''Free variables of a given atomic formula.'''
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
    else: assert False



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

AssignmentId = Tuple[int, Tuple[int, ...]] # Represents a particular assignment in (model_id, (elem0, elem1, elem2, ...))
class CollapseCache(object):
    def __init__(self, sig: Signature):
        self.models: List[Model] = []
        self.sig = sig
        self.cache: Dict[AssignmentId, int] = {}
        self.collapsed: Dict[str, int] = {}
        self.assignments: List[AssignmentId] = []
        self.all_assignments: DefaultDict[int, List[AssignmentId]] = defaultdict(list)
    def add_model(self, model: Model) -> None:
        self.models.append(model)
    def get(self, index: int, asgn: Sequence[int]) -> int:
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


class Logic(Enum):
    FOL = 1
    Universal = 2
    EPR = 3

@dataclass
class PrefixConstraints:
    logic: Logic = Logic.FOL
    min_depth: int = 0 # Minimal depth of quantification
    max_depth: int = 1000 # Maximum depth of quantification
    max_alt: int = 1000 # Maximum number of quantifier alternations
    max_repeated_sorts: int = 1000 # Maximum number of times the same sort repeats in quantifiers
    disallowed_quantifier_edges: List[Tuple[int, int]] = field(default_factory=list)


class Separator(object):
    def __init__(self, sig: Signature, quiet: bool = False, pc: PrefixConstraints = PrefixConstraints(), expt_flags: Set[str] = set()):
        pass
    def add_model(self, model: Model) -> int: raise NotImplemented
    def separate(self, constraints: Collection[Constraint]) -> Optional[Formula]:
        raise NotImplemented

class HybridSeparator(Separator):
    def __init__(self, sig: Signature, quiet: bool = False, pc: PrefixConstraints = PrefixConstraints(), expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
        self._sig = sig
        self._quiet = quiet
        self._pc = pc
        self._logic = pc.logic
        self._separators: Dict[int, FixedHybridSeparator] = {}
        self._models: List[Model] = []
        self._expt_flags = expt_flags
        self._blocked_symbols: List[str] = blocked_symbols

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
            h = FixedHybridSeparator(self._sig, clauses, self._quiet, self._logic, seed, self._expt_flags, self._blocked_symbols)
            for m in self._models:
                h.add_model(m)
            self._separators[clauses] = h
        return self._separators[clauses]
    def separate(self, constraints: Collection[Constraint],
                 max_clauses: int = 1000000,
                 max_complexity: int = 1000000,
                 timer: Timer = UnlimitedTimer()) -> Optional[Formula]:
        
        assert max_clauses > 0
        
        max_depths = [0]
        while True:
            for i in range(len(max_depths)):
                # run clauses == i + 1 to depth max_depths[i]
                if max_depths[i] > self._pc.max_depth or max_depths[i] + i > max_complexity:
                    continue
                r = self._get_separator(i + 1).separate_exact(list(constraints), max_depths[i], timer = timer)
                if r is not None:
                    return r
                max_depths[i] += 1
            if len(max_depths) < max_clauses:
                max_depths.append(0)
            if all(d > self._pc.max_depth or d + i > max_complexity for i, d in enumerate(max_depths)):
                return None

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

class FixedHybridSeparator(object):
    def __init__(self, sig: Signature, clauses: int, quiet: bool = False, logic: Logic = Logic.FOL, seed:Optional[int] = None, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
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
        self._blocked_symbols = blocked_symbols
        # print(f"Inside FixedHybrid Separator, blocked symbols are {blocked_symbols}")
        self._prefixes_seen: Dict[int, Set[Tuple[Tuple[bool, int], ...]]] = {}
        self._prefixes_seen_ae: Dict[int, Set[Tuple[bool, ...]]] = {}
        self._prefixes_seen_sorts: Dict[int, Set[Tuple[int, ...]]] = {}
        self._prefixes_count: Dict[int, Tuple[int,int,int]] = {}
        self._current_prefix_assumptions: List[z3.ExprRef] = []

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
            if 'alternationlimit2' in self._expt_flags:
                if d > 0:
                    self.solver.add(z3.Implies(self._depth_var(conjunct, d),
                        z3.PbLe([(self._prefix_quant_var(conjunct, i) != self._prefix_quant_var(conjunct, i+1), 1) for i in range(d-1)], 2)))
            elif 'alternationlimit1' in self._expt_flags:
                # print("Adding alternation limits!!")
                if d > 0:
                    self.solver.add(z3.Implies(self._depth_var(conjunct, d),
                        z3.PbLe([(self._prefix_quant_var(conjunct, i) != self._prefix_quant_var(conjunct, i+1), 1) for i in range(d-1)], 1)))
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
        if 'matrixsize2' in self._expt_flags:
            self.solver.add(z3.Implies(assump, z3.PbLe([(x,1) for x in literal_vars(atoms)], 2)))
        
        term_limit = 0
        if 'termlimit1' in self._expt_flags:
            term_limit = 1
        elif 'termlimit2' in self._expt_flags:
            term_limit = 2
        elif 'termlimit3' in self._expt_flags:
            term_limit = 3
        elif 'termlimit2' in self._expt_flags:
            term_limit = 4
        def literals_of_atom(a: int) -> z3.ExprRef:
            return z3.Or([self._literal_var(0, c, a, p) for c in range(self._clauses) for p in [True, False]])
        if term_limit > 0:
            for rel in self._sig.relations.keys():
                atoms_to_limit = []
                for a in atoms:
                    if rel in symbols(self._atoms[a]):
                        atoms_to_limit.append(a)
                self.solver.add(z3.Implies(assump, z3.PbLe([(literals_of_atom(x),1) for x in atoms_to_limit], term_limit)))
                
            
            
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
            atms = [a for a in atms if all(sym not in self._blocked_symbols for sym in symbols(a))]
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
               [NotUnless(self._prefix_quant_var(0,d), is_fa)
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
            pass #constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
        
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
        def constraint_complexity(c: Constraint) -> Tuple[int, int]:
            if isinstance(c, Pos) or isinstance(c, Neg):
                m = self._models[c.i]
                return (0, max([len(list(m.universe(s))) for s in self._sig.sort_names]))
            elif isinstance(c, Imp):
                m1,m2 = self._models[c.i], self._models[c.j]
                s1 = max([len(list(m1.universe(s))) for s in self._sig.sort_names])
                s2 = max([len(list(m2.universe(s))) for s in self._sig.sort_names])
                return (0, s1 + s2)
            else:
                assert False
        constraints = list(sorted(constraints, key=constraint_complexity))
        
        self._prefix_var_definition(0, depth)
        assumptions = list(self._constraint_assumptions(constraints)) + [self._depth_var(0, depth)]

        # prefix_assumptions: List[z3.ExprRef] = []

        if depth not in self._prefixes_count:
            self._prefixes_count[depth] = (0,0,0) #count_prefixes(depth, len(self._sig.sorts), self._logic)
            self._prefixes_seen[depth] = set()
            self._prefixes_seen_ae[depth] = set()
            self._prefixes_seen_sorts[depth] = set()

        print(f"Separating depth {depth} clauses {self._clauses}")
        if 'showconstraints' in self._expt_flags:
            s = ', '.join([(f"+{c.i}" if isinstance(c, Pos) else f"-{c.i}" if isinstance(c, Neg) else f"{c.i}->{c.j}" if isinstance(c, Imp) else '') for c in constraints])
        while True:
            res = timer.solver_check(self.solver, *(assumptions + self._current_prefix_assumptions))
            if res == z3.unsat:
                if len(self._current_prefix_assumptions) > 0:
                    self._current_prefix_assumptions = []
                else:
                    # print(f"UNSEP for {depth} clauses {self._clauses}: saw {len(self._prefixes_seen[depth])} of {self._prefixes_count[depth][0]} prefixes")
                    # print(f"UNSEP for {depth} clauses {self._clauses}: saw {len(self._prefixes_seen_ae[depth])} of {self._prefixes_count[depth][1]} quantifiers")
                    # print(f"UNSEP for {depth} clauses {self._clauses}: saw {len(self._prefixes_seen_sorts[depth])} of {self._prefixes_count[depth][2]} sort-patterns")
                    return None
            elif res == z3.sat:
                (prefix, matrix_list) = self._extract_cnf_formula(self.solver.model(), 0, depth, self._clauses)
                self._prefixes_seen[depth].add(tuple(prefix))
                self._prefixes_seen_ae[depth].add(tuple(f for (f, _) in prefix))
                self._prefixes_seen_sorts[depth].add(tuple((s for (_, s) in prefix)))
                matrix = And([Or(cl) for cl in matrix_list])
                prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                       for name, (pol, sort) in zip(prefix_vars, prefix)]),
                       "matrix", And([Or(cl) for cl in matrix_list]), flush=True)

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
                print(f"expanded nodes: {self._next_node_index}/{sum(len(model.elems) ** d for model in self._models for d in range(depth+1))}", flush=True)
                # Assume the same prefix on the next iteration, to help by focusing the solver
                self._current_prefix_assumptions = self._prefix_assumptions(prefix)
            else:
                print(self.solver)
                assert False # z3 should always return SAT/UNSAT on propositional formula

class FixedImplicationSeparator(object):
    def __init__(self, sig: Signature, prefix: Sequence[Tuple[Optional[bool], int]], pc: PrefixConstraints, k_cubes: int = 1, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
        self._sig = sig
        self._depth = len(prefix)
        self._prefix = list(prefix)
        self._prefix_constraints = pc
        self._n_sorts = len(sig.sort_names)
        self.solver = z3.Solver()
        self._models: List[Model] = []
        self._collapse_cache: CollapseCache = CollapseCache(sig)
        self._expt_flags = set(expt_flags)
        self._debug = False
        self._k_cubes = k_cubes
        
        self._node_roots: Dict[int, InstNode] = {}
        self._next_node_index = 0
        # self._node_vars: Dict[int, z3.ExprRef] = {}
        self.constraints: List[Constraint] = []

        self._fo_types_defined: Set[int] = set()

        self._cache_literal_var: Dict[Tuple[int, int], z3.ExprRef] = {}
        
        self.prefix_var_names = pretty_prefix_var_names(self._sig, (s for _, s in self._prefix))
        self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for v, (_, sort) in zip(self.prefix_var_names, self._prefix)]))
        # self.atoms.append(And([])) # add "true" as an atom, and thus "true" and "false" as literals
        self.literals = [a if pol else Not(a) for a in self.atoms for pol in [True, False]]
        self._cache_vars()
        self._constrain_vars()
        self.solver.check()
        self.solution: z3.ModelRef = self.solver.model()
        self.solution_prefix, self.solution_matrix = self._extract_formula()
        
    def _cache_vars(self) -> None:
        for cube in range(1 + self._k_cubes):
            for a in range(len(self.atoms)):
                for p in [True, False]:
                    self._cache_literal_var[(cube, self._literal_id(a, p))] = z3.Bool(f"L_{cube}_{a}_{'t' if p else 'f'}")
    def _constrain_vars(self) -> None:
        # Each atom can appear positively or negatively but not both
        for i in range(len(self.atoms)):
            for c in range(1+self._k_cubes):
                self.solver.add(z3.Or(z3.Not(self._literal_var(c, self._literal_id(i, True))),
                                      z3.Not(self._literal_var(c, self._literal_id(i, False)))))

        for d in range(self._depth):
            self.solver.add(z3.PbEq([(self._prefix_sort_var(d, s), 1) for s in range(self._n_sorts)], 1))
            
            if self._prefix[d][0] == True or self._prefix_constraints.logic == Logic.Universal:
                self.solver.add(self._prefix_quant_var(d))
            elif self._prefix[d][0] == False:
                self.solver.add(z3.Not(self._prefix_quant_var(d)))
            self.solver.add(self._prefix_sort_var(d, self._prefix[d][1]))
        
        for d in range(self._depth-1):
            for i,j in itertools.combinations(reversed(range(self._n_sorts)), 2):
                # Prevent adjacent universals unless their sorts are in non-strict increasing order
                A_i_d = z3.And(self._prefix_sort_var(d, i), self._prefix_quant_var(d))
                A_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), self._prefix_quant_var(d + 1))
                self.solver.add(z3.Not(z3.And(A_i_d, A_j_dp1)))
                # Same for existentials
                E_i_d = z3.And(self._prefix_sort_var(d, i), z3.Not(self._prefix_quant_var(d)))
                E_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), z3.Not(self._prefix_quant_var(d + 1)))
                self.solver.add(z3.Not(z3.And(E_i_d, E_j_dp1)))

        if self._prefix_constraints.max_alt < 1000:
            self.solver.add(z3.PbLe([(self._prefix_quant_var(d-1) != self._prefix_quant_var(d), 1) for d in range(1, self._depth)],
                                    self._prefix_constraints.max_alt))
        if self._prefix_constraints.max_repeated_sorts < 1000:
             for s in range(len(self._sig.sorts)):
                 self.solver.add(z3.PbLe([(self._prefix_sort_var(d, s), 1) for d in range(0, self._depth)], self._prefix_constraints.max_repeated_sorts))

        for (sort_i, sort_j) in self._prefix_constraints.disallowed_quantifier_edges:
            for d_i, d_j in itertools.combinations(range(self._depth), 2):
                # Disallow Ax: sort_i. ... Ey: sort_j.
                self.solver.add(z3.Not(z3.And(self._prefix_quant_var(d_i), z3.Not(self._prefix_quant_var(d_j)), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
                # Disallow Ex: sort_i. ... Ay: sort_j.
                self.solver.add(z3.Not(z3.And(z3.Not(self._prefix_quant_var(d_i)), self._prefix_quant_var(d_j), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
                    

    def _literal_id(self, atom_index: int, polarity: bool) -> int:
        return 2 * atom_index + (0 if polarity else 1)
    def _literal_var(self, cube: int, literal: int) -> z3.ExprRef:
        '''Var represents atom with polarity is in a clause'''
        #assert 0 <= clause < self.n_clauses and 0 <= atom_index < len(self.atoms)
        return self._cache_literal_var[(cube, literal)]
    def _prefix_quant_var(self, d: int) -> z3.ExprRef:
        '''Var represents whether d is a forall (true) or exists (false).'''
        assert 0 <= d < self._depth
        return z3.Bool(f"AE_{d}")
    def _prefix_sort_var(self, d: int, sort: int) -> z3.ExprRef:
        '''Var is true if quantifier d has the given sort. Exactly one is true per index.'''
        assert 0 <= d < self._depth and 0 <= sort < len(self._sig.sort_names)
        return z3.Bool(f"Q_{d}_{sort}")
    # def _prefix_qvar_var(self, sort: int, count: int) -> z3.ExprRef:
    #     '''Var is true whenever there are at least count qvars of sort'''
    #     assert 0 < count <= self._depth and 0 <= sort < len(self._sig.sort_names)
    #     return z3.Bool(f"x_{sort}_{count}")
    
    
    def _make_node(self, model_i: int, inst: List[int]) -> InstNode:
        fo_type = self._collapse_cache.get(model_i, inst)
        c = InstNode(self._next_node_index, inst, fo_type, model_i, len(self._sig.sort_names))
        self._next_node_index += 1
        var = z3.Bool(f"v_{c.index}")
        d = len(c.instantiation)
        # At the right depth, this node is exactly the FO type
        if d == self._depth:
            self.solver.add(var == self._fo_type_var(c.fo_type))
        else:
            pass
            # Unfortunately, this is not true in general because implications are not monotonic in the literal presence variables
            # If the depth is greater, then (FO type) => node
            # self.solver.add(z3.Implies(self._depth_greater_var(0, d),
            #                       z3.Implies(self._fo_type_var(c.fo_type), var)))
        return c

    def _fo_type_var(self, fo_type: int) -> z3.ExprRef:
        if fo_type not in self._fo_types_defined:
            (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
            model = self._models[model_i]
            extra_vars = {v: e for v,e in zip(self.prefix_var_names, assignment)}
            
            literals_with_polarity = []
            for lit in self._valid_literals():
                polarity = check(self.literals[lit], model, extra_vars)
                literals_with_polarity.append((lit, polarity))
            
            # This is for a implication expression
            ante = z3.Or([self._literal_var(0, lit) for (lit, p) in literals_with_polarity if not p])
            cnsq = [z3.And([z3.Not(self._literal_var(1 + i, lit)) for (lit, p) in literals_with_polarity if not p]) for i in range(self._k_cubes)]
            self.solver.add(z3.Bool(f"M_{fo_type}") == z3.Or(ante, *cnsq))

            self._fo_types_defined.add(fo_type)
        return z3.Bool(f"M_{fo_type}")

    def _valid_literals(self) -> Iterable[int]:
        # for atom_id in range(len(self.atoms)):
        #     yield 2 * atom_id
        #     yield 2 * atom_id + 1
        return range(2 * len(self.atoms))

    def _expand_node(self, node: InstNode, sort: int) -> None:
        if len(node.children[sort]) > 0:
            return # don't expand twice
        m_i = node.model_i
        for e in self._models[m_i].elems_of_sort_index[sort]:
            node.children[sort].append(self._make_node(node.model_i, node.instantiation + [e]))
        d = len(node.instantiation)
        var = z3.Bool(f"v_{node.index}")
        child_vars = [z3.Bool(f"v_{c.index}") for c in node.children[sort]]
        self.solver.add(z3.Implies(z3.And(self._prefix_quant_var(d)), var == z3.And(child_vars)))
        self.solver.add(z3.Implies(z3.And(z3.Not(self._prefix_quant_var(d))), var == z3.Or(child_vars)))

    def _model_var(self, i: int) -> z3.ExprRef:
        if i not in self._node_roots:
            self._node_roots[i] = self._make_node(i, [])
        return z3.Bool(f"v_{self._node_roots[i].index}")
    def add_model(self, model:Model) -> int:
        l = len(self._models)
        self._models.append(model)
        self._collapse_cache.add_model(model)
        return l
    def add_constraint(self, c: Constraint) -> None:
        if isinstance(c, Pos):
            self.solver.add(self._model_var(c.i))
        elif isinstance(c, Neg):
            self.solver.add(z3.Not(self._model_var(c.i)))
        elif isinstance(c, Imp):
            self.solver.add(z3.Implies(self._model_var(c.i), self._model_var(c.j)))
        self.constraints.append(c)

    def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[int]]]:
        prefix = []
        for loc in range(self._depth):
            is_forall = z3.is_true(self.solution[self._prefix_quant_var(loc)])
            sort = self._prefix[loc][1]
            name = self.prefix_var_names[loc]
            prefix.append((is_forall, sort, name))
        phi = []
        for ante in range(1 + self._k_cubes):
            cb = []
            for l in self._valid_literals():
                if z3.is_true(self.solution.eval(self._literal_var(ante, l))):
                    cb.append(l)
            phi.append(cb)
        return (prefix, phi)

    def separate(self, minimize: bool = False) -> Optional[Formula]:
        force_forall = [self._prefix_quant_var(d) for d in range(self._depth)]
        while True:
            if self._debug:
                print(f"In implication solver (d={self._depth}) sat query...")
            # print(self.solver)
            result = self.solver.check(*force_forall)
            if result == z3.unsat:
                if len(force_forall) > 0:
                    force_forall.pop()
                    continue
                return None
            assert result == z3.sat
            self.solution = self.solver.model()
            # print(self.solution)
            self.solution_prefix, self.solution_matrix = self._extract_formula()
            
            if self._debug:
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                    for (pol, sort, name) in self.solution_prefix]),
                    "matrix", And([self.literals[i] for i in self.solution_matrix[0]]), "->", "|".join(str(And([self.literals[i] for i in cube])) for cube in self.solution_matrix[1:]))
            
            if self._check_formula_validity([(ifa, sort) for (ifa, sort, _) in self.solution_prefix], self.solution_matrix, self.constraints):
                while minimize and self._local_minimize(): pass
                ante = [] if len(self.solution_matrix[0]) == 0 else [self.literals[i^1] for i in self.solution_matrix[0]]
                f: Formula = Or([*ante, *(And([self.literals[i] for i in cube]) for cube in self.solution_matrix[1:])])
                vars_used = set(free_vars(f))
                # print(f"Vars used: {vars_used} in {f}")
                for is_forall, sort, name in reversed(self.solution_prefix):
                    if name in vars_used:
                        f = (Forall if is_forall else Exists)(name, self._sig.sort_names[sort], f)
                # print(f"Post simplification: {f}")
                return f
            # otherwise, _check_formula_validity has added constraints
            if self._debug:
                print(f"expanded nodes: {self._next_node_index}/{sum(len(model.elems) ** d for model in self._models for d in range(self._depth + 1))}")
                
    def _local_minimize(self) -> bool:
        prefix_restrictions = [NotUnless(self._prefix_quant_var(d), ifa) for d, (ifa, _, _) in enumerate(self.solution_prefix)]
        not_present_literals: List[z3.ExprRef] = []
        present_literals: List[z3.ExprRef] = []
        for (ante, l), v in self._cache_literal_var.items():
            if not z3.is_true(self.solution.eval(v)):
                not_present_literals.append(z3.Not(v))
            else:
                present_literals.append(v)

        ret = self.solver.check(*prefix_restrictions, *not_present_literals, z3.PbLe([(v,1) for v in present_literals], len(present_literals) - 1))
        if ret == z3.sat:
            if self._debug:
                print(f"Found smaller solution")
            self.solution = self.solver.model()
            self.solution_prefix, self.solution_matrix = self._extract_formula()
            return True
        return False
        

    def _truth_value_conjunction(self, conj: List[int], model: Model, mapping: Dict[str, int]) -> Optional[bool]:
        all_true = True
        for lit in conj:
            is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
            v = check(self.literals[lit], model, mapping) if is_defined else None
            if v != True:
                all_true = False
            if v == False:
                return False
        # all literals are either unknown or true, because we would have early returned otherwise
        if all_true: return True
        # We must have at least one unknown, because not all are true
        return None

    def _imp_matrix_value(self, matrix_list: List[List[int]], model: Model, mapping: Dict[str, int] = {}) \
                            -> Optional[bool]:
        """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
        # TODO: Make this correct
        [ante, *cnsq] = matrix_list

        # print(f"_imp_matrix_value for {[self.literals[l] for l in ante]} -> {[self.literals[l] for l in cnsq]}")
        A = self._truth_value_conjunction(ante, model, mapping)
        # print(f"A={A}")
        if A == False:
            return True

        Bs = []
        for cube in cnsq:
            B = self._truth_value_conjunction(cube, model, mapping)
            # print(f"B={B}")
            if B == True:
                return True
            Bs.append(B)
        
        if A == True and all(B == False for B in Bs):
            return False
        return None

    def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[int]],
                                constraints: List[Constraint]) -> bool:
        depth = len(prefix)
        matrix = Or([Not(And([self.literals[i] for i in matrix_list[0]])), *(And([self.literals[i] for i in cube]) for cube in matrix_list[1:])])
        # prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])

        _matrix_value_cache: Dict[int, Optional[bool]] = {}
        def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
            if fo_type not in _matrix_value_cache:
                (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                mapping = {v: e for v,e in zip(self.prefix_var_names, assignment)}
                _matrix_value_cache[fo_type] = self._imp_matrix_value(matrix_list, self._models[model_i], mapping)
            return _matrix_value_cache[fo_type]

        def check_assignment(asgn: List[int], model: Model) -> bool:
            if len(asgn) == depth:
                return check(matrix, model, {v: e for v,e in zip(self.prefix_var_names, asgn)})
            else:
                (is_forall, sort) = prefix[len(asgn)]
                univ = model.elems_of_sort[self._sig.sort_names[sort]]
                return (all if is_forall else any)(check_assignment(asgn + [e], model) for e in univ)

        def expand_to_prove(n: InstNode, expected: bool) -> bool:
            # print(f"expand to proving model={n.model_i} inst={n.instantiation}")
            matrix_value = matrix_value_fo_type(n.fo_type)
            # print(f"matrix value={matrix_value}")
            # Early out because the solver knows that M_i => v_j, so if we know M_i is True, so does the solver
            # This is not true for implication matrices though
            # if not expected and matrix_value is True:
            #     return False            
            if len(n.instantiation) == depth:
                assert matrix_value is not None
                return expected is matrix_value
            # we aren't at the base, but check the rest of the quantifiers and return if they match
            if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                return True

            is_forall, sort = prefix[len(n.instantiation)]
            self._expand_node(n, sort)
            for c in n.children[sort]:
                expand_to_prove(c, expected)
            return False

        _root_node_cache: Dict[int, bool] = {}
        def root_node_value(n: int) -> bool:
            if n not in _root_node_cache:
                _root_node_cache[n] = check_assignment([], self._models[n])
            return _root_node_cache[n]

        def swap_to_front(c: int) -> None:
            # constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
            pass
        
        for c_i in range(len(constraints)):
            c = constraints[c_i]
            if isinstance(c, Pos):
                if not root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], True)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded + in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Neg):
                if root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], False)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded - in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Imp):
                if root_node_value(c.i) and not root_node_value(c.j):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], False)
                    expand_to_prove(self._node_roots[c.j], True)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded x-> in {c.i}, {s}/{max}")
                        s = self._node_roots[c.j].size()
                        max = sum(len(self._models[c.j].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded ->x in {c.j}, {s}/{max}")
                    return False
        return True

class InstNode2(object):
    """Represents an instantiated node in the tree of a particular model"""
    __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i', 'var']
    def __init__(self, index: int, instantiation: Tuple[int, ...], fo_type: int, model_i: int, var: z3.ExprRef):
        self.index = index
        self.instantiation = instantiation
        self.children: Tuple[InstNode2, ...] = ()
        self.fo_type = fo_type
        self.model_i = model_i
        self.var = var
    def size(self) -> int:
        return 1 + sum(c.size() for c in self.children)


class FixedImplicationSeparatorPyCryptoSat(object):
    def __init__(self, sig: Signature, prefix: Sequence[Tuple[Optional[bool], int]], pc: PrefixConstraints, k_cubes: int = 1, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
        self._sig = sig
        self._depth = len(prefix)
        self._prefix = list(prefix)
        self._prefix_constraints = pc
        self._n_sorts = len(sig.sort_names)
        self.solver = z3.Solver()
        self._models: List[Model] = []
        self._collapse_cache: CollapseCache = CollapseCache(sig)
        self._expt_flags = set(expt_flags)
        self._debug = False
        self._k_cubes = k_cubes
        
        self._node_roots: Dict[int, InstNode2] = {}
        self._next_var_index = 1
        self._node_count = 0
        self.constraints: List[Constraint] = []

        self._fo_type_vars: Dict[int, z3.ExprRef] = {}
        self.prefix_var_names = pretty_prefix_var_names(self._sig, (s for _, s in self._prefix))
        self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for v, (_, sort) in zip(self.prefix_var_names, self._prefix)]))
        # self.atoms.append(And([])) # add "true" as an atom, and thus "true" and "false" as literals
        self.literals = [a if pol else Not(a) for a in self.atoms for pol in [True, False]]
        

        self._literal_vars: Dict[Tuple[int, int], z3.ExprRef] = {}
        for cube in range(1 + self._k_cubes):
            for a in range(len(self.atoms)):
                for p in [True, False]:
                    self._literal_vars[(cube, self._literal_id(a, p))] = self._new_var()
        self._prefix_quant_vars: List[z3.ExprRef] = [self._new_var() for d in range(self._depth)]
        
        self._constrain_vars()
        self.solver.check()
        self.solution: z3.ModelRef = self.solver.model()
        self.solution_prefix, self.solution_matrix = self._extract_formula()

    def _new_var(self) -> z3.ExprRef:
        i = self._next_var_index
        self._next_var_index += 1
        return z3.Bool(f"var_{i}")

    def _literal_id(self, atom_index: int, polarity: bool) -> int:
        return 2 * atom_index + (0 if polarity else 1)

    def _constrain_vars(self) -> None:
        # Each atom can appear positively or negatively but not both
        for i in range(len(self.atoms)):
            for c in range(1+self._k_cubes):
                self.solver.add(z3.Or(z3.Not(self._literal_vars[(c, self._literal_id(i, True))]),
                                      z3.Not(self._literal_vars[(c, self._literal_id(i, False))])))

        # Add forall/exists restrictions
        for d in range(self._depth):
            assert (self._prefix[d][0] is not None)  
            if self._prefix[d][0] == True or self._prefix_constraints.logic == Logic.Universal:
                self.solver.add(self._prefix_quant_vars[d])
            elif self._prefix[d][0] == False:
                self.solver.add(z3.Not(self._prefix_quant_vars[d]))
            else:
                assert False

        # if self._prefix_constraints.max_alt < 1000:
        #     self.solver.add(z3.PbLe([(self._prefix_quant_vars[d-1] != self._prefix_quant_vars[d], 1) for d in range(1, self._depth)],
        #                             self._prefix_constraints.max_alt))
        
        # for d in range(self._depth-1):
        #     for i,j in itertools.combinations(reversed(range(self._n_sorts)), 2):
        #         # Prevent adjacent universals unless their sorts are in non-strict increasing order
        #         A_i_d = z3.And(self._prefix_sort_var(d, i), self._prefix_quant_var(d))
        #         A_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), self._prefix_quant_var(d + 1))
        #         self.solver.add(z3.Not(z3.And(A_i_d, A_j_dp1)))
        #         # Same for existentials
        #         E_i_d = z3.And(self._prefix_sort_var(d, i), z3.Not(self._prefix_quant_var(d)))
        #         E_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), z3.Not(self._prefix_quant_var(d + 1)))
        #         self.solver.add(z3.Not(z3.And(E_i_d, E_j_dp1)))

        # for (sort_i, sort_j) in self._prefix_constraints.disallowed_quantifier_edges:
        #     for d_i, d_j in itertools.combinations(range(self._depth), 2):
        #         # Disallow Ax: sort_i. ... Ey: sort_j.
        #         self.solver.add(z3.Not(z3.And(self._prefix_quant_var(d_i), z3.Not(self._prefix_quant_var(d_j)), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
        #         # Disallow Ex: sort_i. ... Ay: sort_j.
        #         self.solver.add(z3.Not(z3.And(z3.Not(self._prefix_quant_var(d_i)), self._prefix_quant_var(d_j), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))


    def _fo_type_var(self, fo_type: int) -> z3.ExprRef:
        if fo_type not in self._fo_type_vars:
            self._fo_type_vars[fo_type] = self._new_var()
            (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
            model = self._models[model_i]
            extra_vars = {v: e for v,e in zip(self.prefix_var_names, assignment)}
            
            literals_with_polarity = []
            for lit in range(2 * len(self.atoms)):
                polarity = check(self.literals[lit], model, extra_vars)
                literals_with_polarity.append((lit, polarity))
            
            # This is for a implication expression
            ante = z3.Or([self._literal_vars[(0, lit)] for (lit, p) in literals_with_polarity if not p])
            cnsq = [z3.And([z3.Not(self._literal_vars[(1 + i, lit)]) for (lit, p) in literals_with_polarity if not p]) for i in range(self._k_cubes)]
            self.solver.add(self._fo_type_vars[fo_type] == z3.Or(ante, *cnsq))
            
        return self._fo_type_vars[fo_type]
    
    def _make_node(self, model_i: int, inst: Tuple[int, ...]) -> InstNode2:
        fo_type = self._collapse_cache.get(model_i, inst)
        node = InstNode2(self._next_var_index, inst, fo_type, model_i, self._new_var())
        self._node_count += 1
        # At the right depth, this node is exactly the FO type
        if len(inst) == self._depth:
            self.solver.add(node.var == self._fo_type_var(node.fo_type))
        return node

    def _expand_node(self, node: InstNode2, sort: int) -> None:
        if len(node.children) > 0:
            return # don't expand twice
        m_i = node.model_i
        node.children = tuple(self._make_node(node.model_i, (*node.instantiation, e)) 
                              for e in self._models[m_i].elems_of_sort_index[sort])
        d = len(node.instantiation)
        child_vars = [c.var for c in node.children]
        if self._prefix[d][0] is None:
            self.solver.add(z3.Implies(self._prefix_quant_vars[d], node.var == z3.And(child_vars)))
            self.solver.add(z3.Implies(z3.Not(self._prefix_quant_vars[d]), node.var == z3.Or(child_vars)))
        else:
            self.solver.add(node.var == (z3.And if self._prefix[d][0] else z3.Or)(child_vars))
        
    def _model_var(self, i: int) -> z3.ExprRef:
        if i not in self._node_roots:
            self._node_roots[i] = self._make_node(i, ())
        return self._node_roots[i].var

    def add_model(self, model:Model) -> int:
        l = len(self._models)
        self._models.append(model)
        self._collapse_cache.add_model(model)
        return l
    def add_constraint(self, c: Constraint) -> None:
        if isinstance(c, Pos):
            self.solver.add(self._model_var(c.i))
        elif isinstance(c, Neg):
            self.solver.add(z3.Not(self._model_var(c.i)))
        elif isinstance(c, Imp):
            self.solver.add(z3.Implies(self._model_var(c.i), self._model_var(c.j)))
        self.constraints.append(c)
    def block_last_separator(self) -> None:
        cl = []
        for ante in range(1 + self._k_cubes):
            for l in range(2 * len(self.atoms)):
                if z3.is_true(self.solution.eval(self._literal_vars[(ante, l)])):
                    cl.append(self._literal_vars[(ante, l)])
        self.solver.add(z3.Not(z3.And(*cl)))
        

    def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[int]]]:
        prefix = []
        for d in range(self._depth):
            prefix_ifa = self._prefix[d][0]
            is_forall = z3.is_true(self.solution[self._prefix_quant_vars[d]]) if prefix_ifa is None else prefix_ifa
            sort = self._prefix[d][1]
            name = self.prefix_var_names[d]
            prefix.append((is_forall, sort, name))
        phi = []
        for ante in range(1 + self._k_cubes):
            cb = []
            for l in range(2 * len(self.atoms)):
                if z3.is_true(self.solution.eval(self._literal_vars[(ante, l)])):
                    cb.append(l)
            phi.append(cb)
        return (prefix, phi)

    def separate(self, minimize: bool = False) -> Optional[Formula]:
        # force_forall = [self._prefix_quant_vars[d] for d in range(self._depth)]
        while True:
            if self._debug:
                print(f"In implication solver (d={self._depth}) sat query...")
            # print(self.solver)
            # result = self.solver.check(*force_forall)
            result = self.solver.check()
            if result == z3.unsat:
                # if len(force_forall) > 0:
                #     force_forall.pop()
                #     continue
                return None
            assert result == z3.sat
            self.solution = self.solver.model()
            # print(self.solution)
            self.solution_prefix, self.solution_matrix = self._extract_formula()
            
            if self._debug:
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                    for (pol, sort, name) in self.solution_prefix]),
                    "matrix", And([self.literals[i] for i in self.solution_matrix[0]]), "->", "|".join(str(And([self.literals[i] for i in cube])) for cube in self.solution_matrix[1:]))
            
            if self._check_formula_validity([(ifa, sort) for (ifa, sort, _) in self.solution_prefix], self.solution_matrix, self.constraints):
                while minimize and self._local_minimize(): pass
                ante = [] if len(self.solution_matrix[0]) == 0 else [self.literals[i^1] for i in self.solution_matrix[0]]
                f: Formula = Or([*ante, *(And([self.literals[i] for i in cube]) for cube in self.solution_matrix[1:])])
                vars_used = set(free_vars(f))
                # print(f"Vars used: {vars_used} in {f}")
                for is_forall, sort, name in reversed(self.solution_prefix):
                    if name in vars_used:
                        f = (Forall if is_forall else Exists)(name, self._sig.sort_names[sort], f)
                # print(f"Post simplification: {f}")
                return f
            # otherwise, _check_formula_validity has added constraints
            if self._debug:
                print(f"expanded nodes: {self._node_count}/{sum(len(model.elems) ** d for model in self._models for d in range(self._depth + 1))}")
                
    def _local_minimize(self) -> bool:
        prefix_restrictions = [NotUnless(self._prefix_quant_vars[d], ifa) for d, (ifa, _, _) in enumerate(self.solution_prefix)]
        not_present_literals: List[z3.ExprRef] = []
        present_literals: List[z3.ExprRef] = []
        for (ante, l), v in self._literal_vars.items():
            if not z3.is_true(self.solution.eval(v)):
                not_present_literals.append(z3.Not(v))
            else:
                present_literals.append(v)

        ret = self.solver.check(*prefix_restrictions, *not_present_literals, z3.Not(z3.And(*present_literals)))
        if ret == z3.sat:
            if self._debug:
                print(f"Found smaller solution")
            self.solution = self.solver.model()
            self.solution_prefix, self.solution_matrix = self._extract_formula()
            return True
        return False
        

    def _truth_value_conjunction(self, conj: List[int], model: Model, mapping: Dict[str, int]) -> Optional[bool]:
        all_true = True
        for lit in conj:
            is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
            v = check(self.literals[lit], model, mapping) if is_defined else None
            if v != True:
                all_true = False
            if v == False:
                return False
        # all literals are either unknown or true, because we would have early returned otherwise
        if all_true: return True
        # We must have at least one unknown, because not all are true
        return None

    def _imp_matrix_value(self, matrix_list: List[List[int]], model: Model, mapping: Dict[str, int] = {}) -> Optional[bool]:
        """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
        [ante, *cnsq] = matrix_list
        A = self._truth_value_conjunction(ante, model, mapping)
        if A == False:
            return True
        Bs = []
        for cube in cnsq:
            B = self._truth_value_conjunction(cube, model, mapping)
            if B == True:
                return True
            Bs.append(B)
        if A == True and all(B == False for B in Bs):
            return False
        return None

    def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[int]],
                                constraints: List[Constraint]) -> bool:
        depth = len(prefix)
        matrix = Or([Not(And([self.literals[i] for i in matrix_list[0]])), *(And([self.literals[i] for i in cube]) for cube in matrix_list[1:])])
        # prefix_vars = prefix_var_names(self._sig, [q[1] for q in prefix])

        _matrix_value_cache: Dict[int, Optional[bool]] = {}
        def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
            if fo_type not in _matrix_value_cache:
                (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                mapping = {v: e for v,e in zip(self.prefix_var_names, assignment)}
                _matrix_value_cache[fo_type] = self._imp_matrix_value(matrix_list, self._models[model_i], mapping)
            return _matrix_value_cache[fo_type]

        def check_assignment(asgn: Tuple[int, ...], model: Model) -> bool:
            if len(asgn) == depth:
                return check(matrix, model, {v: e for v,e in zip(self.prefix_var_names, asgn)})
            else:
                (is_forall, sort) = prefix[len(asgn)]
                univ = model.elems_of_sort[self._sig.sort_names[sort]]
                return (all if is_forall else any)(check_assignment((*asgn, e), model) for e in univ)

        def expand_to_prove(n: InstNode2, expected: bool) -> bool:
            matrix_value = matrix_value_fo_type(n.fo_type)
            if len(n.instantiation) == depth:
                assert matrix_value is not None
                return expected is matrix_value
            # we aren't at the base, but check the rest of the quantifiers and return if they match
            if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                return True

            is_forall, sort = prefix[len(n.instantiation)]
            self._expand_node(n, sort)
            for c in n.children:
                expand_to_prove(c, expected)
            return False

        _root_node_cache: Dict[int, bool] = {}
        def root_node_value(n: int) -> bool:
            if n not in _root_node_cache:
                _root_node_cache[n] = check_assignment((), self._models[n])
            return _root_node_cache[n]

        def swap_to_front(c: int) -> None:
            constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
            # pass
        
        for c_i in range(len(constraints)):
            c = constraints[c_i]
            if isinstance(c, Pos):
                if not root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], True)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded + in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Neg):
                if root_node_value(c.i):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], False)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded - in {c.i}, {s}/{max}")
                    return False
            elif isinstance(c, Imp):
                if root_node_value(c.i) and not root_node_value(c.j):
                    swap_to_front(c_i)
                    expand_to_prove(self._node_roots[c.i], False)
                    expand_to_prove(self._node_roots[c.j], True)
                    if 'showexpansions' in self._expt_flags:
                        s = self._node_roots[c.i].size()
                        max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded x-> in {c.i}, {s}/{max}")
                        s = self._node_roots[c.j].size()
                        max = sum(len(self._models[c.j].elems) ** d for d in range(len(prefix)+1))
                        print(f"Expanded ->x in {c.j}, {s}/{max}")
                    return False
        return True

# class ParallelSeparator:
#     pass
#     def __init__(self, sig: Signature, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
#         self._sig = sig
#         self._prefix_solver = z3.Solver()
#         self._expt_flags = expt_flags
#         self._blocked_symbols = blocked_symbols
#         self._models: List[Model] = []

#         self._depths_defined: Set[int] = set()

#         self._popularity: typing.Counter[Constraint] = Counter()
#         self._sep: Optional[FixedImplicationSeparator] = None
#         self._prefix: Prefix = ()
#         self._sep_constraints: List[Constraint] = []
#         self._to_sep_model_num: Dict[int, int] = {}
            

#     def add_model(self, model: Model) -> int:
#         l = len(self._models)
#         self._models.append(model)
#         return l
    
#     def _depth_var(self, d: int) -> z3.ExprRef: return z3.Bool(f"D_{d}")
#     def _prefix_quant_var(self, d: int) -> z3.ExprRef: return z3.Bool(f"AE_{d}")
#     def _prefix_sort_var(self, d: int, sort: int) -> z3.ExprRef: return z3.Bool(f"Q_{d}_{sort}")
#     def _prefix_vars(self, prefix: Sequence[Tuple[Optional[bool], int]]) -> z3.ExprRef:
#         return z3.And(self._depth_var(len(prefix)),
#                       *(NotUnless(self._prefix_quant_var(d), cast(bool, prefix[d][0])) for d in range(len(prefix)) if prefix[d][0] is not None),
#                       *(self._prefix_sort_var(d, prefix[d][1]) for d in range(len(prefix))))
#     def _constraint_var(self, c: Constraint) -> z3.ExprRef:
#         if isinstance(c, Pos):
#             return z3.Bool(f"Pos_{c.i}")
#         elif isinstance(c, Neg):
#             return z3.Bool(f"Neg_{c.i}")
#         elif isinstance(c, Imp):
#             return z3.Bool(f"Imp_{c.i}_{c.j}")
#         assert False

#     def _ensure_depth(self, depth: int) -> None:
#         if depth in self._depths_defined:
#             return
        
#         def D(e: z3.ExprRef) -> z3.ExprRef:
#             return z3.Implies(self._depth_var(depth), e)
#         for d in range(depth):
#             self._prefix_solver.add(D(z3.PbEq([(self._prefix_sort_var(d, s), 1) for s in range(len(self._sig.sorts))], 1)))
        
#         for d in range(depth-1):
#             for i,j in itertools.combinations(reversed(range(len(self._sig.sorts))), 2):
#                 # Prevent adjacent universals unless their sorts are in non-strict increasing order
#                 A_i_d = z3.And(self._prefix_sort_var(d, i), self._prefix_quant_var(d))
#                 A_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), self._prefix_quant_var(d + 1))
#                 self._prefix_solver.add(D(z3.Not(z3.And(A_i_d, A_j_dp1))))
#                 # Same for existentials
#                 E_i_d = z3.And(self._prefix_sort_var(d, i), z3.Not(self._prefix_quant_var(d)))
#                 E_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), z3.Not(self._prefix_quant_var(d + 1)))
#                 self._prefix_solver.add(D(z3.Not(z3.And(E_i_d, E_j_dp1))))
                
#         self._depths_defined.add(depth)

#     def _alternation_leq(self, depth: int, alts: int) -> z3.ExprRef:
#         return z3.PbLe([(self._prefix_quant_var(d-1) != self._prefix_quant_var(d), 1) for d in range(1, depth)], alts)
#     def _max_repeated_sorts_leq(self, depth: int, rep: int) -> z3.ExprRef:
#         return z3.And(*(z3.PbLe([(self._prefix_sort_var(d, s), 1) for d in range(0, depth)], rep) for s in range(len(self._sig.sorts))))
#     def _logic_expr(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
#         if pc.logic == Logic.Universal:
#             return z3.And(*(self._prefix_quant_var(d) for d in range(0, depth)))
#         elif pc.logic == Logic.FOL:
#             return z3.BoolVal(True)
#         elif pc.logic == Logic.EPR:
#             pass
#             ps = []
#             for (sort_i, sort_j) in pc.disallowed_quantifier_edges:
#                 for d_i, d_j in itertools.combinations(range(depth), 2):
#                     # Disallow Ax: sort_i. ... Ey: sort_j.
#                     ps.append(z3.Not(z3.And(self._prefix_quant_var(d_i), z3.Not(self._prefix_quant_var(d_j)), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
#                     # Disallow Ex: sort_i. ... Ay: sort_j.
#                     ps.append(z3.Not(z3.And(z3.Not(self._prefix_quant_var(d_i)), self._prefix_quant_var(d_j), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
                    
#             return z3.And(*ps)
#         else:
#             assert False

#     def _get_prefix(self, constraints: Collection[Constraint], pc: PrefixConstraints) -> Optional[Tuple[Tuple[Optional[bool], int], ...]]:
#         const_expr = [self._constraint_var(c) for c in constraints]
#         depth = pc.min_depth
#         while depth <= pc.max_depth:
#             self._ensure_depth(depth)
#             r = self._prefix_solver.check(*const_expr,
#                                    self._depth_var(depth),
#                                    self._logic_expr(depth, pc),
#                                    self._alternation_leq(depth, pc.max_alt),
#                                    self._max_repeated_sorts_leq(depth, pc.max_repeated_sorts))
#             if r == z3.sat:
#                 m = self._prefix_solver.model()
#                 prefix = []
#                 for d in range(depth):
#                     #AE = z3.is_true(m.eval(self._prefix_quant_var(d), model_completion=True))
#                     AE = None
#                     sort = next(s for s in range(len(self._sig.sort_names)) if z3.is_true(m.eval(self._prefix_sort_var(d, s), model_completion=True)))
#                     prefix.append((AE, sort))
#                 return tuple(prefix)
#             depth += 1
#         return None

#     def _to_sep(self, i: int) -> int:
#         assert self._sep is not None
#         if i not in self._to_sep_model_num:
#             j = self._sep.add_model(self._models[i])
#             self._to_sep_model_num[i] = j
#         return self._to_sep_model_num[i]
#     def _add_sep_constraint(self, c: Constraint) -> None:
#         assert self._sep is not None
#         if isinstance(c, Pos):
#             self._sep.add_constraint(Pos(self._to_sep(c.i)))
#             self._sep_constraints.append(c)
#         elif isinstance(c, Neg):
#             self._sep.add_constraint(Neg(self._to_sep(c.i)))
#             self._sep_constraints.append(c)
#         elif isinstance(c, Imp):
#             self._sep.add_constraint(Imp(self._to_sep(c.i), self._to_sep(c.j)))
#             self._sep_constraints.append(c)

#     def separate(self, constraints: Sequence[Constraint], pc: PrefixConstraints) -> Optional[Formula]:
#         constraints_set = set(constraints)
#         # Invalidate the current separator if it has more constraints than the requested set. This only
#         # occurs when the client is not monotonic in their constraints
#         if self._sep is not None and not set(self._sep_constraints).issubset(constraints_set):
#             self._sep = None
#         # Similarly, we need to remove constraints from the popularity tracker so they aren't added optimistically
#         self._popularity = Counter(dict((c,cnt) for c,cnt in self._popularity.items() if c in constraints_set))
#         minimize = False

#         while True:
#             while True:
#                 if self._sep is None: break # Early out to find a new prefix
#                 candidate = self._sep.separate(minimize=minimize)
#                 if candidate is None:
#                     print(f"UNSEP: Used {len(self._sep_constraints)} constraints ({self._sep_constraints})")
#                     for c in self._sep_constraints[2:]:
#                         self._popularity[c] += 1
#                     self._prefix_solver.add(z3.Not(z3.And(self._prefix_vars(self._prefix), *(self._constraint_var(c) for c in self._sep_constraints))))
#                     break
#                 # Check candidate satisfies all the constraints. If so, we're done.
#                 # Check them in order of popularity, to maximize the chance of finding a good constraint early
#                 for c in sorted(constraints, key=lambda x: self._popularity.get(x, 0), reverse=True):
#                     if c in self._sep_constraints:
#                         continue
#                     if isinstance(c, Pos):
#                         if not check(candidate, self._models[c.i]):
#                             self._add_sep_constraint(c)
#                             break
#                     elif isinstance(c, Neg):
#                         if check(candidate, self._models[c.i]):
#                             self._add_sep_constraint(c)
#                             break
#                     elif isinstance(c, Imp):
#                         if check(candidate, self._models[c.i]) and not check(candidate, self._models[c.j]):
#                             self._add_sep_constraint(c)
#                             break
#                 else:
#                     if minimize:
#                         return candidate
#                     minimize = True
#                     continue
#                 # Otherwise, we added constraints to sep, so loop around to separate() again
#                 # Also make sure we don't minimize this time
#                 minimize = False
            
#             # There is no separator with the current prefix, so try another
#             prefix = self._get_prefix(constraints, pc)
#             if prefix is None:
#                 return None
#             print(f"Trying {prefix}")
            
#             self._sep = FixedImplicationSeparator(self._sig, prefix, pc, 2, self._expt_flags, self._blocked_symbols)
#             self._sep_constraints = []
#             self._to_sep_model_num = {}
#             self._prefix = prefix

#             # Seed solver with the most popular constraints
#             for c, _ in self._popularity.most_common(2):
#                 self._add_sep_constraint(c)



Prefix = Tuple[Tuple[Optional[bool], int], ...]
PrefixStr = Tuple[Tuple[Optional[bool], str], ...]
class PrefixSolver:
    def __init__(self, sig: Signature, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
        self._sig = sig
        self._prefix_solver = z3.Solver()
        self._expt_flags = expt_flags
        self._blocked_symbols = blocked_symbols
        
        self._depths_defined: Set[int] = set()
        self._reservations: Dict[int, z3.ExprRef] = {}
        self._reservations_by_depth: DefaultDict[int, Set[int]] = defaultdict(set)
        self._reservation_next_index: int = 0

        self._logic_conds: Dict[Tuple[int, Logic], z3.ExprRef] = {}
        self._alt_conds: Dict[Tuple[int, int], z3.ExprRef] = {}
        self._max_repeat_conds: Dict[Tuple[int, int], z3.ExprRef] = {}

        self._epr_edges_seen: Optional[List[Tuple[int, int]]] = None
        
    
    def _depth_var(self, d: int) -> z3.ExprRef: return z3.Bool(f"D_{d}")
    def _prefix_quant_var(self, d: int, i:int) -> z3.ExprRef: return z3.Bool(f"AE_{d}_{i}")
    def _prefix_sort_var(self, d: int, i: int, sort: int) -> z3.ExprRef: return z3.Bool(f"Q_{d}_{i}_{sort}")
    def _prefix_expr(self, d: int, i: int, fa: bool, sort: int) -> z3.ExprRef:
        return z3.And(self._prefix_sort_var(d, i, sort), NotUnless(self._prefix_quant_var(d, i), fa))
    def _prefix_vars(self, prefix: Sequence[Tuple[Optional[bool], int]]) -> z3.ExprRef:
        return z3.And(*(NotUnless(self._prefix_quant_var(len(prefix), i), cast(bool, prefix[i][0])) for i in range(len(prefix)) if prefix[i][0] is not None),
                      *(self._prefix_sort_var(len(prefix), i, prefix[i][1]) for i in range(len(prefix))))
    def _constraint_var(self, c: Constraint) -> z3.ExprRef:
        if isinstance(c, Pos):
            return z3.Bool(f"Pos_{c.i}")
        elif isinstance(c, Neg):
            return z3.Bool(f"Neg_{c.i}")
        elif isinstance(c, Imp):
            return z3.Bool(f"Imp_{c.i}_{c.j}")
        assert False

    def _ensure_depth(self, depth: int) -> None:
        # print(f"ensuring depth {depth}")
        if depth in self._depths_defined:
            return
        self._depths_defined.add(depth)
        
        for j in range(depth):
            self._prefix_solver.add(z3.PbEq([(self._prefix_sort_var(depth, j, s), 1) for s in range(len(self._sig.sorts))], 1))
        
        for i in range(1, depth):
            for j,k in itertools.combinations(reversed(range(len(self._sig.sorts))), 2):
                # Prevent adjacent universals unless their sorts are in non-strict increasing order
                self._prefix_solver.add(z3.Not(z3.And(self._prefix_expr(depth, i - 1, True, j), self._prefix_expr(depth, i, True, k))))
                # Same for existentials
                self._prefix_solver.add(z3.Not(z3.And(self._prefix_expr(depth, i - 1, False, j), self._prefix_expr(depth, i, False, k))))
                
        # if depth > 0:
        #     self._ensure_depth(depth-1)
        #     self._prefix_solver.add(z3.Implies(self._depth_var(depth-1), self._depth_var(depth)))
        #     disjuncts = []
        #     for i in range(depth):
        #         higher = list(range(depth)[:i]) + list(range(depth)[i+1:])
        #         lower = list(range(depth-1))
        #         assert len(higher) == len(lower)
        #         conj = []
        #         for h,l in zip(higher, lower):
        #             conj.append(self._prefix_quant_var(depth-1, l) == self._prefix_quant_var(depth, h))
        #             conj.extend(self._prefix_sort_var(depth-1, l, s) == self._prefix_sort_var(depth, h, s) for s in range(len(self._sig.sorts)))
        #         disjuncts.append(z3.And(*conj))
        #     self._prefix_solver.add(z3.Or(*disjuncts))

    def _alternation_leq(self, depth: int, alts: int) -> z3.ExprRef:
        return z3.PbLe([(self._prefix_quant_var(depth, i-1) != self._prefix_quant_var(depth, i), 1) for i in range(1, depth)], alts)
    def _max_repeated_sorts_leq(self, depth: int, rep: int) -> z3.ExprRef:
        return z3.And(*(z3.PbLe([(self._prefix_sort_var(depth, i, s), 1) for i in range(depth)], rep) for s in range(len(self._sig.sorts))))
    def _logic_expr(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
        if pc.logic == Logic.Universal:
            return z3.And(*(self._prefix_quant_var(depth, d) for d in range(0, depth)))
        elif pc.logic == Logic.FOL:
            return z3.BoolVal(True)
        elif pc.logic == Logic.EPR:
            pass
            ps = []
            for (sort_i, sort_j) in pc.disallowed_quantifier_edges:
                for d_i, d_j in itertools.combinations(range(depth), 2):
                    # Disallow Ax: sort_i. ... Ey: sort_j.
                    ps.append(z3.Not(z3.And(self._prefix_quant_var(depth, d_i),
                                            z3.Not(self._prefix_quant_var(depth, d_j)),
                                            self._prefix_sort_var(depth, d_i, sort_i),
                                            self._prefix_sort_var(depth, d_j, sort_j))))
                    # Disallow Ex: sort_i. ... Ay: sort_j.
                    ps.append(z3.Not(z3.And(z3.Not(self._prefix_quant_var(depth, d_i)),
                                            self._prefix_quant_var(depth, d_j),
                                            self._prefix_sort_var(depth, d_i, sort_i),
                                            self._prefix_sort_var(depth, d_j, sort_j))))
                    
            return z3.And(*ps)
        else:
            assert False

    def _alt_vars(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
        if (depth, pc.max_alt) not in self._alt_conds:
            v = z3.Bool(f"Alt_{depth}_{pc.max_alt}")
            self._prefix_solver.add(v == self._alternation_leq(depth, pc.max_alt))
            self._alt_conds[(depth, pc.max_alt)] = v
        return self._alt_conds[(depth, pc.max_alt)]
    def _logic_vars(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
        if (depth, pc.logic) not in self._logic_conds:
            v = z3.Bool(f"Logic_{depth}_{pc.logic.name}")
            self._prefix_solver.add(v == self._logic_expr(depth, pc))
            self._logic_conds[(depth, pc.logic)] = v
        return self._logic_conds[(depth, pc.logic)]
    def _repeat_vars(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
        if (depth, pc.max_repeated_sorts) not in self._max_repeat_conds:
            v = z3.Bool(f"MaxRepeat_{depth}_{pc.max_repeated_sorts}")
            self._prefix_solver.add(v == self._max_repeated_sorts_leq(depth, pc.max_repeated_sorts))
            self._max_repeat_conds[(depth, pc.max_repeated_sorts)] = v
        return self._max_repeat_conds[(depth, pc.max_repeated_sorts)]
    
    def _pc_vars(self, depth: int, pc: PrefixConstraints) -> z3.ExprRef:
        return z3.And(self._alt_vars(depth, pc), self._logic_vars(depth, pc), self._repeat_vars(depth, pc))

    def _extract_prefix(self, depth: int) -> Prefix:
        m = self._prefix_solver.model()
        prefix = []
        for d in range(depth):
            AE = z3.is_true(m.eval(self._prefix_quant_var(depth, d), model_completion=True))
            # AE = None
            sort = next(s for s in range(len(self._sig.sort_names)) if z3.is_true(m.eval(self._prefix_sort_var(depth, d, s), model_completion=True)))
            prefix.append((AE, sort))
        return tuple(prefix)
    def is_feasible(self, constraints: Collection[Constraint], prefix: PrefixStr) -> bool:
        constr_expr = [self._constraint_var(c) for c in constraints]
        depth = len(prefix)
        self._ensure_depth(depth)
        pre = tuple((ifa, self._sig.sort_indices[s]) for (ifa, s) in prefix)
        r = self._prefix_solver.check(self._depth_var(depth), *constr_expr, self._prefix_vars(pre))
        return r == z3.sat
    def get_prefix(self, constraints: Collection[Constraint], pc: PrefixConstraints) -> Optional[Prefix]:
        if pc.logic == Logic.EPR:
            if self._epr_edges_seen is None: self._epr_edges_seen = list(pc.disallowed_quantifier_edges)
            assert pc.disallowed_quantifier_edges == self._epr_edges_seen
        
        constr_expr = [self._constraint_var(c) for c in constraints]
        depth = pc.min_depth
        while depth <= pc.max_depth:
            if depth > pc.max_repeated_sorts * len(self._sig.sorts):
                return None
            self._ensure_depth(depth)
            # print(f"check({depth}): ", self._prefix_solver, *constr_expr,
            #                               *(self._reservations[i] for i in self._reservations_by_depth[depth]),
            #                               self._pc_vars(depth, pc))
            r = self._prefix_solver.check(self._depth_var(depth), *constr_expr,
                                          *(self._reservations[i] for i in self._reservations_by_depth[depth]),
                                          self._pc_vars(depth, pc))
            # print(f"r = {r}")
            if r == z3.sat:
                return self._extract_prefix(depth)
            depth += 1
        return None
    def reserve(self, prefix: Prefix, pc: PrefixConstraints) -> int:
        i = self._reservation_next_index
        self._reservation_next_index += 1
        if all(q[0] is not None for q in prefix):
            self._reservations[i] = z3.Not(z3.And(self._depth_var(len(prefix)), self._prefix_vars(prefix)))
        else:
            self._reservations[i] = z3.Not(z3.And(self._prefix_vars(prefix), self._logic_vars(len(prefix), pc), self._alt_vars(len(prefix), pc)))
        self._reservations_by_depth[len(prefix)].add(i)
        return i

    def unreserve(self, ident: int) -> None:
        for d, res in self._reservations_by_depth.items():
            res.discard(ident)
        del self._reservations[ident]

    def unsep(self, constraints: Collection[Constraint], pc: PrefixConstraints, prefix: Prefix) -> None:
        if all(q[0] is not None for q in prefix):
            # print("UNSEP with prefix vars only")
            self._prefix_solver.add(z3.Not(z3.And(self._depth_var(len(prefix)), self._prefix_vars(prefix), *(self._constraint_var(c) for c in constraints))))
        else:
            self._prefix_solver.add(z3.Not(z3.And(self._depth_var(len(prefix)), self._pc_vars(len(prefix), pc), self._prefix_vars(prefix), *(self._constraint_var(c) for c in constraints))))


# def _decompose(f: Formula) -> Tuple[List[Tuple[bool, str, str]], List[List[Formula]]]:
#     prefix: List[Tuple[bool, str, str]] = []
#     while isinstance(f, (Forall, Exists)):
#         is_forall = isinstance(f, Forall)
#         prefix.append((is_forall, f.sort, f.var))
#         f = f.f
#     clauses: List[List[Formula]] = []
#     if isinstance(f, And):
#         for c in f.c:
#             if isinstance(c, Or):
#                 clauses.append(c.c)
#             else:
#                 clauses.append([c])
#     elif isinstance(f, Or):
#         clauses.append(f.c)
#     else:
#         clauses.append([f])
#     return prefix, clauses

# def successor_formula(s: Signature, f: Formula) -> Iterable[Formula]:
#     prefix, clauses = _decompose(f)

#     def with_prefix(matrix: Formula) -> Formula:
#         f = matrix
#         for (is_forall, sort, var) in reversed(prefix):
#             f = (Forall if is_forall else Exists)(var, sort, f)
#         return f

#     atoms = atoms_of(s, [(var, sort) for (is_forall, sort, var) in prefix])

#     for atom in atoms:
#         for clause_ind in range(len(clauses)):
#             if atom in clauses[clause_ind] or Not(atom) in clauses[clause_ind]:
#                 continue
#             new_clauses_p = And([Or(cl if i != clause_ind else cl + [atom]) for i, cl in enumerate(clauses)])
#             new_clauses_n = And([Or(cl if i != clause_ind else cl + [cast(Formula, Not(atom))]) for i, cl in enumerate(clauses)])
#             yield with_prefix(new_clauses_p)
#             yield with_prefix(new_clauses_n)
            
# def predecessor_formula(s: Signature, f: Formula) -> Iterable[Formula]:
#     prefix, clauses = _decompose(f)
    
#     def with_prefix(matrix: Formula) -> Formula:
#         f = matrix
#         for (is_forall, sort, var) in reversed(prefix):
#             f = (Forall if is_forall else Exists)(var, sort, f)
#         return f
    
#     for clause_ind in range(len(clauses)):
#         for literal_ind in range(len(clauses[clause_ind])):
#             new_clauses = And([Or(cl if i != clause_ind else cl[:literal_ind] + cl[literal_ind+1:]) for i, cl in enumerate(clauses)])
#             yield with_prefix(new_clauses)
