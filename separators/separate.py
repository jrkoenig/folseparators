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
import itertools, copy, re, random, typing, sys, functools
from typing import Tuple, Iterable, Union, Set, Optional, cast, Collection, List, Dict, DefaultDict, Iterator, Sequence
from dataclasses import dataclass, field
from enum import Enum
import z3
import separators.sat as sat
try:
    import pycryptosat
except ModuleNotFoundError:
    pass

from .logic import Forall, Exists, Equal, Iff, Relation, And, Or, Not, Formula, Term, Var, Func, Model, Signature, free_vars, Neg, Pos, Imp, Constraint
from .check import check

# Unrolling constant
K_function_unrolling = 1

# Support things:
Quantifier = Tuple[bool, int] # (is_forall, sort_index)

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
    '''Free variables of a given atomic/literal formula.'''
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
    elif isinstance(t, And) and len(t.c) == 0:
        return
    elif isinstance(t, Or) and len(t.c) == 0:
        return
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

AssignmentId = Tuple[int, Tuple[int, ...]] # Represents a particular quantifed var assignment in model: (model_id, (elem0, elem1, elem2, ...))

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
    def get_example(self, i: int) -> AssignmentId:
        return self.assignments[i]
    def __len__(self) -> int:
        return len(self.assignments)

class Logic(Enum):
    FOL = 1
    Universal = 2
    EPR = 3
    @staticmethod
    def from_str(s: str) -> 'Logic':
        if s.lower() == 'fol': return Logic.FOL
        if s.lower() == 'universal': return Logic.Universal
        if s.lower() == 'epr': return Logic.EPR
        assert False, f"{s} is not a logic"
        
@dataclass
class PrefixConstraints:
    logic: Logic = Logic.FOL
    min_depth: int = 0 # Minimal depth of quantification
    max_depth: int = 1000 # Maximum depth of quantification
    max_alt: int = 1000 # Maximum number of quantifier alternations
    max_repeated_sorts: int = 1000 # Maximum number of times the same sort repeats in quantifiers
    disallowed_quantifier_edges: List[Tuple[int, int]] = field(default_factory=list)

class Separator(object):
    def __init__(self) -> None: pass
    def add_model(self, model: Model) -> int: raise NotImplemented
    def add_constraint(self, c: Constraint) -> None: raise NotImplemented
    def separate(self, minimize: bool) -> Optional[Formula]: raise NotImplemented
    def block_last_separator(self) -> None: raise NotImplemented

# def NotUnless(x: z3.ExprRef, b: bool) -> z3.ExprRef: return x if b else z3.Not(x)

# class InstNode2(object):
#     """Represents an instantiated node in the tree of a particular model"""
#     __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i', 'var']
#     def __init__(self, index: int, instantiation: Tuple[int, ...], fo_type: int, model_i: int, var: z3.ExprRef):
#         self.index = index
#         self.instantiation = instantiation
#         self.children: Tuple[InstNode2, ...] = ()
#         self.fo_type = fo_type
#         self.model_i = model_i
#         self.var = var
#     def size(self) -> int:
#         return 1 + sum(c.size() for c in self.children)


# class FixedImplicationSeparatorZ3(object):
#     def __init__(self, sig: Signature, prefix: Sequence[Tuple[Optional[bool], int]], pc: PrefixConstraints = PrefixConstraints(), k_cubes: int = 1, expt_flags: Set[str] = set(), blocked_symbols: List[str] = []):
#         self._sig = sig
#         self._depth = len(prefix)
#         self._prefix = list(prefix)
#         # self._prefix_constraints = pc
#         self._n_sorts = len(sig.sort_names)
#         self.solver = z3.Solver()
#         self._models: List[Model] = []
#         self._collapse_cache: CollapseCache = CollapseCache(sig)
#         self._expt_flags = set(expt_flags)
#         self._debug = False
#         self._k_cubes = k_cubes
        
#         self._node_roots: Dict[int, InstNode2] = {}
#         self._next_var_index = 1
#         self._node_count = 0
#         self.constraints: List[Constraint] = []

#         self._fo_type_vars: Dict[int, z3.ExprRef] = {}
#         self.prefix_var_names = pretty_prefix_var_names(self._sig, (s for _, s in self._prefix))
#         self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for v, (_, sort) in zip(self.prefix_var_names, self._prefix)]))
#         # self.atoms.append(And([])) # add "true" as an atom, and thus "true" and "false" as literals
#         self.literals = [a if pol else Not(a) for a in self.atoms for pol in [True, False]]
        

#         self._literal_vars: Dict[Tuple[int, int], z3.ExprRef] = {}
#         for cube in range(1 + self._k_cubes):
#             for a in range(len(self.atoms)):
#                 for p in [True, False]:
#                     self._literal_vars[(cube, self._literal_id(a, p))] = self._new_var()
#         self._prefix_quant_vars: List[z3.ExprRef] = [self._new_var() for d in range(self._depth)]
        
#         self._constrain_vars()
#         self.solver.check()
#         self.solution: z3.ModelRef = self.solver.model()
#         self.solution_prefix, self.solution_matrix = self._extract_formula()

#     def _new_var(self) -> z3.ExprRef:
#         i = self._next_var_index
#         self._next_var_index += 1
#         return z3.Bool(f"var_{i}")

#     def _literal_id(self, atom_index: int, polarity: bool) -> int:
#         return 2 * atom_index + (0 if polarity else 1)

#     def _constrain_vars(self) -> None:
#         # Each atom can appear positively or negatively but not both
#         for i in range(len(self.atoms)):
#             for c in range(1+self._k_cubes):
#                 self.solver.add(z3.Or(z3.Not(self._literal_vars[(c, self._literal_id(i, True))]),
#                                       z3.Not(self._literal_vars[(c, self._literal_id(i, False))])))

#         # Add forall/exists restrictions
#         for d in range(self._depth):
#             ifa = self._prefix[d][0]
#             assert (ifa is not None)  
#             self.solver.add(NotUnless(self._prefix_quant_vars[d], ifa))

#         # if self._prefix_constraints.max_alt < 1000:
#         #     self.solver.add(z3.PbLe([(self._prefix_quant_vars[d-1] != self._prefix_quant_vars[d], 1) for d in range(1, self._depth)],
#         #                             self._prefix_constraints.max_alt))
        
#         # for d in range(self._depth-1):
#         #     for i,j in itertools.combinations(reversed(range(self._n_sorts)), 2):
#         #         # Prevent adjacent universals unless their sorts are in non-strict increasing order
#         #         A_i_d = z3.And(self._prefix_sort_var(d, i), self._prefix_quant_var(d))
#         #         A_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), self._prefix_quant_var(d + 1))
#         #         self.solver.add(z3.Not(z3.And(A_i_d, A_j_dp1)))
#         #         # Same for existentials
#         #         E_i_d = z3.And(self._prefix_sort_var(d, i), z3.Not(self._prefix_quant_var(d)))
#         #         E_j_dp1 = z3.And(self._prefix_sort_var(d + 1, j), z3.Not(self._prefix_quant_var(d + 1)))
#         #         self.solver.add(z3.Not(z3.And(E_i_d, E_j_dp1)))

#         # for (sort_i, sort_j) in self._prefix_constraints.disallowed_quantifier_edges:
#         #     for d_i, d_j in itertools.combinations(range(self._depth), 2):
#         #         # Disallow Ax: sort_i. ... Ey: sort_j.
#         #         self.solver.add(z3.Not(z3.And(self._prefix_quant_var(d_i), z3.Not(self._prefix_quant_var(d_j)), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))
#         #         # Disallow Ex: sort_i. ... Ay: sort_j.
#         #         self.solver.add(z3.Not(z3.And(z3.Not(self._prefix_quant_var(d_i)), self._prefix_quant_var(d_j), self._prefix_sort_var(d_i, sort_i), self._prefix_sort_var(d_j, sort_j))))


#     def _fo_type_var(self, fo_type: int) -> z3.ExprRef:
#         if fo_type not in self._fo_type_vars:
#             self._fo_type_vars[fo_type] = self._new_var()
#             (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
#             model = self._models[model_i]
#             extra_vars = {v: e for v,e in zip(self.prefix_var_names, assignment)}
            
#             literals_with_polarity = []
#             for lit in range(2 * len(self.atoms)):
#                 polarity = check(self.literals[lit], model, extra_vars)
#                 literals_with_polarity.append((lit, polarity))
            
#             # This is for a implication expression
#             ante = z3.Or([self._literal_vars[(0, lit)] for (lit, p) in literals_with_polarity if not p])
#             cnsq = [z3.And([z3.Not(self._literal_vars[(1 + i, lit)]) for (lit, p) in literals_with_polarity if not p]) for i in range(self._k_cubes)]
#             self.solver.add(self._fo_type_vars[fo_type] == z3.Or(ante, *cnsq))
            
#         return self._fo_type_vars[fo_type]
    
#     def _make_node(self, model_i: int, inst: Tuple[int, ...]) -> InstNode2:
#         fo_type = self._collapse_cache.get(model_i, inst)
#         node = InstNode2(self._next_var_index, inst, fo_type, model_i, self._new_var())
#         self._node_count += 1
#         # At the right depth, this node is exactly the FO type
#         if len(inst) == self._depth:
#             self.solver.add(node.var == self._fo_type_var(node.fo_type))
#         return node

#     def _expand_node(self, node: InstNode2, sort: int) -> None:
#         if len(node.children) > 0:
#             return # don't expand twice
#         m_i = node.model_i
#         node.children = tuple(self._make_node(node.model_i, (*node.instantiation, e)) 
#                               for e in self._models[m_i].elems_of_sort_index[sort])
#         d = len(node.instantiation)
#         child_vars = [c.var for c in node.children]
#         if self._prefix[d][0] is None:
#             self.solver.add(z3.Implies(self._prefix_quant_vars[d], node.var == z3.And(child_vars)))
#             self.solver.add(z3.Implies(z3.Not(self._prefix_quant_vars[d]), node.var == z3.Or(child_vars)))
#         else:
#             self.solver.add(node.var == (z3.And if self._prefix[d][0] else z3.Or)(child_vars))
        
#     def _model_var(self, i: int) -> z3.ExprRef:
#         if i not in self._node_roots:
#             self._node_roots[i] = self._make_node(i, ())
#         return self._node_roots[i].var

#     def add_model(self, model:Model) -> int:
#         l = len(self._models)
#         self._models.append(model)
#         self._collapse_cache.add_model(model)
#         return l
#     def add_constraint(self, c: Constraint) -> None:
#         if isinstance(c, Pos):
#             self.solver.add(self._model_var(c.i))
#         elif isinstance(c, Neg):
#             self.solver.add(z3.Not(self._model_var(c.i)))
#         elif isinstance(c, Imp):
#             self.solver.add(z3.Implies(self._model_var(c.i), self._model_var(c.j)))
#         self.constraints.insert(0, c)
#     def block_last_separator(self) -> None:
#         cl = []
#         for ante in range(1 + self._k_cubes):
#             for l in range(2 * len(self.atoms)):
#                 if z3.is_true(self.solution.eval(self._literal_vars[(ante, l)])):
#                     cl.append(self._literal_vars[(ante, l)])
#         self.solver.add(z3.Not(z3.And(*cl)))
        

#     def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[int]]]:
#         prefix = []
#         for d in range(self._depth):
#             prefix_ifa = self._prefix[d][0]
#             is_forall = z3.is_true(self.solution[self._prefix_quant_vars[d]]) if prefix_ifa is None else prefix_ifa
#             sort = self._prefix[d][1]
#             name = self.prefix_var_names[d]
#             prefix.append((is_forall, sort, name))
#         phi = []
#         for ante in range(1 + self._k_cubes):
#             cb = []
#             for l in range(2 * len(self.atoms)):
#                 if z3.is_true(self.solution.eval(self._literal_vars[(ante, l)])):
#                     cb.append(l)
#             phi.append(cb)
#         return (prefix, phi)

#     def separate(self, minimize: bool = False) -> Optional[Formula]:
#         # force_forall = [self._prefix_quant_vars[d] for d in range(self._depth)]
#         while True:
#             if self._debug:
#                 print(f"In implication solver (d={self._depth}) sat query...")
#             # print(self.solver)
#             # result = self.solver.check(*force_forall)
#             result = self.solver.check()
#             if result == z3.unsat:
#                 # if len(force_forall) > 0:
#                 #     force_forall.pop()
#                 #     continue
#                 return None
#             assert result == z3.sat
#             self.solution = self.solver.model()
#             # print(self.solution)
#             self.solution_prefix, self.solution_matrix = self._extract_formula()
            
#             if self._debug:
#                 print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
#                     for (pol, sort, name) in self.solution_prefix]),
#                     "matrix", And([self.literals[i] for i in self.solution_matrix[0]]), "->", "|".join(str(And([self.literals[i] for i in cube])) for cube in self.solution_matrix[1:]))
            
#             if self._check_formula_validity([(ifa, sort) for (ifa, sort, _) in self.solution_prefix], self.solution_matrix, self.constraints):
#                 while minimize and self._local_minimize(): pass
#                 ante = [] if len(self.solution_matrix[0]) == 0 else [self.literals[i^1] for i in self.solution_matrix[0]]
#                 f: Formula = Or([*ante, *(And([self.literals[i] for i in cube]) for cube in self.solution_matrix[1:])])
#                 vars_used = set(free_vars(f))
#                 # print(f"Vars used: {vars_used} in {f}")
#                 for is_forall, sort, name in reversed(self.solution_prefix):
#                     if name in vars_used:
#                         f = (Forall if is_forall else Exists)(name, self._sig.sort_names[sort], f)
#                 # print(f"Post simplification: {f}")
#                 return f
#             # otherwise, _check_formula_validity has added constraints
#             if self._debug:
#                 print(f"expanded nodes: {self._node_count}/{sum(len(model.elems) ** d for model in self._models for d in range(self._depth + 1))}")
                
#     def _local_minimize(self) -> bool:
#         prefix_restrictions = [NotUnless(self._prefix_quant_vars[d], ifa) for d, (ifa, _, _) in enumerate(self.solution_prefix)]
#         not_present_literals: List[z3.ExprRef] = []
#         present_literals: List[z3.ExprRef] = []
#         for (ante, l), v in self._literal_vars.items():
#             if not z3.is_true(self.solution.eval(v)):
#                 not_present_literals.append(z3.Not(v))
#             else:
#                 present_literals.append(v)

#         ret = self.solver.check(*prefix_restrictions, *not_present_literals, z3.Not(z3.And(*present_literals)))
#         if ret == z3.sat:
#             if self._debug:
#                 print(f"Found smaller solution")
#             self.solution = self.solver.model()
#             self.solution_prefix, self.solution_matrix = self._extract_formula()
#             return True
#         return False
        

#     def _truth_value_conjunction(self, conj: List[int], model: Model, mapping: Dict[str, int]) -> Optional[bool]:
#         all_true = True
#         for lit in conj:
#             is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
#             v = check(self.literals[lit], model, mapping) if is_defined else None
#             if v != True:
#                 all_true = False
#             if v == False:
#                 return False
#         # all literals are either unknown or true, because we would have early returned otherwise
#         if all_true: return True
#         # We must have at least one unknown, because not all are true
#         return None

#     def _imp_matrix_value(self, matrix_list: List[List[int]], model: Model, mapping: Dict[str, int] = {}) -> Optional[bool]:
#         """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
#         [ante, *cnsq] = matrix_list
#         A = self._truth_value_conjunction(ante, model, mapping)
#         if A == False:
#             return True
#         Bs = []
#         for cube in cnsq:
#             B = self._truth_value_conjunction(cube, model, mapping)
#             if B == True:
#                 return True
#             Bs.append(B)
#         if A == True and all(B == False for B in Bs):
#             return False
#         return None

#     def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[int]],
#                                 constraints: List[Constraint]) -> bool:
#         depth = len(prefix)
#         matrix = Or([Not(And([self.literals[i] for i in matrix_list[0]])), *(And([self.literals[i] for i in cube]) for cube in matrix_list[1:])])

#         _matrix_value_cache: Dict[int, Optional[bool]] = {}
#         def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
#             if fo_type not in _matrix_value_cache:
#                 (model_i, assignment) = self._collapse_cache.get_example(fo_type)
#                 mapping = {v: e for v,e in zip(self.prefix_var_names, assignment)}
#                 _matrix_value_cache[fo_type] = self._imp_matrix_value(matrix_list, self._models[model_i], mapping)
#             return _matrix_value_cache[fo_type]

#         def check_assignment(asgn: Tuple[int, ...], model: Model) -> bool:
#             if len(asgn) == depth:
#                 return check(matrix, model, {v: e for v,e in zip(self.prefix_var_names, asgn)})
#             else:
#                 (is_forall, sort) = prefix[len(asgn)]
#                 univ = model.elems_of_sort[self._sig.sort_names[sort]]
#                 return (all if is_forall else any)(check_assignment((*asgn, e), model) for e in univ)

#         def expand_to_prove(n: InstNode2, expected: bool) -> bool:
#             matrix_value = matrix_value_fo_type(n.fo_type)
#             if len(n.instantiation) == depth:
#                 assert matrix_value is not None
#                 return expected is matrix_value
#             # we aren't at the base, but check the rest of the quantifiers and return if they match
#             if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
#                 return True

#             is_forall, sort = prefix[len(n.instantiation)]
#             self._expand_node(n, sort)
#             for c in n.children:
#                 expand_to_prove(c, expected)
#             return False

#         _root_node_cache: Dict[int, bool] = {}
#         def root_node_value(n: int) -> bool:
#             if n not in _root_node_cache:
#                 _root_node_cache[n] = check_assignment((), self._models[n])
#             return _root_node_cache[n]

#         def swap_to_front(c: int) -> None:
#             if c > 0:
#                 constraints[c - 1], constraints[c] = constraints[c], constraints[c - 1]
#             #constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
#             # pass
        
#         for c_i in range(len(constraints)):
#             c = constraints[c_i]
#             if isinstance(c, Pos):
#                 if not root_node_value(c.i):
#                     swap_to_front(c_i)
#                     expand_to_prove(self._node_roots[c.i], True)
#                     if 'showexpansions' in self._expt_flags:
#                         s = self._node_roots[c.i].size()
#                         max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
#                         print(f"Expanded + in {c.i}, {s}/{max}")
#                     return False
#             elif isinstance(c, Neg):
#                 if root_node_value(c.i):
#                     swap_to_front(c_i)
#                     expand_to_prove(self._node_roots[c.i], False)
#                     if 'showexpansions' in self._expt_flags:
#                         s = self._node_roots[c.i].size()
#                         max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
#                         print(f"Expanded - in {c.i}, {s}/{max}")
#                     return False
#             elif isinstance(c, Imp):
#                 if root_node_value(c.i) and not root_node_value(c.j):
#                     swap_to_front(c_i)
#                     expand_to_prove(self._node_roots[c.i], False)
#                     expand_to_prove(self._node_roots[c.j], True)
#                     if 'showexpansions' in self._expt_flags:
#                         s = self._node_roots[c.i].size()
#                         max = sum(len(self._models[c.i].elems) ** d for d in range(len(prefix)+1))
#                         print(f"Expanded x-> in {c.i}, {s}/{max}")
#                         s = self._node_roots[c.j].size()
#                         max = sum(len(self._models[c.j].elems) ** d for d in range(len(prefix)+1))
#                         print(f"Expanded ->x in {c.j}, {s}/{max}")
#                     return False
#         return True


class InstNode3(object):
    """Represents an instantiated node in the tree of a particular model"""
    __slots__ = ['index', 'instantiation', 'children', 'fo_type', 'model_i', 'sat_var']
    def __init__(self, index: int, instantiation: Tuple[int, ...], fo_type: int, model_i: int, sat_var: sat.Var):
        self.index = index
        self.instantiation = instantiation
        self.children: Tuple[InstNode3, ...] = ()
        self.fo_type = fo_type
        self.model_i = model_i
        self.sat_var = sat_var
    def size(self) -> int:
        return 1 + sum(c.size() for c in self.children)

def value_of(e: Formula) -> Optional[bool]:
    if isinstance(e, And):
        return _ternary_and(value_of(c) for c in e.c)
    if isinstance(e, Or):
        return _ternary_or(value_of(c) for c in e.c)
    if isinstance(e, Not):
        return _ternary_not(value_of(e.f))
    return None

def SimplifyingOr(*args: Formula) -> Formula:
    final_args = []
    for arg in args:
        v = value_of(arg) 
        if v is True: return And([])
        if v is None:
            final_args.append(arg)
    if len(final_args) == 1:
        return final_args[0]
    return Or(final_args)

def SimplifyingAnd(*args: Formula) -> Formula:
    final_args = []
    for arg in args:
        v = value_of(arg) 
        if v is False: return Or([])
        if v is None:
            final_args.append(arg)
    if len(final_args) == 1:
        return final_args[0]
    return And(final_args)
            
def _ternary_or(args: Iterable[Optional[bool]]) -> Optional[bool]:
    all_false = True
    for a in args:
        if a == True:
            return True
        elif a != False:
            all_false = False
    return False if all_false else None

def _ternary_not(arg: Optional[bool]) -> Optional[bool]:
    return arg if arg is None else not arg

def _ternary_and(args: Iterable[Optional[bool]]) -> Optional[bool]:
    all_true = True
    for a in args:
        if a == False:
            return False
        elif a != True:
            all_true = False
    return True if all_true else None

class FixedImplicationSeparatorPyCryptoSat(Separator):
    def __init__(self, sig: Signature, prefix: Sequence[Tuple[Optional[bool], int]], pc: PrefixConstraints = PrefixConstraints(), k_cubes: int = 1, expt_flags: Set[str] = set(), blocked_symbols: List[str] = [], debug: bool = False):
        self._sig = sig
        self._depth = len(prefix)
        self._prefix = [(is_forall, sort) for (is_forall, sort) in prefix if is_forall is not None]
        assert len(prefix) == len(self._prefix)
        self._prefix_constraints = pc
        self._n_sorts = len(sig.sort_names)
        self._solver = pycryptosat.Solver()
        self._next_sat_var = 1 # not 0 as 0 means "end of clause"
        self._models: List[Model] = []
        self._collapse_cache: CollapseCache = CollapseCache(sig)
        self._expt_flags = set(expt_flags)
        self._debug = debug
        self._k_cubes = k_cubes
        
        self._node_roots: Dict[int, InstNode3] = {}
        self._next_var_index = 1
        self._node_count = 0
        self.constraints: List[Constraint] = []

        self._fo_type_sat_vars: Dict[int, sat.Var] = {}
        self.prefix_var_names = pretty_prefix_var_names(self._sig, (s for _, s in self._prefix))
        self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for v, (_, sort) in zip(self.prefix_var_names, self._prefix)]))
        self.atoms.append(And([])) # add "true" as an atom, and thus "true" and "false" as literals
        
        self.literals = [a if pol else Not(a) for a in self.atoms for pol in [True, False]]
        
        self._literal_sat_vars: Dict[Tuple[int, int], sat.Var] = {}
        for cube in range(self._k_cubes):
            for a in range(len(self.atoms)):
                for p in [True, False]:
                    self._literal_sat_vars[(cube, self._literal_id(a, p))] = sat.Var(self._new_sat_var())
        
        # Vars for EPR pushdown
        self._prefix_order_vars: Dict[Tuple[int, int], sat.Var] = {}
        self._scope_vars: Dict[Tuple[int, int], sat.Var] = {}
        self._free_literal_division_vars: Dict[int, sat.Var] = {}
        self._quantifier_grouping = [list(l) for k, l in itertools.groupby(range(len(self._prefix)), key = lambda x: self._prefix[x][0])]
        
        self._constrain_vars()
        self._solver.solve(model=False)
        self.solution_prefix, self.solution_matrix = self._extract_formula()

    def _new_sat_var(self) -> int:
        v = self._next_sat_var
        self._next_sat_var += 1
        return v

    def _add_sat_expr(self, e: sat.Expr) -> None:
        if self._debug:
            print("Adding clause:", e)
        r = sat.Reduction(self._new_sat_var)
        r.reduce(e)
        self._solver.add_clauses(r.clauses)
        if self._debug:
            print("Translated to: ", r.clauses)

    def _literal_id(self, atom_index: int, polarity: bool) -> int:
        return 2 * atom_index + (0 if polarity else 1)

    def _constrain_vars(self) -> None:
        # Each atom can appear positively or negatively but not both
        for i in range(len(self.atoms)):
            for c in range(self._k_cubes):
                self._add_sat_expr(~self._literal_sat_vars[(c, self._literal_id(i, True))]
                                     | ~self._literal_sat_vars[(c, self._literal_id(i, False))])
        
        if self._prefix_constraints.logic == Logic.EPR:
            for group_index, quantifier_group in enumerate(self._quantifier_grouping):
                for i in quantifier_group:
                    for j in quantifier_group:
                        if i < j:
                            self._prefix_order_vars[(i,j)] = sat.Var(self._new_sat_var())

            for i in range(len(self._prefix)):
                for j in range(self._k_cubes + 1):
                    self._scope_vars[(i,j)] = sat.Var(self._new_sat_var())
            for l in range(2 * len(self.atoms)):
                self._free_literal_division_vars[l] = sat.Var(self._new_sat_var())

            # Order variables must be transitive.
            def _ord(i: int,j: int) -> sat.Expr: return self._prefix_order_vars[(i,j)] if i < j else ~self._prefix_order_vars[(j,i)]
            for group in self._quantifier_grouping:
                for a in group:
                    for b in group:
                        for c in group:
                            if a != b and b != c and a != c:
                                #print(f"{_ord(a,b)} ^ {_ord(b,c)} => {_ord(a,c)}")
                                # group_clauses.append(~_ord(a,b) | ~_ord(b,c) | _ord(a,c))
                                self._add_sat_expr(~_ord(a,b) | ~_ord(b,c) | _ord(a,c))

            for a in range(len(self.atoms)):
                fv = set(free_vars(self.atoms[a]))
                l_0 = self._literal_id(a, True)
                l_1 = self._literal_id(a, False)
                for i in range(len(self._prefix)):
                    if self.prefix_var_names[i] in fv:
                        for j in range(self._k_cubes + 1):
                            if j <= 1:
                                # decision var true corresponds to literal in sub-term j == 0, false to j == 1
                                c_0 = ~self._free_literal_division_vars[l_0] if j == 0 else self._free_literal_division_vars[l_0]
                                c_1 = ~self._free_literal_division_vars[l_1] if j == 0 else self._free_literal_division_vars[l_1]
                                self._add_sat_expr(c_0 | ~self._literal_sat_vars[(0, l_0)] | self._scope_vars[(i,j)])
                                self._add_sat_expr(c_1 | ~self._literal_sat_vars[(0, l_1)] | self._scope_vars[(i,j)])
                            else:
                                cube_index = j - 1 # there are two free literal sub-terms
                                self._add_sat_expr(~self._literal_sat_vars[(cube_index, l_0)] | self._scope_vars[(i,j)])
                                self._add_sat_expr(~self._literal_sat_vars[(cube_index, l_1)] | self._scope_vars[(i,j)])

            def _add_epr_constraint(i: int, i_p: int, order_var: sat.Expr) -> None:
                # print(f"Considering EPR {i} {i_p} {order_var}", file = sys.stderr)
                if self._prefix[i][0] == self._prefix[i_p][0]: return # we need either forall exists or exists forall
                if (self._prefix[i][1], self._prefix[i_p][1]) not in self._prefix_constraints.disallowed_quantifier_edges: return
                for j in range(self._k_cubes + 1):
                    self._add_sat_expr(order_var >> ~(self._scope_vars[(i,j)] & self._scope_vars[(i_p,j)]))
                    # print("Assert", order_var >> ~(self._scope_vars[(i,j)] & self._scope_vars[(i_p,j)]), file = sys.stderr)

            for group_index, group in enumerate(self._quantifier_grouping):
                for i in group:
                    for i_p in group:
                        if i!= i_p:
                            _add_epr_constraint(i, i_p, _ord(i, i_p))
                        if i != i_p and self._prefix[i_p][0]: # only need to process different quantifiers that are foralls
                            for j in range(self._k_cubes + 1):
                                for j_p in range(self._k_cubes + 1):
                                    if j != j_p:
                                        pass # assert Ord_ii' & S_ij & S_i'j & S_i'j' => S_ij'
                                        self._add_sat_expr(~_ord(i, i_p) | ~self._scope_vars[(i,j)] | ~self._scope_vars[(i_p,j)] | ~self._scope_vars[(i_p,j_p)] | self._scope_vars[(i,j_p)])

                    for sub_group in self._quantifier_grouping[group_index+1:]:
                        for i_p in sub_group:
                            _add_epr_constraint(i, i_p, sat.Val(True))
                            if self._prefix[i_p][0]: # only need to process smaller quantifiers that are foralls
                                for j in range(self._k_cubes + 1):
                                    for j_p in range(self._k_cubes + 1):
                                        if j != j_p:
                                            self._add_sat_expr(~self._scope_vars[(i,j)] | ~self._scope_vars[(i_p,j)] | ~self._scope_vars[(i_p,j_p)] | self._scope_vars[(i,j_p)])
                                            # assert S_ij & S_i'j & S_i'j' => S_ij'

            # Ensure the solver has a higher numbered variable, so it doesn't ignore any of the above 
            # even if they aren't included in any clauses. Particularly problematic for order vars

            self._add_sat_expr(sat.Var(self._new_sat_var()))

    def _fo_type_sat_var(self, fo_type: int) -> sat.Var:
        if fo_type not in self._fo_type_sat_vars:
            self._fo_type_sat_vars[fo_type] = sat.Var(self._new_sat_var())
            (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
            model = self._models[model_i]
            extra_vars = {v: e for v,e in zip(self.prefix_var_names, assignment)}
            
            literals_with_polarity = []
            for lit in range(2 * len(self.atoms)):
                polarity = check(self.literals[lit], model, extra_vars)
                literals_with_polarity.append((lit, polarity))
            
            # This is for a k-pDNF expression
            ante = [self._literal_sat_vars[(0, lit)] for (lit, p) in literals_with_polarity if not p]
            cnsq = [sat.And(*(~(self._literal_sat_vars[(1 + i, lit)]) for (lit, p) in literals_with_polarity if not p)) for i in range(self._k_cubes - 1)]
            self._add_sat_expr(self._fo_type_sat_vars[fo_type] == sat.Or(*ante, *cnsq))
            
        return self._fo_type_sat_vars[fo_type]


    def _make_node(self, model_i: int, inst: Tuple[int, ...]) -> InstNode3:
        fo_type = self._collapse_cache.get(model_i, inst)
        node = InstNode3(self._next_var_index, inst, fo_type, model_i, sat.Var(self._new_sat_var()))
        self._node_count += 1
        # At the right depth, this node is exactly the FO type
        if len(inst) == self._depth:
            self._add_sat_expr(node.sat_var == self._fo_type_sat_var(node.fo_type))
        return node

    def _expand_node(self, node: InstNode3, sort: int) -> None:
        if len(node.children) > 0:
            return # don't expand twice
        m_i = node.model_i
        node.children = tuple(self._make_node(node.model_i, (*node.instantiation, e)) 
                              for e in self._models[m_i].elems_of_sort_index[sort])
        child_sat_vars = [c.sat_var for c in node.children]
        ifa = self._prefix[len(node.instantiation)][0]
        assert ifa is not None
        self._add_sat_expr(node.sat_var == (sat.And(*child_sat_vars) if ifa else sat.Or(*child_sat_vars)))
        
    def _model_node(self, i: int) -> InstNode3:
        if i not in self._node_roots:
            self._node_roots[i] = self._make_node(i, ())
        return self._node_roots[i]

    def add_model(self, model:Model) -> int:
        l = len(self._models)
        self._models.append(model)
        self._collapse_cache.add_model(model)
        return l
    def add_constraint(self, c: Constraint) -> None:
        if isinstance(c, Pos):
            self._add_sat_expr(self._model_node(c.i).sat_var)
        elif isinstance(c, Neg):
            self._add_sat_expr(~self._model_node(c.i).sat_var)
        elif isinstance(c, Imp):
            self._add_sat_expr(self._model_node(c.i).sat_var >> self._model_node(c.j).sat_var)
        self.constraints.insert(0, c)

    def _query_literal(self, ante: int, literal: int) -> bool:
        r = self._solver.assignment([self._literal_sat_vars[(ante, literal)].i])[0]
        return r == True

    def block_last_separator(self) -> None:
        # cl = []
        cl_sat = []
        for ante in range(self._k_cubes):
            for l in range(2 * len(self.atoms)):
                if self._query_literal(ante, l):
                    cl_sat.append(self._literal_sat_vars[(ante, l)])
        self._add_sat_expr(~sat.And(*cl_sat))

    def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[int]]]:
        prefix = []
        for d in range(self._depth):
            is_forall = self._prefix[d][0]
            sort = self._prefix[d][1]
            name = self.prefix_var_names[d]
            prefix.append((is_forall, sort, name))
        phi = []
        for ante in range(self._k_cubes):
            cb = []
            for l in range(2 * len(self.atoms)):
                if self._query_literal(ante, l):
                    cb.append(l)
            phi.append(cb)
        return (prefix, phi)

    def _extract_ordered_prefix(self) -> List[Tuple[bool, int, str]]:
        order_val: Dict[Tuple[int, int], bool] = {}
        for k, v in zip(self._prefix_order_vars.keys(), self._solver.assignment(v.i for v in self._prefix_order_vars.values())):
            order_val[k] = v if v else False

        def cmp(i: int, i_p: int) -> int:
            if i == i_p:
                return 0
            if i_p < i:
                return -cmp(i_p, i)
            return -1 if order_val.get((i, i_p), True) else 1

        order = list(range(self._depth))
        order.sort(key = functools.cmp_to_key(cmp))
        return [(*self._prefix[d], self.prefix_var_names[d]) for d in order]

    def separate(self, minimize: bool = False) -> Optional[Formula]:
        if self._debug:
            print(f"Starting separate()")
        while True:
            if self._debug:
                print(f"In implication solver (d={self._depth}) sat query...")
            sat_result, _ = self._solver.solve(model=False)
            if not sat_result:
                if self._debug:
                    print("unsep from solver")
                return None
            
            if minimize:
                self._local_minimize_sat()
            else:
                self.solution_prefix, self.solution_matrix = self._extract_formula()
            # all_literal_vars = [v.i for v in self._literal_sat_vars.values()]
            # all_literal_vars.sort()
            # print(list(zip(all_literal_vars, self._solver.assignment(all_literal_vars))))
            # print(self.solution_matrix)
            
            if self._debug:
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                    for (pol, sort, name) in self.solution_prefix]),
                    "matrix", And([self.literals[i] for i in self.solution_matrix[0]]), "->", "|".join(str(And([self.literals[i] for i in cube])) for cube in self.solution_matrix[1:]))
            # if minimize:
            #     if self._local_minimize_sat2(): 
            #         print("minimized changed")
                #    continue
                
            if self._check_formula_validity([(ifa, sort) for (ifa, sort, _) in self.solution_prefix], self.solution_matrix, self.constraints):
                # while minimize and self._local_minimize_sat(): pass
                # if self._local_minimize_sat2(): 
                #     continue
                original_prefix = self.solution_prefix
                if self._prefix_constraints.logic == Logic.EPR:
                    self.solution_prefix = self._extract_ordered_prefix()
                final = self._pushdown()
                if self._prefix_constraints.logic == Logic.EPR and not self._check_epr(final):
                    print(f"PANIC, not in EPR: {final}", file=sys.stderr)
                    self._debug_epr(original_prefix, final)
                    raise RuntimeError("Not in EPR")
                return final
            # otherwise, _check_formula_validity has added constraints
            if self._debug:
                print(f"expanded nodes: {self._node_count}/{sum(len(model.elems) ** d for model in self._models for d in range(self._depth + 1))}")
    
    def _local_minimize_sat(self) -> None:
        v_i_s = [v.i for (cube, lit), v in self._literal_sat_vars.items() if lit//2 != len(self.atoms) - 1]
        while True:
            assignment = self._solver.assignment(v_i_s)
            present_literals: List[int] = [v_i for t, v_i in zip(assignment, v_i_s) if t]
            not_present_literals: List[int] = [-v_i for t, v_i in zip(assignment, v_i_s) if not t]

            random.shuffle(present_literals)
            for p in present_literals:
                ret, _ = self._solver.solve([*not_present_literals, -p], model=False)
                if ret == True:
                    if self._debug:
                        print(f"Found smaller solution")
                    break
            else:
                self.solution_prefix, self.solution_matrix = self._extract_formula()
                return

    def _pushdown_helper(self, is_forall: bool, sort: int, bv: str, terms: List[Formula]) -> List[Formula]:
        in_terms = [bv in set(free_vars(t)) for t in terms]
        p_plus = [t for t, in_term in zip(terms, in_terms) if in_term]
        p_minus = [t for t, in_term in zip(terms, in_terms) if not in_term]
        if len(p_plus) == 0: return p_minus
        if not is_forall:
            return [cast(Formula, Exists(bv, self._sig.sort_names[sort], t)) for t in p_plus] + p_minus
        else:
            body = SimplifyingOr(*p_plus)
            return [cast(Formula, Forall(bv, self._sig.sort_names[sort], body))] + p_minus

    def _pushdown(self) -> Formula:
        # Implement pushdown. Relies on self.solution_prefix being in the right order
        ante = [] if len(self.solution_matrix[0]) == 0 else [self.literals[i^1] for i in self.solution_matrix[0]]
        body = [*ante, *(SimplifyingAnd(*(self.literals[i] for i in cube)) for cube in self.solution_matrix[1:])]
        for is_forall, sort, name in reversed(self.solution_prefix):
            body = self._pushdown_helper(is_forall, sort, name, body)
        return SimplifyingOr(*body)

    def _check_epr(self, f: Formula, univ_sorts: Set[int] = set(), exst_sorts: Set[int] = set()) -> bool:
        if isinstance(f, Forall):
            this_sort = self._sig.sort_indices[f.sort]
            if not self._check_epr(f.f, univ_sorts.union([this_sort]), exst_sorts):
                return False
            for larger in exst_sorts:
                if (larger, this_sort) in self._prefix_constraints.disallowed_quantifier_edges:
                    return False
            return True
        elif isinstance(f, Exists):
            this_sort = self._sig.sort_indices[f.sort]
            if not self._check_epr(f.f, univ_sorts, exst_sorts.union([this_sort])):
                return False
            for larger in univ_sorts:
                if (larger, this_sort) in self._prefix_constraints.disallowed_quantifier_edges:
                    return False
            return True                
        elif isinstance(f, Or) or isinstance(f, And):
            return all(self._check_epr(subf, univ_sorts, exst_sorts) for subf in f.c)
        elif isinstance(f, Not):
            return self._check_epr(f.f, exst_sorts, univ_sorts)
        elif isinstance(f, Iff):
            return self._check_epr(f.c[0], univ_sorts, exst_sorts) and \
                   self._check_epr(f.c[1], exst_sorts, univ_sorts)
        else:
            return True
    
    def _debug_epr(self, prefix: List[Tuple[bool, int, str]], final: Formula) -> None:
        sys.stdout = sys.stderr
        print("final", final)
        print("initial prefix def", self._prefix)
        print("initial prefix", prefix)
        print(self.solution_prefix)
        print(self.solution_matrix)
        for ord, var in self._prefix_order_vars.items():
            print("ord", ord, self._solver.assignment([var.i])[0])
        
        for i in range(len(self._prefix)):
            print (f"{i}: ", end='')
            for j in range(self._k_cubes + 1):
                var = self._scope_vars[(i, j)]
                print(1 if self._solver.assignment([var.i])[0] else 0, end = ' ')

            print (f"({self.prefix_var_names[i]}, {'forall' if self._prefix[i][0] else 'exists'})")

    # def _truth_value_conjunction(self, conj: List[int], model: Model, mapping: Dict[str, int]) -> Optional[bool]:
    #     all_true = True
    #     for lit in conj:
    #         is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
    #         v = check(self.literals[lit], model, mapping) if is_defined else None
    #         if v != True:
    #             all_true = False
    #         if v == False:
    #             return False
    #     # all literals are either unknown or true, because we would have early returned otherwise
    #     if all_true: return True
    #     # We must have at least one unknown, because not all are true
    #     return None

    def _literal_value(self, lit: int, model: Model, mapping: Dict[str, int]) -> Optional[bool]:
        is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
        return check(self.literals[lit], model, mapping) if is_defined else None

    def _imp_matrix_value(self, matrix_list: List[List[int]], model: Model, mapping: Dict[str, int] = {}) -> Optional[bool]:
        """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
        return _ternary_or((_ternary_not(_ternary_and(self._literal_value(lit, model, mapping) for lit in cl_cube)) if i == 0
                             else _ternary_and(self._literal_value(lit, model, mapping) for lit in cl_cube) for i, cl_cube in enumerate(matrix_list)))
        
        # [ante, *cnsq] = matrix_list
        # A = self._truth_value_conjunction(ante, model, mapping)
        # if A == False:
        #     return True
        # Bs = []
        # for cube in cnsq:
        #     B = self._truth_value_conjunction(cube, model, mapping)
        #     if B == True:
        #         return True
        #     Bs.append(B)
        # if A == True and all(B == False for B in Bs):
        #     return False
        # return None

    def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[int]],
                                constraints: List[Constraint]) -> bool:
        depth = len(prefix)
        # matrix = Or([Not(And([self.literals[i] for i in matrix_list[0]])), *(And([self.literals[i] for i in cube]) for cube in matrix_list[1:])])

        _matrix_value_cache: Dict[int, Optional[bool]] = {}
        def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
            if fo_type not in _matrix_value_cache:
                (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                mapping = {v: e for v,e in zip(self.prefix_var_names, assignment)}
                _matrix_value_cache[fo_type] = self._imp_matrix_value(matrix_list, self._models[model_i], mapping)
            return _matrix_value_cache[fo_type]

        def check_assignment(asgn: Tuple[int, ...], model: Model) -> bool:
            if len(asgn) == depth:
                mapping = {v: e for v,e in zip(self.prefix_var_names, asgn)}
                value = self._imp_matrix_value(matrix_list, model, mapping)
                assert value is not None
                return value
                # return check(matrix, model, {v: e for v,e in zip(self.prefix_var_names, asgn)})
            else:
                (is_forall, sort) = prefix[len(asgn)]
                univ = model.elems_of_sort[self._sig.sort_names[sort]]
                return (all if is_forall else any)(check_assignment((*asgn, e), model) for e in univ)

        def expand_to_prove(n: InstNode3, expected: bool) -> bool:
            matrix_value = matrix_value_fo_type(n.fo_type)
            if len(n.instantiation) == depth:
                assert matrix_value is not None
                return expected is matrix_value
            # we aren't at the base, but check the rest of the quantifiers and return if they match
            if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                return True

            _, sort = prefix[len(n.instantiation)]
            self._expand_node(n, sort)
            if 'showexpansions' in self._expt_flags:
                print(f"Expanded node {n}")
            for c in n.children:
                expand_to_prove(c, expected)
            return False

        _root_node_cache: Dict[int, bool] = {}
        def root_node_value(n: int) -> bool:
            if n not in _root_node_cache:
                _root_node_cache[n] = check_assignment((), self._models[n])
            return _root_node_cache[n]

        def swap_to_front(c: int) -> None:
            if c > 0:
                constraints[c - 1], constraints[c] = constraints[c], constraints[c - 1]
            #constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
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


class FixedImplicationSeparatorPyCryptoSatCNF(Separator):
    def __init__(self, sig: Signature, prefix: Sequence[Tuple[Optional[bool], int]], pc: PrefixConstraints = PrefixConstraints(), k_cubes: int = 1, expt_flags: Set[str] = set(), blocked_symbols: List[str] = [], debug: bool = False):
        self._sig = sig
        self._depth = len(prefix)
        self._prefix = [(is_forall, sort) for (is_forall, sort) in prefix if is_forall is not None]
        assert len(prefix) == len(self._prefix)
        self._prefix_constraints = pc
        self._n_sorts = len(sig.sort_names)
        self._solver = pycryptosat.Solver()
        self._next_sat_var = 1 # not 0 as 0 means "end of clause" in DIMACS encoding
        self._models: List[Model] = []
        self._collapse_cache: CollapseCache = CollapseCache(sig)
        self._expt_flags = set(expt_flags)
        self._debug = debug
        self._k_clauses = k_cubes
        
        self._node_roots: Dict[int, InstNode3] = {}
        self._next_var_index = 1
        self._node_count = 0
        self.constraints: List[Constraint] = []

        self._fo_type_sat_vars: Dict[int, sat.Var] = {}
        self.prefix_var_names = pretty_prefix_var_names(self._sig, (s for _, s in self._prefix))
        self.atoms = list(atoms_of(self._sig, [(v, self._sig.sort_names[sort]) for v, (_, sort) in zip(self.prefix_var_names, self._prefix)]))
        self.atoms.append(And([])) # add "true" as an atom, and thus "true" and "false" as literals
        
        self.literals = [a if pol else Not(a) for a in self.atoms for pol in [True, False]]
        
        self._literal_sat_vars: Dict[Tuple[int, int], sat.Var] = {}
        for cube in range(self._k_clauses):
            for a in range(len(self.atoms)):
                for p in [True, False]:
                    self._literal_sat_vars[(cube, self._literal_id(a, p))] = sat.Var(self._new_sat_var())
        
        # Vars for EPR pushdown
        # self._prefix_order_vars: Dict[Tuple[int, int], sat.Var] = {}
        # self._scope_vars: Dict[Tuple[int, int], sat.Var] = {}
        # self._free_literal_division_vars: Dict[int, sat.Var] = {}
        # self._quantifier_grouping = [list(l) for k, l in itertools.groupby(range(len(self._prefix)), key = lambda x: self._prefix[x][0])]
        
        self._constrain_vars()
        self._solver.solve(model=False)
        self.solution_prefix, self.solution_matrix = self._extract_formula()

    def _new_sat_var(self) -> int:
        v = self._next_sat_var
        self._next_sat_var += 1
        return v

    def _add_sat_expr(self, e: sat.Expr) -> None:
        if self._debug:
            print("Adding clause:", e)
        r = sat.Reduction(self._new_sat_var)
        r.reduce(e)
        self._solver.add_clauses(r.clauses)
        if self._debug:
            print("Translated to: ", r.clauses)

    def _literal_id(self, atom_index: int, polarity: bool) -> int:
        return 2 * atom_index + (0 if polarity else 1)

    def _constrain_vars(self) -> None:
        # Each atom can appear positively or negatively but not both
        for i in range(len(self.atoms)):
            for c in range(self._k_clauses):
                self._add_sat_expr(~self._literal_sat_vars[(c, self._literal_id(i, True))]
                                     | ~self._literal_sat_vars[(c, self._literal_id(i, False))])
        
    def _fo_type_sat_var(self, fo_type: int) -> sat.Var:
        if fo_type not in self._fo_type_sat_vars:
            self._fo_type_sat_vars[fo_type] = sat.Var(self._new_sat_var())
            (model_i, assignment) = self._collapse_cache.get_example(fo_type)
            
            model = self._models[model_i]
            extra_vars = {v: e for v,e in zip(self.prefix_var_names, assignment)}
            
            literals_with_polarity = []
            for lit in range(2 * len(self.atoms)):
                polarity = check(self.literals[lit], model, extra_vars)
                literals_with_polarity.append((lit, polarity))
            
            # This is for a CNF expression
            clauses = [sat.Or(*(self._literal_sat_vars[(i, lit)] for (lit, p) in literals_with_polarity if p)) for i in range(self._k_clauses)]
            self._add_sat_expr(self._fo_type_sat_vars[fo_type] == sat.And(*clauses))
            
        return self._fo_type_sat_vars[fo_type]


    def _make_node(self, model_i: int, inst: Tuple[int, ...]) -> InstNode3:
        fo_type = self._collapse_cache.get(model_i, inst)
        node = InstNode3(self._next_var_index, inst, fo_type, model_i, sat.Var(self._new_sat_var()))
        self._node_count += 1
        # At the right depth, this node is exactly the FO type
        if len(inst) == self._depth:
            self._add_sat_expr(node.sat_var == self._fo_type_sat_var(node.fo_type))
        return node

    def _expand_node(self, node: InstNode3, sort: int) -> None:
        if len(node.children) > 0:
            return # don't expand twice
        m_i = node.model_i
        node.children = tuple(self._make_node(node.model_i, (*node.instantiation, e)) 
                              for e in self._models[m_i].elems_of_sort_index[sort])
        child_sat_vars = [c.sat_var for c in node.children]
        ifa = self._prefix[len(node.instantiation)][0]
        assert ifa is not None
        self._add_sat_expr(node.sat_var == (sat.And(*child_sat_vars) if ifa else sat.Or(*child_sat_vars)))
        
    def _model_node(self, i: int) -> InstNode3:
        if i not in self._node_roots:
            self._node_roots[i] = self._make_node(i, ())
        return self._node_roots[i]

    def add_model(self, model: Model) -> int:
        l = len(self._models)
        self._models.append(model)
        self._collapse_cache.add_model(model)
        return l

    def add_constraint(self, c: Constraint) -> None:
        if isinstance(c, Pos):
            self._add_sat_expr(self._model_node(c.i).sat_var)
        elif isinstance(c, Neg):
            self._add_sat_expr(~self._model_node(c.i).sat_var)
        elif isinstance(c, Imp):
            self._add_sat_expr(self._model_node(c.i).sat_var >> self._model_node(c.j).sat_var)
        self.constraints.insert(0, c)

    def _query_literal(self, ante: int, literal: int) -> bool:
        r = self._solver.assignment([self._literal_sat_vars[(ante, literal)].i])[0]
        return r == True

    def block_last_separator(self) -> None:
        # cl = []
        cl_sat = []
        for ante in range(self._k_clauses):
            for l in range(2 * len(self.atoms)):
                if self._query_literal(ante, l):
                    cl_sat.append(self._literal_sat_vars[(ante, l)])
        self._add_sat_expr(~sat.And(*cl_sat))

    def _extract_formula(self) -> Tuple[List[Tuple[bool, int, str]], List[List[int]]]:
        prefix = []
        for d in range(self._depth):
            is_forall = self._prefix[d][0]
            sort = self._prefix[d][1]
            name = self.prefix_var_names[d]
            prefix.append((is_forall, sort, name))
        phi = []
        for ante in range(self._k_clauses):
            cb = []
            for l in range(2 * len(self.atoms)):
                if self._query_literal(ante, l):
                    cb.append(l)
            phi.append(cb)
        return (prefix, phi)

    def separate(self, minimize: bool = False) -> Optional[Formula]:
        if self._debug:
            print(f"Starting separate()")
        while True:
            if self._debug:
                print(f"In implication solver (d={self._depth}) sat query...")
            sat_result, _ = self._solver.solve(model=False)
            if not sat_result:
                if self._debug:
                    print("unsep from solver")
                return None
            
            if minimize:
                self._local_minimize_sat()
            else:
                self.solution_prefix, self.solution_matrix = self._extract_formula()
            # all_literal_vars = [v.i for v in self._literal_sat_vars.values()]
            # all_literal_vars.sort()
            # print(list(zip(all_literal_vars, self._solver.assignment(all_literal_vars))))
            # print(self.solution_matrix)
            
            if self._debug:
                print ("prefix", " ".join([f"{'A' if pol else 'E'} {name}:{self._sig.sort_names[sort]}" \
                    for (pol, sort, name) in self.solution_prefix]),
                    "matrix", And([Or([self.literals[i] for i in cl]) for cl in self.solution_matrix]))
            # if minimize:
            #     if self._local_minimize_sat2(): 
            #         print("minimized changed")
                #    continue
                
            if self._check_formula_validity([(ifa, sort) for (ifa, sort, _) in self.solution_prefix], self.solution_matrix, self.constraints):
                # while minimize and self._local_minimize_sat(): pass
                # if self._local_minimize_sat2(): 
                #     continue
                print("formula is correct")
                return self._to_formula()
            # otherwise, _check_formula_validity has added constraints
            if self._debug:
                print(f"expanded nodes: {self._node_count}/{sum(len(model.elems) ** d for model in self._models for d in range(self._depth + 1))}")
    
    def _local_minimize_sat(self) -> None:
        v_i_s = [v.i for (cube, lit), v in self._literal_sat_vars.items() if lit//2 != len(self.atoms) - 1]
            
        while True:
            assignment = self._solver.assignment(v_i_s)
            present_literals: List[int] = [v_i for t, v_i in zip(assignment, v_i_s) if t]
            not_present_literals: List[int] = [-v_i for t, v_i in zip(assignment, v_i_s) if not t]

            random.shuffle(present_literals)
            for p in present_literals:
                ret, _ = self._solver.solve([*not_present_literals, -p], model=False)
                if ret == True:
                    if self._debug:
                        print(f"Found smaller solution")
                    break
            else:
                self.solution_prefix, self.solution_matrix = self._extract_formula()
                return

    def _to_formula(self) -> Formula:
        # Classic version:
        f: Formula = SimplifyingAnd(*(SimplifyingOr(*(self.literals[i] for i in cl)) for cl in self.solution_matrix))
        vars_used = set(free_vars(f))
        for is_forall, sort, name in reversed(self.solution_prefix):
            if name in vars_used:
                f = (Forall if is_forall else Exists)(name, self._sig.sort_names[sort], f)
        return f



    def _literal_value(self, lit: int, model: Model, mapping: Dict[str, int]) -> Optional[bool]:
        is_defined = all((v in mapping or v in model.constants) for v in vars_of(self.literals[lit]))
        return check(self.literals[lit], model, mapping) if is_defined else None
            
    def _cnf_matrix_value(self, matrix_list: List[List[int]], model: Model, mapping: Dict[str, int] = {}) -> Optional[bool]:
        """Returns `True`/`False` if the matrix's value is determined on model, or `None` if it is not determined"""
        return _ternary_and(_ternary_or(self._literal_value(lit, model, mapping) for lit in cl) for cl in matrix_list)
        
    def _check_formula_validity(self, prefix: List[Quantifier], matrix_list: List[List[int]],
                                constraints: List[Constraint]) -> bool:
        depth = len(prefix)
        
        _matrix_value_cache: Dict[int, Optional[bool]] = {}
        def matrix_value_fo_type(fo_type: int) -> Optional[bool]:
            if fo_type not in _matrix_value_cache:
                (model_i, assignment) = self._collapse_cache.get_example(fo_type)
                mapping = {v: e for v,e in zip(self.prefix_var_names, assignment)}
                _matrix_value_cache[fo_type] = self._cnf_matrix_value(matrix_list, self._models[model_i], mapping)
            return _matrix_value_cache[fo_type]

        def check_assignment(asgn: Tuple[int, ...], model: Model) -> bool:
            if len(asgn) == depth:
                mapping = {v: e for v,e in zip(self.prefix_var_names, asgn)}
                value = self._cnf_matrix_value(matrix_list, model, mapping)
                assert value is not None
                return value
            
                # return check(matrix, model, {v: e for v,e in zip(self.prefix_var_names, asgn)})
            else:
                (is_forall, sort) = prefix[len(asgn)]
                univ = model.elems_of_sort[self._sig.sort_names[sort]]
                return (all if is_forall else any)(check_assignment((*asgn, e), model) for e in univ)

        def expand_to_prove(n: InstNode3, expected: bool) -> bool:
            matrix_value = matrix_value_fo_type(n.fo_type)
            if len(n.instantiation) == depth:
                assert matrix_value is not None
                return expected is matrix_value
            # we aren't at the base, but check the rest of the quantifiers and return if they match
            if matrix_value is expected or check_assignment(n.instantiation, self._models[n.model_i]) == expected:
                return True

            is_forall, sort = prefix[len(n.instantiation)]
            self._expand_node(n, sort)
            if 'showexpansions' in self._expt_flags:
                print(f"Expanded node {n}")
            for c in n.children:
                expand_to_prove(c, expected)
            return False

        _root_node_cache: Dict[int, bool] = {}
        def root_node_value(n: int) -> bool:
            if n not in _root_node_cache:
                _root_node_cache[n] = check_assignment((), self._models[n])
            return _root_node_cache[n]

        def swap_to_front(c: int) -> None:
            if c > 0:
                constraints[c - 1], constraints[c] = constraints[c], constraints[c - 1]
            #constraints[:] = [constraints[c]] + constraints[:c] + constraints[c+1:]
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
