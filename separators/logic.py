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

from collections import defaultdict
import itertools
from typing import Optional, Set, Dict, List, Tuple, DefaultDict, Iterable, Iterator

reserved_names = ["", "sort", "relation", "constant", "function", "axiom", "model", "forall", "exists", "and", "or", "not", "implies", "iff", "="]

# Represents the signature part of a FOL structure, such as sorts, functions, etc.
class Signature(object):
    def __init__(self) -> None:
        self.sorts: Set[str] = set()
        self.sort_names: List[str] = []
        self.sort_indices: Dict[str, int] = {}
        self.relations: Dict[str, List[str]] = {}
        self.constants: Dict[str, str] = {}
        self.functions: Dict[str, Tuple[List[str], str]] = {}
    def is_free_name(self, n: str) -> bool:
        if n in reserved_names or n in self.sorts or n in self.relations or n in self.constants or n in self.functions:
            return False
        return True
    def all_names(self) -> Iterable[str]:
        return itertools.chain(self.sort_names, self.constants.keys(), self.relations.keys(), self.functions.keys())
    def finalize_sorts(self) -> None:
        self.sort_indices = {}
        self.sort_names = []
        for s in sorted(self.sorts):
            self.sort_indices[s] = len(self.sort_names)
            self.sort_names.append(s)
    def __repr__(self) -> str:
        return "; Sig\n" + "\n".join(
            itertools.chain(
              (f"(sort {s})" for s in self.sort_names),
              (f"(constant {c} {s})" for (c, s) in sorted(self.constants.items())),
              (f"(relation {r} {' '.join(ss)})" for (r, ss) in sorted(self.relations.items())),
              (f"(function {f} {' '.join(ss)} {s})" for (f, (ss, s)) in sorted(self.functions.items()))
            )) + "\n"

class Environment(object):
    def __init__(self, sig: Signature):
        self.sig = sig
        self.bound: Dict[str, List[str]] = {}
        self.stack: List[str] = []
    def bind(self, v: str, sort: str) -> None:
        self.bound.setdefault(v, [])
        self.bound[v].append(sort)
        self.stack.append(v)
    def pop(self) -> None:
        v = self.stack[-1]
        self.stack.pop()
        self.bound[v].pop()
    def lookup_var(self, x: str) -> Optional[str]:
        if x in self.bound and len(self.bound[x]) > 0:
            return self.bound[x][-1]
        elif x in self.sig.constants:
            return self.sig.constants[x]
        else:
            return None


# Term types: variable (constant or bound variable), function
class Term(object):
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Term): return NotImplemented
        return self._unpack() == other._unpack()
    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Term): return NotImplemented
        return self._unpack() < other._unpack()
    def _unpack(self) -> Tuple: return ()

class Var(Term):
    def __init__(self, v: str):
        self.var = v
    def __str__(self) -> str:
        return self.var
    def __repr__(self) -> str:
        return self.var
    def _unpack(self) -> Tuple: return ('0Var', self.var) # extra zero so vars before funcs
    def __hash__(self) -> int: return hash(self._unpack())


class Func(Term):
    def __init__(self, f: str, args: List[Term]):
        self.f = f
        self.args = args
    def __str__(self) -> str:
        return self.f + "(" + ", ".join(map(str, self.args)) + ")"
    def __repr__(self) -> str:
        return "(" + self.f + " " + " ".join(map(repr, self.args)) + ")"
    def _unpack(self) -> Tuple: return ('1Func', self.f, self.args)
    def __hash__(self) -> int: return hash(('1Func', self.f, tuple(map(hash, self.args))))


# Formula types: And, Or, Not, Exists, Forall, Equal, Relation
class Formula(object):
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Formula): return NotImplemented
        return self._unpack() == other._unpack()
    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Formula): return NotImplemented
        return self._unpack() < other._unpack()
    def _unpack(self) -> Tuple: return ()

class And(Formula):
    def __init__(self, conjuncts: List[Formula]):
        self.c = conjuncts
    def __str__(self) -> str:
        if len(self.c) == 0:
            return "true"
        if len(self.c) == 1:
            return str(self.c[0])
        return "(" + " & ".join(map(str, self.c)) + ")"
    def __repr__(self) -> str:
        return "(and " + " ".join(map(repr, self.c)) + ")"
    def _unpack(self) -> Tuple: return ("And", self.c)

class Or(Formula):
    def __init__(self, disjuncts: List[Formula]):
        self.c = disjuncts
    def __str__(self) -> str:
        if len(self.c) == 0:
            return "false"
        if len(self.c) == 1:
            return str(self.c[0])
        return "(" + " | ".join(map(str, self.c)) + ")"
    def __repr__(self) -> str:
        return "(or " + " ".join(map(repr, self.c)) + ")"
    def _unpack(self) -> Tuple: return ("Or", self.c)

class Not(Formula):
    def __init__(self, formula: Formula):
        self.f = formula
    def __str__(self) -> str:
        if isinstance(self.f, (Relation, Var)):
            return "~" + str(self.f)
        if isinstance(self.f, Equal):
            return str(self.f.args[0]) + " ~= " + str(self.f.args[1])
        return "~(" + str(self.f) + ")"
    def __repr__(self) -> str:
        return f"(not {repr(self.f)})"
    def _unpack(self) -> Tuple: return ("Not", self.f)

class Iff(Formula):
    def __init__(self, a: Formula, b: Formula):
        self.c = [a,b]
    def __str__(self) -> str:
        return "(" +  " <-> ".join(map(str, self.c)) + ")"
    def __repr__(self) -> str:
        return "(iff " +  " ".join(map(repr, self.c)) + ")"
    def _unpack(self) -> Tuple: return ("Iff", self.c)

class Exists(Formula):
    def __init__(self, var: str, sort: str, formula: Formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __str__(self) -> str:
        return "exists "+self.var+":"+self.sort+". " + str(self.f)
    def __repr__(self) -> str:
        return f"(exists {self.var} {self.sort} {repr(self.f)})"
    def _unpack(self) -> Tuple: return ("Exists", self.var, self.sort, self.f)

class Forall(Formula):
    def __init__(self, var: str, sort: str, formula: Formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __str__(self) -> str:
        return "forall "+self.var+":"+self.sort+". " + str(self.f)
    def __repr__(self) -> str:
        return f"(forall {self.var} {self.sort} {repr(self.f)})"
    def _unpack(self) -> Tuple: return ("Forall", self.var, self.sort, self.f)

class Equal(Formula):
    def __init__(self, a: Term, b: Term):
        self.args = [a,b]
    def __str__(self) -> str:
        return " = ".join(map(str, self.args))
    def __repr__(self) -> str:
        return f"(= {repr(self.args[0])} {repr(self.args[1])})"
    def _unpack(self) -> Tuple: return ("Equal", self.args)
    def __hash__(self) -> int: return hash(('Equal', tuple(map(hash, self.args))))

class Relation(Formula):
    def __init__(self, r:str, args: List[Term]):
        self.rel = r
        self.args = args
    def __str__(self) -> str:
        return self.rel + "(" + ", ".join(map(str, self.args)) + ")"
    def __repr__(self) -> str:
        return f"({self.rel} {' '.join(map(repr, self.args))})"
    def _unpack(self) -> Tuple: return ("Relation", self.rel, self.args)
    def __hash__(self) -> int: return hash(('Relation', self.rel, tuple(map(hash, self.args))))

def Implies(a: Formula, b: Formula) -> Formula:
    return Or([Not(a), b])

def rename_free_vars_term(t: Term, mapping: Dict[str, str]) -> Term:
    if isinstance(t, Var):
        return Var(mapping.get(t.var, t.var))
    elif isinstance(t, Func):
        return Func(t.f, [rename_free_vars_term(a, mapping) for a in t.args])
    else:
        raise RuntimeError("Term is illformed")
def rename_free_vars(f: Formula, mapping: Dict[str, str]) -> Formula:
    if isinstance(f, And) or isinstance(f, Or):
        return (And if isinstance(f, And) else Or)([rename_free_vars(c, mapping) for c in f.c])
    if isinstance(f, Iff):
        return Iff(*[rename_free_vars(c, mapping) for c in f.c])
    elif isinstance(f, Not):
        return Not(rename_free_vars(f.f, mapping))
    elif isinstance(f, Equal):
        return Equal(rename_free_vars_term(f.args[0], mapping), rename_free_vars_term(f.args[1], mapping))
    elif isinstance(f, Relation):
        return Relation(f.rel, [rename_free_vars_term(a, mapping) for a in f.args])
    elif isinstance(f, Forall) or isinstance(f, Exists):
        m = mapping if f.var not in mapping else dict((a,b) for a,b in mapping.items() if a != f.var)
        return (Forall if isinstance(f, Forall) else Exists)(f.var, f.sort, rename_free_vars(f.f, m))
    else:
        raise RuntimeError("Formula is illformed")

def free_vars_term(t: Term) -> Iterator[str]:
    if isinstance(t, Var):
        yield t.var
    elif isinstance(t, Func):
        for a in t.args:
            yield from free_vars_term(a)
    else:
        raise RuntimeError("Term is illformed")
def free_vars(f: Formula) -> Iterator[str]:
    if isinstance(f, And) or isinstance(f, Or) or isinstance(f, Iff):
        for c in f.c:
            yield from free_vars(c)
    elif isinstance(f, Not):
        yield from free_vars(f.f)
    elif isinstance(f, Equal):
        yield from free_vars_term(f.args[0])
        yield from free_vars_term(f.args[1])
    elif isinstance(f, Relation):
        for a in f.args:
            yield from free_vars_term(a)
    elif isinstance(f, Forall) or isinstance(f, Exists):
        for v in free_vars(f.f):
            if v != f.var:
                yield v
    else:
        raise RuntimeError("Formula is illformed")


def symbols_term(t: Term) -> Iterator[str]:
    if isinstance(t, Var):
        yield t.var
    elif isinstance(t, Func):
        yield t.f
        for a in t.args:
            yield from symbols_term(a)
    else:
        raise RuntimeError("Term is illformed")
def symbols(f: Formula) -> Iterator[str]:
    if isinstance(f, And) or isinstance(f, Or) or isinstance(f, Iff):
        for c in f.c:
            yield from symbols(c)
    elif isinstance(f, Not):
        yield from symbols(f.f)
    elif isinstance(f, Equal):
        yield "="
        yield from symbols_term(f.args[0])
        yield from symbols_term(f.args[1])
    elif isinstance(f, Relation):
        for a in f.args:
            yield from symbols_term(a)
    elif isinstance(f, Forall) or isinstance(f, Exists):
        yield from symbols(f.f)
    else:
        raise RuntimeError("Formula is illformed")

class Model(object):
    def __init__(self, sig: Signature):
        self.label = ""
        self.names: List[str] = []
        self.elems: Dict[str, int] = {}
        self.sorts: List[str] = []
        self.elems_of_sort: DefaultDict[str, List[int]] = defaultdict(list)
        self.elems_of_sort_index: List[List[int]] = [[] for i in range(len(sig.sort_names))]
        self.constants: Dict[str, Optional[int]] = dict([(c, None) for c in sig.constants])
        self.relations: Dict[str, Dict[Tuple[int, ...], bool]] = dict([(r, dict()) for r in sig.relations])
        self.functions: Dict[str, Dict[Tuple[int, ...], int]] = dict([(f, dict()) for f in sig.functions])
        self.constraints: List[Formula] = []
        self.sig = sig
    def add_elem(self, name: str, sort: str) -> bool:
        if name in self.elems:
            return False
        elem_id = len(self.names)
        self.elems[name] = elem_id
        self.elems_of_sort[sort].append(elem_id)
        self.elems_of_sort_index[self.sig.sort_indices[sort]].append(elem_id)        
        self.sorts.append(sort)
        self.names.append(name)
        return True
    def sort_of(self, name: str) -> Optional[str]:
        if name in self.elems:
            return self.sorts[self.elems[name]]
        else:
            return None
    def add_constant(self, name: str, elem: Optional[str]) -> bool:
        if name in self.constants and self.constants[name] is not None:
            return False
        self.constants[name] = self.elems[elem] if elem is not None else None
        return True
    def add_relation(self, rel: str, args: List[str], value: bool = True) -> None:
        self.relations[rel][tuple(self.elems[a] for a in args)] = value
    def add_function(self, func: str, args: List[str], result: str) -> None:
        self.functions[func][tuple(self.elems[a] for a in args)] = self.elems[result]
    def __str__(self) -> str:
        return print_model(self)
    def universe(self, sort:str) -> Iterable[str]:
        return (self.names[i] for i in self.elems_of_sort[sort])
    def copy(self) -> 'Model':
        m = Model(self.sig)
        m.label = self.label
        for n, s in zip(self.names, self.sorts):
            m.add_elem(n, s)
        m.constants = dict(self.constants)
        for r in self.relations:
            m.relations[r] = dict(self.relations[r])
        for f in self.functions:
            m.functions[f] = dict(self.functions[f])
        m.constraints = list(self.constraints)
        return m

def model_is_complete_wrt_sig(model: Model, sig: Signature) -> bool:
    for sort in sig.sorts:
        if len(model.elems_of_sort[sort]) == 0:
            return False
    for c in sig.constants.keys():
        if c not in model.constants:
            return False
        if model.constants[c] is None:
            return False
    for rel, (sorts) in sig.relations.items():
        if rel not in model.relations:
            return False
        interp = model.relations[rel]
        for t in itertools.product(*[model.elems_of_sort[sort] for sort in sorts]):
            if t not in interp:
                return False
    for func, (sorts, ret_sort) in sig.functions.items():
        if func not in model.functions:
            return False
        repr = model.functions[func]
        for t in itertools.product(*[model.elems_of_sort[sort] for sort in sorts]):
            if t not in repr:
                return False
    for func in model.functions:
        if func not in sig.functions:
            return False
    for c in model.constants:
        if c not in sig.constants:
            return False
    for rel in model.relations:
        if rel not in sig.relations:
            return False
    return True

def model_is_partial_wrt_sig(model: Model, sig: Signature) -> bool:
    for sort in sig.sorts:
        if len(model.elems_of_sort[sort]) == 0:
            return False
    for c in sig.constants.keys():
        if c not in model.constants:
            return False
    for rel in sig.relations.keys():
        if rel not in model.relations:
            return False
    for func, (sorts, ret_sort) in sig.functions.items():
        if func not in model.functions:
            return False
    for func in model.functions:
        if func not in sig.functions:
            return False
    for c in model.constants:
        if c not in sig.constants:
            return False
    for rel in model.relations:
        if rel not in sig.relations:
            return False
    return True
    

def print_model(model: Model) -> str:
    elems = "("+" ".join(["({} {})".format(model.names[i], model.sorts[i]) for i in range(len(model.names))])+")"
    facts = []
    for c, e in sorted(model.constants.items()):
        if e is not None:
            facts.append("(= {} {})".format(c, model.names[e]))
    for rel, rinterp in sorted(model.relations.items()):
        for t, v in sorted(rinterp.items()):
            call = "({} {})".format(rel, " ".join([model.names[i] for i in t]))
            facts.append(call if v else f"(not {call})")
        for t in itertools.product(*[model.elems_of_sort[sort] for sort in model.sig.relations[rel]]):
            if t not in rinterp:
                call = "({} {})".format(rel, " ".join([model.names[i] for i in t]))
                facts.append(f"; {call} is arbitrary")
    for func, finterp in model.functions.items():
        for args, result in finterp.items():
            facts.append("(= ({} {}) {})".format(func, " ".join([model.names[i] for i in args]), model.names[result]))
        for t in itertools.product(*[model.elems_of_sort[sort] for sort in model.sig.functions[func][0]]):
            if t not in finterp:
                call = "({} {})".format(func, " ".join([model.names[i] for i in t]))
                facts.append(f"; {call} is arbitrary")
    for constraint in model.constraints:
        facts.append(f"; constraint: {constraint}")
    return "(model {}\n  {}\n{}\n)".format(model.label, elems, "\n".join(["  "+f for f in facts]))
