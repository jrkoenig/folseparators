
from collections import defaultdict
import itertools
from typing import Optional, Set, Dict, List, Tuple, DefaultDict, Iterable

reserved_names = ["", "sort", "relation", "constant", "function", "axiom", "model", "forall", "exists", "and", "or", "not", "implies", "="]

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
        self.bound: Dict[str, str] = {}
        self.stack: List[str] = []
    def bind(self, v: str, sort: str) -> None:
        self.bound[v] = sort
        self.stack.append(v)
    def pop(self) -> None:
        v = self.stack[-1]
        self.stack.pop()
        del self.bound[v]
    def lookup_var(self, x: str) -> Optional[str]:
        if x in self.bound:
            return self.bound[x]
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
    def __repr__(self) -> str:
        return self.var
    def _unpack(self) -> Tuple: return ('0Var', self.var) # extra zero so vars before funcs
    def __hash__(self) -> int: return hash(self._unpack())


class Func(Term):
    def __init__(self, f: str, args: List[Term]):
        self.f = f
        self.args = args
    def __repr__(self) -> str:
        return self.f + "(" + ", ".join(map(repr, self.args)) + ")"
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
    def __repr__(self) -> str:
        if len(self.c) == 0:
            return "true"
        if len(self.c) == 1:
            return repr(self.c[0])
        return "(" + " & ".join(map(repr, self.c)) + ")"
    def _unpack(self) -> Tuple: return ("And", self.c)

class Or(Formula):
    def __init__(self, disjuncts: List[Formula]):
        self.c = disjuncts
    def __repr__(self) -> str:
        if len(self.c) == 0:
            return "false"
        if len(self.c) == 1:
            return repr(self.c[0])
        return "(" + " | ".join(map(repr, self.c)) + ")"
    def _unpack(self) -> Tuple: return ("Or", self.c)

class Not(Formula):
    def __init__(self, formula: Formula):
        self.f = formula
    def __repr__(self) -> str:
        if isinstance(self.f, (Relation, Var)):
            return "~" + repr(self.f)
        if isinstance(self.f, Equal):
            return repr(self.f.args[0]) + " ~= " + repr(self.f.args[1])
        return "~(" + repr(self.f) + ")"
    def _unpack(self) -> Tuple: return ("Not", self.f)

class Exists(Formula):
    def __init__(self, var: str, sort: str, formula: Formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __repr__(self) -> str:
        return "exists "+self.var+":"+self.sort+". " + repr(self.f)
    def _unpack(self) -> Tuple: return ("Exists", self.var, self.sort, self.f)

class Forall(Formula):
    def __init__(self, var: str, sort: str, formula: Formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __repr__(self) -> str:
        return "forall "+self.var+":"+self.sort+". " + repr(self.f)
    def _unpack(self) -> Tuple: return ("Forall", self.var, self.sort, self.f)

class Equal(Formula):
    def __init__(self, a: Term, b: Term):
        self.args = [a,b]
    def __repr__(self) -> str:
        return " = ".join(map(repr, self.args))
    def _unpack(self) -> Tuple: return ("Equal", self.args)
    def __hash__(self) -> int: return hash(('Equal', tuple(map(hash, self.args))))

class Relation(Formula):
    def __init__(self, r:str, args: List[Term]):
        self.rel = r
        self.args = args
    def __repr__(self) -> str:
        return self.rel + "(" + ", ".join(map(repr, self.args)) + ")"
    def _unpack(self) -> Tuple: return ("Relation", self.rel, self.args)
    def __hash__(self) -> int: return hash(('Relation', self.rel, tuple(map(hash, self.args))))


class Model(object):
    def __init__(self, sig: Signature):
        self.label = ""
        self.names: List[str] = []
        self.elems: Dict[str, int] = {}
        self.sorts: List[str] = []
        self.elems_of_sort: DefaultDict[str, List[int]] = defaultdict(list)
        self.constants: Dict[str, int] = {}
        self.relations: Dict[str, Set[Tuple]] = dict([(r, set()) for r in sig.relations])
        self.functions: Dict[str, Dict[Tuple, int]] = dict([(f, dict()) for f in sig.functions])
    def add_elem(self, name: str, sort: str) -> bool:
        if name in self.elems:
            return False
        self.elems[name] = len(self.names)
        self.elems_of_sort[sort].append(len(self.names))
        self.sorts.append(sort)
        self.names.append(name)
        return True
    def sort_of(self, name: str) -> Optional[str]:
        if name in self.elems:
            return self.sorts[self.elems[name]]
        else:
            return None
    def add_constant(self, name: str, elem: str) -> bool:
        if name in self.constants:
            return False
        self.constants[name] = self.elems[elem]
        return True
    def add_relation(self, rel: str, args: List[str]) -> None:
        self.relations[rel].add(tuple(self.elems[a] for a in args))
    def add_function(self, func: str, args: List[str], result: str) -> None:
        self.functions[func][tuple(self.elems[a] for a in args)] = self.elems[result]
    def __str__(self) -> str:
        return print_model(self)

def model_complete_wrt_sig(model: Model, sig: Signature) -> bool:
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
        repr = model.functions[func]
        for t in itertools.product(*[model.elems_of_sort[sort] for sort in sorts]):
            if t not in repr:
                return False
    return True

def print_model(model: Model) -> str:
    elems = "("+" ".join(["({} {})".format(model.names[i], model.sorts[i]) for i in range(len(model.names))])+")"
    facts = []
    for c, e in sorted(model.constants.items()):
        facts.append("(= {} {})".format(c, model.names[e]))
    for rel, tuples in sorted(model.relations.items()):
        for t in sorted(tuples):
            facts.append("({} {})".format(rel, " ".join([model.names[i] for i in t])))
    for func, repr in model.functions.items():
        for args, result in repr.items():
            facts.append("(= ({} {}) {})".format(func, " ".join([model.names[i] for i in args]), model.names[result]))
    return "(model {}\n  {}\n{}\n)\n".format(model.label, elems, "\n".join(["  "+f for f in facts]))
