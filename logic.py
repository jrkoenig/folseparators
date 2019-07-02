
from collections import defaultdict
import itertools

reserved_names = ["sort", "relation", "constant", "function", "axiom", "model", "forall", "exists", "and", "or", "not", "implies", "="]

# Represents the signature part of a FOL structure, such as sorts, functions, etc.
class Signature(object):
    def __init__(self):
        self.sorts = set()
        self.relations = {}
        self.constants = {}
        self.functions = {}
    def is_free_name(self, n):
        if n in reserved_names or n in self.sorts or n in self.relations or n in self.constants or n in self.functions:
            return False
        return True
    def __repr__(self):
        return "\n".join(["Signature:", repr(self.sorts), repr(self.relations), repr(self.constants), repr(self.functions)])

class Environment(object):
    def __init__(self, sig):
        self.sig = sig
        self.bound = {}
        self.stack = []
    def bind(self, v, sort):
        self.bound[v] = sort
        self.stack.append(v)
    def pop(self):
        v = self.stack[-1]
        self.stack.pop()
        del self.bound[v]
    def lookup_var(self, x):
        if x in self.bound:
            return self.bound[x]
        elif x in self.sig.constants:
            return self.sig.constants[x]
        else:
            return None

# Formula types: And, Or, Not, Exists, Forall, Equal, Relation
class Formula(object):
    def __eq__(self, other):
        assert isinstance(other, Formula)
        if self._priority() != other._priority():
            return False
        if isinstance(self, Equal):
            return self.args == other.args
        elif isinstance(self, Relation):
            return self.rel == other.rel and self.args == other.args
        elif isinstance(self, Not):
            return self.f == other.f
        elif isinstance(self, And):
            return self.c == other.c
        elif isinstance(self, Or):
            return self.c == other.c
        else:
            assert False
    def __lt__(self, other):
        assert isinstance(other, Formula)
        if self._priority() < other._priority():
            return True
        if self._priority() > other._priority():
            return False
        if isinstance(self, Equal):
            return self.args < other.args
        elif isinstance(self, Relation):
            return self.rel < other.rel and self.args < other.args
        elif isinstance(self, Not):
            return self.f < other.f
        elif isinstance(self, And):
            return self.c < other.c
        elif isinstance(self, Or):
            return self.c < other.c
        else:
            assert False




class And(Formula):
    def __init__(self, conjuncts):
        self.c = conjuncts
    def __repr__(self):
        if len(self.c) == 0:
            return "true"
        return "(" + " & ".join(map(repr, self.c)) + ")"
    def _priority(self): return 3
class Or(Formula):
    def __init__(self, disjuncts):
        self.c = disjuncts
    def __repr__(self):
        if len(self.c) == 0:
            return "false"
        return "(" + " | ".join(map(repr, self.c)) + ")"
    def _priority(self): return 2
class Not(Formula):
    def __init__(self, formula):
        self.f = formula
    def __repr__(self):
        return "~(" + repr(self.f) + ")"
    def _priority(self): return 4
class Exists(Formula):
    def __init__(self, var, sort, formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __repr__(self):
        return "exists "+self.var+":"+self.sort+". " + repr(self.f)
class Forall(Formula):
    def __init__(self, var, sort, formula):
        self.var = var
        self.sort = sort
        self.f = formula
    def __repr__(self):
        return "forall "+self.var+":"+self.sort+". " + repr(self.f)
class Equal(Formula):
    def __init__(self, a, b):
        self.args = [a,b]
    def __repr__(self):
        return " = ".join(map(repr, self.args))
    def _priority(self): return 0
class Relation(Formula):
    def __init__(self, r, args):
        self.rel = r
        self.args = args
    def __repr__(self):
        return self.rel + "(" + ", ".join(map(repr, self.args)) + ")"
    def _priority(self): return 1

# Term types: variable (constant or bound variable), function
class Term(object):
    def __lt__(self, other):
        assert isinstance(other, Term)
        if self._priority() < other._priority():
            return True
        elif self._priority() > other._priority():
            return False
        else:
            if isinstance(self, Var):
                return self.var < other.var
            if isinstance(self, Func):
                if self.f < other.f and self.args < other.args:
                    return True
            return False


class Var(Term):
    def __init__(self, s):
        self.var = s
    def __repr__(self):
        return self.var
    def __eq__(self, other):
        return isinstance(other, Var) and self.var == other.var
    def _priority(self): return 0
class Func(Term):
    def __init__(self, f, args):
        self.f = f
        self.args = args
    def __repr__(self):
        return self.f + "(" + ", ".join(map(repr, self.args)) + ")"
    def __eq__(self, other):
        return isinstance(other, Func) and self.f == other.f and len(self.args) == len(other.args) and self.args == other.args
    def _priority(self): return 1

class Model(object):
    def __init__(self, sig):
        self.label = ""
        self.names = []
        self.elems = {}
        self.sorts = []
        self.elems_of_sort = defaultdict(list)
        self.constants = {}
        self.relations = dict([(r, set()) for r in sig.relations])
        self.functions = dict([(f, dict()) for f in sig.functions])
    def add_elem(self, name, sort):
        if name in self.elems:
            return None
        self.elems[name] = len(self.names)
        self.elems_of_sort[sort].append(len(self.names))
        self.sorts.append(sort)
        self.names.append(name)
        return True
    def sort_of(self, name):
        if name in self.elems:
            return self.sorts[self.elems[name]]
        else:
            return None
    def add_constant(self, name, elem):
        if name in self.constants:
            return False
        self.constants[name] = self.elems[elem]
        return True
    def add_relation(self, rel, args):
        self.relations[rel].add(tuple(self.elems[a] for a in args))
    def add_function(self, func, args, result):
        self.functions[func][tuple(self.elems[a] for a in args)] = self.elems[result]
    def __repr__(self):
        r = "Model:\nElems: "+ ", ".join([n + ":"+ s for n,s in zip(self.names, self.sorts)]) + "\n"
        for c, e in self.constants.items():
            r += c + " = " + self.names[e] + "\n"
        r += "\n".join([rel + "(" + ", ".join([self.names[i] for i in e]) + ")" for rel, es in self.relations.items() for e in es])
        return r
    def __str__(self):
        return print_model(self)

def model_complete_wrt_sig(model, sig):
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

def print_model(model):
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
    return "(model {}\n  {}\n{}\n)".format(model.label, elems, "\n".join(["  "+f for f in facts]))
