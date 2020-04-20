
from .logic import *

def resolve_term(term: Term, model: Model, assumptions: Dict[str, int] = {}) -> int:
    if isinstance(term, Var):
        if term.var in assumptions:
            return assumptions[term.var]
        elif term.var in model.constants:
            c = model.constants[term.var]
            assert c is not None
            return c
        else:
            raise RuntimeError(f"variable {term.var} not defined")
    elif isinstance(term, Func):
        return model.functions[term.f][tuple([resolve_term(a, model, assumptions) for a in term.args])]
    else: assert False

def check(formula: Formula, model: Model, assumptions: Dict[str, int] = {}) -> bool:
    if isinstance(formula, And):
        for f in formula.c:
            if not check(f, model, assumptions):
                return False
        return True
    elif isinstance(formula, Or):
        for f in formula.c:
            if check(f, model, assumptions):
                return True
        return False
    elif isinstance(formula, Not):
        return not check(formula.f, model, assumptions)
    if isinstance(formula, Iff):
        return check(formula.c[0], model, assumptions) == check(formula.c[1], model, assumptions)
    elif isinstance(formula, Equal):
        return resolve_term(formula.args[0], model, assumptions) == \
               resolve_term(formula.args[1], model, assumptions)
    elif isinstance(formula, Relation):
        elems = tuple(resolve_term(t, model, assumptions) for t in formula.args)
        assert elems in model.relations[formula.rel]
        return model.relations[formula.rel][elems]
    elif isinstance(formula, Forall):
        universe = model.elems_of_sort[formula.sort]
        for e in universe:
            if not check(formula.f, model, {**assumptions, formula.var: e}):
                return False
        return True
    elif isinstance(formula, Exists):
        universe = model.elems_of_sort[formula.sort]
        for e in universe:
            if check(formula.f, model, {**assumptions, formula.var: e}):
                return True
        return False
    else:
        raise RuntimeError("Formula is illformed")
