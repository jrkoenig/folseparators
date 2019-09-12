
from .logic import *

def resolve_term(term, model):
    if isinstance(term, Var):
        return model.constants[term.var]
    elif isinstance(term, Func):
        return model.functions[term.f][tuple([resolve_term(a, model) for a in term.args])]
    else: assert False

def check(formula, model):
    if isinstance(formula, And):
        for f in formula.c:
            if not check(f, model):
                return False
        return True
    elif isinstance(formula, Or):
        for f in formula.c:
            if check(f, model):
                return True
        return False
    elif isinstance(formula, Not):
        return not check(formula.f, model)
    elif isinstance(formula, Equal):
        return resolve_term(formula.args[0], model) == resolve_term(formula.args[1], model)
    elif isinstance(formula, Relation):
        elems = [resolve_term(t, model) for t in formula.args]
        return tuple(elems) in model.relations[formula.rel]
    elif isinstance(formula, Forall):
        universe = model.elems_of_sort[formula.sort]
        for e in universe:
            assert(formula.var not in model.constants)
            model.constants[formula.var] = e
            truth = check(formula.f, model)
            del model.constants[formula.var]
            if not truth:
                return False
        return True
    elif isinstance(formula, Exists):
        universe = model.elems_of_sort[formula.sort]
        for e in universe:
            assert(formula.var not in model.constants)
            model.constants[formula.var] = e
            truth = check(formula.f, model)
            del model.constants[formula.var]
            if truth:
                return True
        return False
    else:
        raise RuntimeError("Formula is illformed")

if __name__ == "__main__":
    from interpret import interpret, SemanticError
    from parse import parse, SyntaxError
    import sys

    if len(sys.argv) not in [1,2]:
        print("Usage: python3 check.py [file.fol]")
        exit(1)

    filen = "problems/node_has_edge.fol" if len(sys.argv) == 1 else sys.argv[1]
    print("Checking", filen)
    try:

        (sig, axioms, conjectures, models) = interpret(parse(open(filen).read()))
        for model in models:
            for axiom in axioms:
                if not check(axiom, model):
                    print("Model does not meet axiom!")
                    print(axiom)
                    print(model)
    except SemanticError as e:
        print(e)
    except SyntaxError as e:
        print(e)
