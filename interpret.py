
from parse import parse, Atom, List
from logic import *

def error_at(desc, node):
    raise RuntimeError(desc + " at " + str(node.loc[0]) + ":" + str(node.loc[1]))


def term(env, token):
    if isinstance(token, Atom):
        sort = env.lookup_var(token.name())
        if sort is None:
            error_at("Symbol not bound", token)
        return (Var(token.name()), sort)
    else:
        if len(token) == 0: error_at("Term must not be empty", token)
        f = token[0]
        if isinstance(f, Atom) and f.name() in env.sig.functions:
            expected_sorts, ret_sort = env.sig.functions[f.name()]
            args = [term(env, t) for t in token[1:]]
            if len(args) != len(expected_sorts):
                error_at("Function has wrong arity", f)
            for es, (_, arg_sort), i in zip(expected_sorts, args, range(1, len(token))):
                if es != arg_sort:
                    error_at("Sort mismatch", token[i])
            return (Func(f.name(), [a[0] for a in args]), ret_sort)
        else:
            error_at("Expected a function symbol", f)


def formula(env, token):
    if isinstance(token, Atom) or len(token) == 0 or not isinstance(token[0], Atom):
        error_at("Invalid formula", token)
    head = token[0]
    # check for and
    if head.name() == "and":
        return And([formula(env, t) for t in token[1:]])
    # check for or
    if head.name() == "or":
        return Or([formula(env, t) for t in token[1:]])
    # check for not
    if head.name() == "not":
        if len(token) != 2:
            error_at("Not takes exactly one argument", token)
        return Not(formula(env, token[1]))
    # check for forall, exists
    if head.name() == "forall" or head.name() == "exists":
        if len(token) != 4:
            error_at("Quantifiers must have variable, sort, and sub-formula", token)
        v = token[1]
        sort = token[2]
        if not isinstance(v, Atom) or env.lookup_var(v.name()) is not None:
            error_at("Must be an unbound variable", v)
        if not isinstance(sort, Atom) or sort.name() not in env.sig.sorts:
            error_at("Must be a sort", sort)
        env.bind(v.name(), sort.name())
        f = formula(env, token[3])
        env.pop()
        if head.name() == "forall":
            return Forall(v.name(), sort.name(), f)
        else:
            return Exists(v.name(), sort.name(), f)

    # check for =
    if head.name() == "=":
        if len(token) != 3:
            error_at("Equality is binary", token)
        [a,b] = [term(env, t) for t in token[1:3]]
        if a[1] != b[1]:
            error_at("Equality must be between terms of the same sort", token)
        return Equal(a[0], b[0])

    # check for relation
    if head.name() in env.sig.relations:
        expected_sorts = env.sig.relations[head.name()]
        if len(expected_sorts) != len(token) - 1:
            error_at("Relation has incorrect arity", head)
        args = [term(env, t) for t in token[1:]]
        for es, (_, term_sort), src in zip(expected_sorts, args, token[1:]):
            if (es != term_sort):
                error_at("Sort mismatch", src)
        return Relation(head.name(), [a[0] for a in args])
    error_at("Invalid formaula", token)

# From the List of commands, intepret the definitions to construct a representation
# of the signature, axioms and models
def interpret(commands):
    sig = Signature()

    # Helper to turn a list of Atoms into a list of sort names, checking that each is defined
    def sort_list(l):
        resolved_sorts = []
        for s in l:
            if isinstance(s, Atom) and s.name() in sig.sorts:
                resolved_sorts.append(s.name())
            else:
                error_at("Must be sort", s)
        return resolved_sorts
    def is_free_name(token):
        return isinstance(token, Atom) and sig.is_free_name(token.name())
    axioms = []
    conjectures = []
    models = []

    in_sig = True
    for c in commands:
        if isinstance(c, List) and isinstance(c[0], Atom):
            command = c[0].name()

            if command == "sort":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) == 2 and is_free_name(c[1]):
                    sig.sorts.add(c[1].name())
                else:
                    error_at("Sort must define one non-reserved name", c)

            elif command == "relation":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) >= 3 and is_free_name(c[1]):
                    sig.relations[c[1].name()] = sort_list(c[2:])
                else:
                    error_at("Invalid relation definition", c)

            elif command == "constant":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) == 3 and is_free_name(c[1]):
                    sig.constants[c[1].name()] = sort_list(c[2:])[0]
                else:
                    error_at("Invalid constant definition", c)

            elif command == "function":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) >= 4 and is_free_name(c[1]):
                    function_sort = sort_list(c[2:])
                    sig.functions[c[1].name()] = (function_sort[:-1], function_sort[-1])
                else:
                    error_at("Invalid function definition", c)

            elif command == "axiom":
                if len(c) != 2:
                    error_at("Invalid axiom definition", c)
                env = Environment(sig)
                axioms.append(formula(env, c[1]))
                in_sig = False
            elif command == "conjecture":
                if len(c) != 2:
                    error_at("Invalid conjecture definition", c)
                env = Environment(sig)
                conjectures.append(formula(env, c[1]))
                in_sig = False

            elif command == "model":
                in_sig = False
                m = Model(sig)
                if len(c) < 2 or not isinstance(c[1], Atom):
                    error_at("Model must have label", c[1])
                m.label = c[1].name()
                if len(c) < 3 or not isinstance(c[2], List):
                    error_at("Model must have list of elements/sorts",c)
                for pair in c[2]:
                    if not isinstance(pair, List) or len(pair) != 2 or not is_free_name(pair[0]) or not (isinstance(pair[1], Atom) and pair[1].name() in sig.sorts):
                        error_at("Elements must be (name SORT)", pair)
                    if m.add_elem(pair[0].name(), pair[1].name()) is None:
                        error_at("Element names must be unique", pair[0])
                for fact in c[3:]:
                    if len(fact) == 0 or not isinstance(fact[0], Atom):
                        error_at("Invalid model fact", fact)
                    fact_root = fact[0].name()
                    if fact_root in sig.relations:
                        expected_sorts = sig.relations[fact_root]
                        if len(fact) != len(expected_sorts) + 1:
                            error_at("Wrong relation arity", fact)
                        for arg, e_s in zip(fact[1:], expected_sorts):
                            if not isinstance(arg, Atom) or m.sort_of(arg.name()) != e_s:
                                error_at("Incorrect sort", arg)
                        m.add_relation(fact_root, [arg.name() for arg in fact[1:]])
                    elif fact_root == "=":
                        if len(fact) != 3:
                            error_at("Equality is binary", fact)
                        if isinstance(fact[1], Atom) and fact[1].name() in sig.constants:
                            if not isinstance(fact[2], Atom) or m.sort_of(fact[2].name()) != sig.constants[fact[1].name()]:
                                error_at("Constant must be assigned a model element with the right sort", fact[1])
                            m.add_constant(fact[1].name(), fact[2].name())
                        elif isinstance(fact[1], List) and len(fact[1]) > 0 and fact[1][0].name() in sig.functions:
                            func_name = fact[1][0].name()
                            (arg_sorts, expected_sort) = sig.functions[fact[1][0].name()]
                            arg_names = []
                            for i, arg_sort in enumerate(arg_sorts):
                                if i+1 >= len(fact[1]):
                                    error_at("Expected function argument", fact[1])
                                arg_name = fact[1][i+1]
                                if not isinstance(arg_name, Atom) or m.sort_of(arg_name.name()) != arg_sort:
                                    error_at("Function argument must be element of correct sort", arg_name)
                                arg_names.append(arg_name.name())
                            if not isinstance(fact[2], Atom) or m.sort_of(fact[2].name()) != expected_sort:
                                error_at("Function assignment must be a model element with the right sort", fact[1])
                            result_name = fact[2].name()
                            m.add_function(func_name, arg_names, result_name)
                        else:
                            error_at("Equality not of correct form", fact)
                    else:
                        error_at("Unrecognized fact in model", fact)
                if not model_complete_wrt_sig(m, sig):
                    error_at("Model is not complete with respect to signature (missing constant/function definitions?)", c)
                models.append(m)
            else:
                error_at("Unexpected Command", c)
        else:
            error_at("Unexpected Command", c)

    return (sig, axioms, conjectures, models)

if __name__=="__main__":
    import sys
    if len(sys.argv) not in [1,2]:
        print("Usage: python3 interpret.py [file.fol]")
        exit(1)
    file = "problems/node_has_edge.fol" if len(sys.argv) == 1 else sys.argv[1]
    (sig, axioms, conjectures, models) = interpret(parse(open(file).read()))


    print(sig)
    for ax in axioms:
        print("Axiom:", ax)
    for ax in conjectures:
        print("Conjecture:", ax)
    for m in models:
        print(m)
