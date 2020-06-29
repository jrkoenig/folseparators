
from separators.separate import *
from separators.learn import *
from separators.parse import parse
from separators.interpret import interpret

def test_partial() -> None:
    fol = interpret(parse('''
    (sort N)
    (relation r N N)
    (model + 
        ((e0 N) (e1 N) (e2 N))
        (r e0 e0)
        (r e0 e1)
        (r e0 e2)
        (r e1 e0)
        (r e1 e1)
        (r e1 e2)
        (r e2 e0)
        (r e2 e1)
    )
    (conjecture (forall x N (forall y N (r x y))))
    (conjecture (forall x N (forall y N (not (r x y)))))
    (conjecture (forall x N (forall y N (or (r x y) (r y x)))))
    (conjecture (forall x N (forall y N (or (= x y) (r x y) (r y x)))))
    (conjecture (exists x N (exists y N (or (r x y)))))
    (conjecture (exists x N (r x x)))
    (conjecture (exists x N (not (r x x))))
    '''))
    print(fol.models[0])
    for conj,expected in zip(fol.conjectures, [False, False, False, True, True, True, False]):
        value = check_partial(Completion(PartialModel(fol.models[0])), conj)
        print("Conjecture", conj, " = ", value)
        assert value == expected

def test_sep() -> None:
    fol = interpret(parse('''
    (sort N)
    (relation r N N)
    (constant a N)
    (model + 
        ((e0 N) (e1 N))
        (r e0 e0)
        (r e0 e1)
        (r e1 e0)
        (= a e1)
    )
    (model + 
        ((e0 N) (e1 N))
        (r e0 e0)
        (r e0 e1)
        (r e1 e0)
    )
    (model + 
        ((e0 N) (e1 N))
        (r e0 e0)
        (r e0 e1)
        (r e1 e0)
        (= a e0)
    )
    (model - 
        ((e0 N) (e1 N))
        (not (r e0 e0))
        (not (r e1 e1))
    )
    (conjecture (r a a))
    '''))
    sep = PartialSeparator(fol.sig, len([]), 1)
    print("SEP=", sep.separate())
    sep.add_model(fol.models[1], True)
    print("SEP=", sep.separate())
    sep.add_model(fol.models[3], False)
    print("SEP=", sep.separate())


    fol = interpret(parse('''
        (sort N)
        (relation r N N)
        (constant a N)
        (constant b N)
        (conjecture (r a a))
        (conjecture (r a b))
        (conjecture (or (r b b) (r a a)))
        (conjecture (not (r a a)))
        (conjecture (or (not (r b b)) (r a a)))
        '''))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([]), 1)
        mini_learn(sep, conjecture, fol.axioms)
    
    fol = interpret(parse('''
        (sort N)
        (relation p N)
        (constant a N)
        (constant b N)
        (conjecture (and (p a) (p b)))
        (conjecture (and (or (= a b) (p a)) (p b)))
        (conjecture (and (or (p a) (p b)) (not (= a b))))
        '''))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([]), 2)
        mini_learn(sep, conjecture, fol.axioms)

    fol = interpret(parse('''
        (sort N)
        (relation r N N)
        (conjecture (forall x N (r x x)))
        (conjecture (forall x N (not (r x x))))
        '''))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([(True, 'N')]), 1)
        mini_learn(sep, conjecture, fol.axioms)

    fol = interpret(parse('''
        (sort N)
        (relation r N N)
        (conjecture (forall x N (exists y N (or (r x y) (= x y)))))
        (conjecture (forall x N (exists y N (or (r x y) (r y x)))))
        (conjecture (forall x N (exists y N (r y x))))
        (conjecture (forall x N (exists y N (r x y))))
        '''))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([(True, 'N'), (False, 'N')]), 1)
        mini_learn(sep, conjecture, fol.axioms)

    fol = interpret(parse('''
        (sort N)
        (relation r N N)
        (conjecture (exists x N (exists y N (and (r x y) (not (= x y))))))
        '''))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([(False, 'N'), (False, 'N')]), 1)
        mini_learn(sep, conjecture, fol.axioms)

    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        sep = PartialSeparator(fol.sig, len([(False, 'N'), (False, 'N')]), 2)
        mini_learn(sep, conjecture, fol.axioms)
        

def mini_learn(sep: PartialSeparator, f: Formula, axioms: List[Formula]) -> None:
    sig = sep._sig
    env = Environment(sig)
    
    s = z3.Solver()
    for sort in sig.sorts:
        sorts_to_z3[sort] = z3.DeclareSort(sort)
    for const, sort in sig.constants.items():
        z3.Const(const, sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
    for fun, (sorts, ret) in sig.functions.items():
        z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])
    for ax in axioms:
        s.add(toZ3(ax, env))

    t = UnlimitedTimer()
    with t:
        while True:
            p = sep.separate()
            if p is None:
                print("Problem is UNSEP")
                print(f"[time] Elapsed: {t.elapsed()}")
                return
            print("Checking equivalence...")
            if m := find_model_or_equivalence_cvc4(p, f, env, s, Timer(100000)):
                if m.label == '+':
                    print("Generalizing...")
                    gm = generalize_model(m, And([f]), label='+')
                    print("Adding pos constraint:\n", gm)
                    sep.add_model(gm, True)
                else:
                    gm = generalize_model(m, And([Not(f)]), label='-')
                    print("Adding neg constraint:\n", gm)
                    sep.add_model(gm, False)
            else:
                print("Solved with separator:", p)
                print(f"[time] Elapsed: {t.elapsed()}")
                return
def mini_learn2(sig: Signature, sep: Union[DiagonalPartialSeparator, PartialSeparator], f: Formula, axioms: List[Formula]) -> None:
    env = Environment(sig)
    
    s = z3.Solver()
    for sort in sig.sorts:
        sorts_to_z3[sort] = z3.DeclareSort(sort)
    for const, sort in sig.constants.items():
        z3.Const(const, sorts_to_z3[sort])
    for rel, sorts in sig.relations.items():
        z3_rel_func[rel] = z3.Function(rel, *[sorts_to_z3[x] for x in sorts], z3.BoolSort())
    for fun, (sorts, ret) in sig.functions.items():
        z3_rel_func[fun] = z3.Function(fun, *[sorts_to_z3[x] for x in sorts], sorts_to_z3[ret])
    for ax in axioms:
        s.add(toZ3(ax, env))

    t = UnlimitedTimer()
    with t:
        while True:
            p = sep.separate()
            if p is None:
                print("Problem is UNSEP")
                print(f"[time] Elapsed: {t.elapsed()}")
                return
            print("Checking equivalence...")
            if m := find_model_or_equivalence_cvc4(p, f, env, s, Timer(100000)):
                if m.label == '+':
                    print("Generalizing...")
                    gm = generalize_model(m, And([f]), label='+')
                    print("Adding pos constraint:\n", gm)
                    sep.add_model(gm, True)
                else:
                    gm = generalize_model(m, And([Not(f)]), label='-')
                    print("Adding neg constraint:\n", gm)
                    sep.add_model(gm, False)
            else:
                print("Solved with separator:", p)
                print(f"[time] Elapsed: {t.elapsed()}")
                return


def main_test() -> None:
    print('Beginning tests...')
    test_partial()
    test_sep()
    print('Finished.')

def learn_file() -> None:
    fol = interpret(parse(open(sys.argv[1]).read()))
    for conjecture in fol.conjectures:
        print(f"\n=== Trying to learn {conjecture} ===\n")
        #sep = PartialSeparator(fol.sig, 2, 1)
        sep = DiagonalPartialSeparator(fol.sig)
        mini_learn2(fol.sig, sep, conjecture, fol.axioms)


#main_test()
learn_file()