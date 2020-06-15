
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
    '''))
    print(fol.models[0])
    for conj,expected in zip(fol.conjectures, [False, False, False, True]):
        value = check_partial(Completion(PartialModel(fol.models[0])), conj)
        print("Conjecture", conj, " = ", value)
        assert value == expected
    pass

def main_test() -> None:
    print('Beginning tests...')
    test_partial()
    print('Finished.')

main_test()