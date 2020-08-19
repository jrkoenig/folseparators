

import sys, random, json
from separators.separate import *
from separators.learn import *
from separators.parse import parse
from separators.interpret import formula, interpret

def NotUnless(x: Formula, y: bool) -> Formula:
    if y: return x
    return Not(x)

def random_formula(sig: Signature, max_quantifiers: int = 5, max_clauses: int = 5, max_literals: int = 20, rand: random.Random = random.Random()) -> Tuple[Formula, int]:
    n_quantifiers = rand.randint(1, max_quantifiers)
    prefix = [rand.randrange(len(sig.sorts)) for _ in range(n_quantifiers)]
    atoms = list(atoms_of(sig, [(f'x{i}', sig.sort_names[s]) for i, s in enumerate(prefix)]))
    n_clauses = 1
    while n_clauses < max_clauses:
        if rand.randint(0,1) == 1:
            break
        n_clauses += 1
    clauses: List[List[Formula]] = [[] for _ in range(n_clauses)]
    
    n_literals = 0

    for cl in clauses:
        i = rand.randrange(len(atoms))
        truth = rand.randint(0, 1)
        cl.append(NotUnless(atoms[i], truth == 1))
        n_literals += 1
    
    for _ in range(rand.randint(0, max_literals-n_clauses)):
        cl = clauses[rand.randrange(n_clauses)]
        i = rand.randrange(len(atoms))
        truth = rand.randint(0, 1)
        if atoms[i] not in cl and Not(atoms[i]) not in cl:
            cl.append(NotUnless(atoms[i], truth == 1))
            n_literals += 1
    

    matrix = And([Or(cl) for cl in clauses])
    f: Formula = matrix
    for i, sort in reversed(list(enumerate(prefix))):
        is_forall = True
        f = (Forall if is_forall else Exists)(f'x{i}', sig.sort_names[sort], f)
    return (f, n_literals + n_clauses + n_quantifiers)

def main() -> None:
    sigfile = open(sys.argv[1]).read()
    fol = interpret(parse(sigfile))
    rand = random.Random(3429045093458)
    
    formulas: DefaultDict[int, List[Formula]] = defaultdict(list)
    for i in range(101):
        f, complexity = random_formula(fol.sig, max_quantifiers=3, max_clauses=3, max_literals=6, rand=rand)
        formulas[complexity].append(f)
    
    index = 0
    descs: List[Any] = []
    for complexity in sorted(formulas.keys()):
        print(complexity)
        fs = list(sorted(formulas[complexity]))
        f_old: Optional[Formula] = None
        for f in fs:
            if f != f_old:
                with open(f"conjectures/random/r-{index}.fol", "w") as output:
                    output.write(f"; Random formula: {f}\n")
                    output.write(f"; Complexity: {complexity}\n")
                    output.write(sigfile)
                    output.write(f"\n; Conjecture:\n")
                    output.write(f"(conjecture {repr(f)})\n")
                descs.append({'base': 'random',
                              'conjecture': f'r{index}',
                              'file': f"conjectures/random/r-{index}.fol",
                              'quantifiers': 1,
                              'max_quantifier_depth': 1,
                              'existentials': 0,
                              'max_term_depth': 1,
                              'golden_formula': str(f),
                              })
                index += 1
            f_old = f
    json.dump(descs, open('conjectures/random.json', 'w'), indent=1)
main()