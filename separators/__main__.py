
import argparse, random, json
from .learn import learn
from .interpret import interpret
from .parse import parse
from .logic import print_model, Exists, Forall, Formula

import z3


def count_quantifier_prenex(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifier_prenex(f.f)
    else: return 0

def main() -> None:
    parser = argparse.ArgumentParser(prog='separators')
    parser.add_argument("filename", metavar="FILE", help=".fol file to learn conjecture of")

    parser.add_argument("--max-clauses", metavar='N', type=int, default = 10, help="maximum clauses in matrix")
    parser.add_argument("--max-depth", metavar='N', type=int, default = 10, help="maximum quantifiers")
    parser.add_argument("--timeout", metavar='T', type=float, default = 1000000, help="timeout for each of learning and separation (seconds)")
    parser.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="restrict form of quantifier to given logic (fol is unrestricted)")
    parser.add_argument("--separator", choices=('naive', 'v1', 'v2', 'hybrid'), default='naive', help="separator algorithm to use")
    parser.add_argument("-q", "--quiet", action="store_true", help="disable most output")
    args = parser.parse_args()
    
    (sig, axioms, conjectures, models) = interpret(parse(open(args.filename).read()))

    #seed = random.randrange(0, 2**31)
    seed = 329342
    z3.set_param("sat.random_seed", seed, "smt.random_seed", seed, "sls.random_seed", seed, "fp.spacer.random_seed", seed, "nlsat.seed", seed)    
    #success, formula, models, ctimer, stimer, mtimer, error 
    result = learn(sig, axioms, conjectures[0], timeout = args.timeout, args = args)
    if not args.quiet:
        for m in models:
            print(print_model(m))
    j = {
        'success': result.success,
        'total_time': result.counterexample_timer.elapsed() + result.separation_timer.elapsed(),
        'separation_time': result.separation_timer.elapsed(),
        'counterexample_time': result.counterexample_timer.elapsed(),
        'matrix_time': result.matrix_timer.elapsed(),
        'model_count': len(result.models),
        'formula': str(result.current),
        'formula_quantifiers': count_quantifier_prenex(result.current),
        'error': result.reason
    }
    
    print(json.dumps(j, separators=(',',':'), indent=None))

if __name__ == "__main__":
    main()