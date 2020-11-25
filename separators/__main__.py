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

import argparse, json, sys, asyncio
from .learn import learn, learn2, separate
from .interpret import interpret
from .parse import parse
from .logic import Exists, Forall, Formula

import z3


def count_quantifier_prenex(f: Formula) -> int:
    if isinstance(f, (Exists, Forall)):
        return 1 + count_quantifier_prenex(f.f)
    else: return 0

def main() -> None:
    parser = argparse.ArgumentParser(prog='separators')
    parser.add_argument("filename", metavar="FILE", help=".fol file to learn conjecture of")

    parser.add_argument("--seed", metavar='S', type=int, default = 10, help="seed used for solver")
    parser.add_argument("--log", metavar='L', type=str, default = '', help="redirect log to file")
    parser.add_argument("--max-clauses", metavar='N', type=int, default = 329342, help="maximum clauses in matrix")
    parser.add_argument("--max-depth", metavar='D', type=int, default = 10, help="maximum quantifiers")
    parser.add_argument("--timeout", metavar='T', type=float, default = 1000000, help="timeout for each of learning and separation (seconds)")
    parser.add_argument("--logic", choices=('fol', 'epr', 'universal', 'existential'), default="fol", help="restrict form of quantifier to given logic (fol is unrestricted)")
    parser.add_argument("--separator", choices=('naive', 'v1', 'v2', 'generalized', 'hybrid'), default='hybrid', help="separator algorithm to use")
    parser.add_argument("--separate", action="store_true", default=False, help="only try to separate provided models")
    parser.add_argument("--parallel", action="store_true", default=False, help="Use experimental partial separation")
    parser.add_argument("--no-cvc4", action="store_true", default=False, help="Don't use cvc4 to generate counterexamples")
    parser.add_argument("--expt-flags", dest="expt_flags", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    parser.add_argument("--blocked-symbols", dest="blocked_symbols", type=lambda x: set(x.split(',')), default=set(), help="Experimental flags")
    parser.add_argument("-q", "--quiet", action="store_true", help="disable most output")
    args = parser.parse_args()
    
    f = interpret(parse(open(args.filename).read()))
    if len(args.log) > 0:
        sys.stdout = open(args.log, "w")

    seed = args.seed

    z3.set_param("sat.random_seed", seed, "smt.random_seed", seed, "sls.random_seed", seed, "fp.spacer.random_seed", seed, "nlsat.seed", seed)    
    #success, formula, models, ctimer, stimer, mtimer, error 
    if args.separate:
        result = separate(f, timeout = args.timeout, args = args)
    elif args.parallel:
        result = asyncio.run(learn2(f.sig, f.axioms, f.conjectures[0], timeout = args.timeout, args = args))
    else:
        result = learn(f.sig, f.axioms, f.conjectures[0], timeout = args.timeout, args = args)
    j = {
        'success': result.success,
        'total_time': result.counterexample_timer.elapsed() + result.separation_timer.elapsed(),
        'separation_time': result.separation_timer.elapsed(),
        'counterexample_time': result.counterexample_timer.elapsed(),
        'model_count': len(result.models),
        'formula': str(result.current),
        'formula_quantifiers': count_quantifier_prenex(result.current),
        'error': result.reason,
        'sep_algo': args.separator,
        'action': 'separate' if args.separate else 'learn'
    }
    
    print(json.dumps(j, separators=(',',':'), indent=None))

if __name__ == "__main__":
    main()