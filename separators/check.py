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


from .logic import *

def resolve_term(term: Term, model: Model, assumptions: Dict[str, int] = {}) -> int:
    if isinstance(term, Var):
        if term.var in assumptions:
            return assumptions[term.var]
        elif term.var in model.constants:
            return model.constants[term.var]
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
    elif isinstance(formula, Equal):
        return resolve_term(formula.args[0], model, assumptions) == \
               resolve_term(formula.args[1], model, assumptions)
    elif isinstance(formula, Relation):
        elems = [resolve_term(t, model, assumptions) for t in formula.args]
        return tuple(elems) in model.relations[formula.rel]
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
