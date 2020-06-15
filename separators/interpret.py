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

from typing import Optional, List, Tuple, NoReturn

from .parse import parse, Atom, Parens, AstNode, SrcLoc
from .logic import Signature, Environment, Model, And, Or, Not, Iff, Exists, Forall, Equal, Relation, Formula, Term, Var, Func, model_is_partial_wrt_sig

class SemanticError(Exception):
    def __init__(self, desc:str = "?"):
        self.desc = desc
    def __str__(self) -> str:
        return "Semantic Error: " + self.desc

def error_at(desc: str, node: AstNode) -> NoReturn:
    raise SemanticError(desc + " at " + str(node.loc[0]) + ":" + str(node.loc[1]))

def term(env: Environment, token: AstNode) -> Tuple[Term, str]:
    if isinstance(token, Atom):
        sort = env.lookup_var(token.name())
        if sort is None:
            error_at("Symbol not bound", token)
        return (Var(token.name()), sort)
    elif isinstance(token, Parens):
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
    else: assert False

def formula(env: Environment, token: AstNode) -> Formula:
    if isinstance(token, Atom) or len(token) == 0 or not isinstance(token[0], Atom):
        error_at("Invalid formula", token)
    head = token[0]
    if head.name() == "and":
        return And([formula(env, t) for t in token[1:]])
    if head.name() == "or":
        return Or([formula(env, t) for t in token[1:]])
    if head.name() == "not":
        if len(token) != 2:
            error_at("Not takes exactly one argument", token)
        return Not(formula(env, token[1]))
    if head.name() == "iff":
        if len(token) != 3:
            error_at("Iff is binary", token)
        return Iff(*[formula(env, t) for t in token[1:]])
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
    error_at("Invalid formula", token)

class FOLFile(object):
    def __init__(self, sig: Signature):
        self.sig = sig
        self.axioms: List[Formula] = []
        self.conjectures: List[Formula] = []
        self.models: List[Model] = []
        self.constraint_pos: List[str] = []
        self.constraint_neg: List[str] = []
        self.constraint_imp: List[Tuple[str,str]] = []

# From the List of commands, intepret the definitions to construct a representation
# of the signature, axioms and models
def interpret(commands: List[AstNode]) -> FOLFile:
    result = FOLFile(Signature())
    sig = result.sig
    axioms = result.axioms
    conjectures = result.conjectures
    models = result.models

    # Helper to turn a list of Atoms into a list of sort names, checking that each is defined
    def sort_list(l: List[AstNode]) -> List[str]:
        resolved_sorts = []
        for s in l:
            if isinstance(s, Atom) and s.name() in sig.sorts:
                resolved_sorts.append(s.name())
            else:
                error_at("Must be sort", s)
        return resolved_sorts
    def free_name(t: AstNode) -> Optional[str]:
        return t.name() if isinstance(t, Atom) and sig.is_free_name(t.name()) else None
    
    saw_any_constraint = False
    in_sig = True
    for c in commands:
        if isinstance(c, Parens) and isinstance(c[0], Atom):
            command = c[0].name()

            if command == "sort":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) != 2: error_at("Sort must define one non-reserved name", c)
                n = free_name(c[1])
                if n is None: error_at("Sort must define one non-reserved name", c)
                sig.sorts.add(n)

            elif command == "relation":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) < 2: error_at("Invalid relation definition", c)
                n = free_name(c[1])
                if n is None: error_at("Invalid relation definition", c)
                sig.relations[n] = sort_list(c[2:])                

            elif command == "constant":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) != 3: error_at("Invalid constant definition", c)
                n = free_name(c[1])
                if n is None: error_at("Invalid constant definition", c)
                sig.constants[n] = sort_list(c[2:])[0]

            elif command == "function":
                if not in_sig: error_at("Signature must come before axioms and models", c)
                if len(c) < 4: error_at("Invalid function definition", c)
                n = free_name(c[1])
                if n is None: error_at("Invalid function definition", c)
                function_sort = sort_list(c[2:])
                sig.functions[n] = (function_sort[:-1], function_sort[-1])
                
            elif command == "axiom":
                in_sig = False
                if len(c) != 2:
                    error_at("Invalid axiom definition", c)
                env = Environment(sig)
                axioms.append(formula(env, c[1]))
            elif command == "conjecture":
                in_sig = False
                if len(c) != 2:
                    error_at("Invalid conjecture definition", c)
                env = Environment(sig)
                conjectures.append(formula(env, c[1]))
            elif command == "constraint":
                saw_any_constraint = True
                for constraint in c[1:]:
                    if isinstance(constraint, Atom):
                        result.constraint_pos.append(constraint.name())
                    else:
                        head = constraint[0]
                        if isinstance(head, Atom) and head.name() == "not" and len(constraint) == 2 and isinstance(constraint[1], Atom):
                            result.constraint_neg.append(constraint[1].name())
                        elif isinstance(head, Atom) and head.name() == "implies" and len(constraint) == 3 and isinstance(constraint[1], Atom) and isinstance(constraint[2], Atom):
                            result.constraint_imp.append((constraint[1].name(), constraint[2].name()))
                        else:
                            error_at("constraint must be M, (not M), or (implies M1 M2)", constraint)
            elif command == "model":
                if in_sig:
                    sig.finalize_sorts()
                in_sig = False
                m = Model(sig)
                if len(c) < 2 or not isinstance(c[1], Atom):
                    error_at("Model must have label", c[1])
                m.label = c[1].name()
                if len(c) < 3:
                    error_at("Model must have list of elements/sorts",c)
                elements = c[2]
                if not isinstance(elements, Parens):
                    error_at("Model must have list of elements/sorts",c)
                for pair in elements[:]:
                    if not isinstance(pair, Parens) or len(pair) != 2:
                        error_at("Elements must be (name SORT)", pair)
                    (elem,sort) = pair[0], pair[1]
                    n = free_name(elem)
                    if n is None: error_at("Elements must be (name SORT)", pair)
                    s = sort_list([sort])[0]
                    if not m.add_elem(n, s):
                        error_at("Element names must be unique", pair[0])
                for fact in c[3:]:
                    if not isinstance(fact, Parens):
                        error_at("Invalid model fact", fact)
                    if len(fact) == 0 or not isinstance(fact[0], Atom):
                        error_at("Invalid model fact", fact)
                    fact_root = fact[0].name()
                    if fact_root in sig.relations:
                        expected_sorts = sig.relations[fact_root]
                        if len(fact) != len(expected_sorts) + 1:
                            error_at("Wrong relation arity", fact)
                        args = []
                        for arg, e_s in zip(fact[1:], expected_sorts):
                            if not isinstance(arg, Atom) or m.sort_of(arg.name()) != e_s:
                                error_at("Incorrect sort", arg)
                            args.append(arg.name())
                        m.add_relation(fact_root, args, True)
                    elif fact_root == "not":
                        if len(fact) != 2:
                            error_at("Negation is unary", fact)
                        fact = fact[1]
                        if not isinstance(fact, Parens):
                            error_at("Invalid model fact", fact)
                        if len(fact) == 0 or not isinstance(fact[0], Atom):
                            error_at("Invalid model fact", fact)
                        fact_root = fact[0].name()
                        if fact_root not in sig.relations:
                            error_at("Model fact must be relation", fact)
                        expected_sorts = sig.relations[fact_root]
                        if len(fact) != len(expected_sorts) + 1:
                            error_at("Wrong relation arity", fact)
                        args = []
                        for arg, e_s in zip(fact[1:], expected_sorts):
                            if not isinstance(arg, Atom) or m.sort_of(arg.name()) != e_s:
                                error_at("Incorrect sort", arg)
                            args.append(arg.name())
                        m.add_relation(fact_root, args, False)
                    elif fact_root == "=":
                        if len(fact) != 3:
                            error_at("Equality is binary", fact)
                        if isinstance(fact[1], Atom) and fact[1].name() in sig.constants:
                            if not isinstance(fact[2], Atom) or m.sort_of(fact[2].name()) != sig.constants[fact[1].name()]:
                                error_at("Constant must be assigned a model element with the right sort", fact[1])
                            m.add_constant(fact[1].name(), fact[2].name())
                        elif isinstance(fact[1], Parens) and len(fact[1]) > 0 and isinstance(fact[1][0], Atom) and fact[1][0].name() in sig.functions:
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
                if not model_is_partial_wrt_sig(m, sig):
                    error_at("Model is not partial with respect to signature (missing constant/function definitions?)", c)
                models.append(m)
            else:
                error_at("Unexpected Command", c)
        else:
            error_at("Unexpected Command", c)
    # if no constraints are given, assume models labeled + are positive and those labeled - are negative
    # there is no implicit way to specify implication constraints
    if not saw_any_constraint:
        result.constraint_pos.append("+")
        result.constraint_neg.append("-")
        
    if in_sig:
        sig.finalize_sorts()
    return result
