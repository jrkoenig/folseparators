
import z3

from logic import Forall, Exists, Equal, Relation, And, Or, Not
from check import check, resolve_term
from matrix import infer_matrix, K_function_unrolling
import itertools, copy
import sys

def collapse(model, sig, assignment):
    mapping = {}
    consts = []
    funcs = []
    rels = []

    for const in sorted(model.constants.keys()):
        e = model.constants[const]
        if e not in mapping:
            mapping[e] = len(mapping)
        consts.append(mapping[e])

    for e in assignment:
        if e not in mapping:
            mapping[e] = len(mapping)
        consts.append(mapping[e])

    for _ in range(K_function_unrolling):
        # we need to iterate over elements of the collapsed model in a way
        # consistent with their collapsed identity, hence iterating over them
        # in the mapping value order
        reachable = list(sorted(mapping.keys(), key = lambda x: mapping[x]))
        for f in sorted(model.functions.keys()):
            (arg_sorts, _) = sig.functions[f]
            arg_tuples = itertools.product(*[[r for r in reachable if model.sorts[r] == sort] for sort in arg_sorts])
            f_repr = model.functions[f]
            for t in arg_tuples:
                e = f_repr[t]
                if e not in mapping:
                    mapping[e] = len(mapping)
                funcs.append(mapping[e])


    for rel in sorted(model.relations.keys()):
        tuples = model.relations[rel]
        collapsed_tuples = []
        for t in tuples:
            if all([x in mapping for x in t]):
                collapsed_tuples.append(tuple([mapping[x] for x in t]))
        collapsed_tuples.sort()
        rels.append(collapsed_tuples)
    return repr((consts, funcs, rels))

class CollapseCache(object):
    def __init__(self, sig, models = []):
        self.models = models
        self.sig = sig
        self.cache = {}
        self.collapsed = {}
        self.assignments = []
    def add_model(self, model):
        self.models.append(model)
    def get(self, index, assignment):
        N = len(self.models[index].sorts)
        assignment = tuple(assignment)
        # ensure elems are integers referring to elements of model index
        assert all(e < N for e in assignment)
        # fast path if assignment has been seen before
        if (index, assignment) in self.cache:
            return self.cache[(index, assignment)]
        # collapse model
        key = collapse(self.models[index], self.sig, assignment)
        if key not in self.collapsed:
            r = len(self.collapsed)
            self.collapsed[key] = r
            self.assignments.append((index, assignment))
        else:
            r = self.collapsed[key]
        self.cache[(index, assignment)] = r
        return r
    def get_concrete(self, i):
        (index, assignment) = self.assignments[i]
        M = copy.deepcopy(self.models[index])
        for var_i, element in enumerate(assignment):
            M.add_constant("x_"+str(var_i), M.names[element])
        return M
    def __len__(self):
        return len(self.assignments)

def prefix_is_redundant(prefix):
    if len(prefix) == 0: return False
    for i in range(len(prefix) - 1):
        a,b = prefix[i], prefix[i+1]
        if a[0] == b[0] and a[1] > b[1]:
            return True
    return False

def build_prefix_formula(prefix, f, n = 0):
    if len(prefix) == 0:
        return f
    (is_forall, sort) = prefix[0]
    if is_forall:
        return Forall("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))
    else:
        return Exists("x_"+str(n), sort, build_prefix_formula(prefix[1:], f, n+1))

class VarSet(object):
    def __init__(self):
        self.vars = set()
        self.pos = set()
        self.neg = set()
    def add(self, v, polarity):
        self.vars.add(v)
        if polarity:
            self.pos.add(v)
        else:
            self.neg.add(v)
    def __iter__(self): return iter(self.vars)

def formula_for_model(model_index, assignment, prefix, collapsed, vars):
    m = collapsed.models[model_index]
    if len(prefix) == 0:
        x = collapsed.get(model_index, assignment)
        v = z3.Bool("M"+str(x))
        polarity = m.label.startswith("+")
        vars.add(x, polarity)
        return v if polarity else z3.Not(v)
    else:
        (is_forall, sort) = prefix[0]
        rest = prefix[1:]
        formulas = []
        for elem in m.elems_of_sort[sort]:
            f = formula_for_model(model_index, assignment + [elem], rest, collapsed, vars)
            formulas.append(f)
        if is_forall == m.label.startswith("+"):
            return z3.And(formulas)
        else:
            return z3.Or(formulas)

def check_prefix(models, prefix, sig, collapsed, solver):
    solver.push()
    vars = VarSet()
    sat_formula = z3.And([formula_for_model(m_index, [], prefix, collapsed, vars) for m_index in range(len(models))])
    # print("There are ", len(vars.pos.symmetric_difference(vars.neg)), "pure variables of", len(vars.vars))
    solver.add(sat_formula)
    result = solver.check()
    solver.pop()
    if result == z3.unsat:
        return None
    elif result == z3.sat:
        models = {}
        for x in vars:
            models[x] = collapsed.get_concrete(x)
        sig_with_bv = copy.deepcopy(sig)
        for i,(_, sort) in enumerate(prefix):
            assert "x_"+str(i) not in sig_with_bv.constants
            sig_with_bv.constants["x_"+str(i)] = sort
        matrix = infer_matrix(models, sig_with_bv, sat_formula)
        checker = z3.Solver()
        checker.add(sat_formula)
        for x, m in models.items():
            checker.add(z3.Bool('M'+str(x)) if check(matrix, m) else z3.Not(z3.Bool('M'+str(x))))
        if checker.check() != z3.sat:
            raise RuntimeError("Incorrect matrix!")
        return build_prefix_formula(prefix, matrix)
    else:
        assert False and "Error, z3 returned unknown"

def ae_edges_of(sig):
    ae = {sort: set() for sort in sig.sorts}
    for f, (arg_sorts, ret_sort) in sig.functions.items():
        for a in arg_sorts:
            ae[a].add(ret_sort)
    return ae

def update_ae_edges(ae, f, negate=False, outer_universal_sorts=set()):
    if isinstance(f, (Equal, Relation)):
        return
    elif isinstance(f, (Or, And)):
        for subf in f.c:
            update_ae_edges(ae, subf, negate, outer_universal_sorts)
    elif isinstance(f, Not):
        update_ae_edges(ae, f.f, not negate, outer_universal_sorts)
    else:
        assert isinstance(f, (Exists, Forall))
        if isinstance(f, Forall) != negate:
            # A, or ~E
            update_ae_edges(ae, f.f, negate, outer_universal_sorts.union(set([f.sort])))
        else:
            # E, or ~A
            for s in outer_universal_sorts:
                ae[s].add(f.sort)
            update_ae_edges(ae, f.f, negate, outer_universal_sorts)

def digraph_is_acyclic(edges):
    visited = set()
    time = {}
    def visit(n):
        if n in visited: return
        visited.add(n)
        for m in edges[n]:
            visit(m)
        time[n] = len(time)
    for root in edges.keys():
        visit(root)
    for n, neighbors in edges.items():
        for m in neighbors:
            if time[n] <= time[m]:
                return False
    return True


class Separator(object):
    def __init__(self, sig, quiet=False, logic="fol", max_depth = 100000, epr_wrt_formulas = []):
        self.sig = sig
        self.collapsed = CollapseCache(sig)
        self.models = []
        self.quiet = quiet
        self.logic = logic
        self.max_depth = max_depth
        self.ae_edges = None
        if logic == "epr":
            self.ae_edges = ae_edges_of(sig)
            for f in epr_wrt_formulas:
                update_ae_edges(self.ae_edges, f)
            if not digraph_is_acyclic(self.ae_edges):
                raise RuntimeError("EPR logic requires background formulas to be already in EPR")
        self.forget_learned_facts()

    def add_model(self, model):
        self.models.append(model)
        self.collapsed.add_model(model)
    def forget_learned_facts(self):
        """Forgets all inferred facts (about prenex, etc) but keeps models"""
        self.prefixes = [[]]
        self.prefix_index = 0
    def separate(self):
        solver = z3.Solver()
        while True:
            if self.prefix_index == len(self.prefixes):
                # We have reached our maximum depth
                if len(self.prefixes[0]) == self.max_depth:
                    return None
                self.prefixes = [[(is_forall, s)]+p for is_forall in [True, False] for p in self.prefixes for s in sorted(self.sig.sorts)]
                self.prefixes = [p for p in self.prefixes if self._filter_prefix(p)]
                self.prefix_index = 0
            p = self.prefixes[self.prefix_index]
            if not prefix_is_redundant(p):
                if not self.quiet: print ("Prefix:", " ".join([("∀" if is_forall else "∃") + sort + "." for (is_forall, sort) in p]))
                c = check_prefix(self.models, p, self.sig, self.collapsed, solver)
                if c is not None:
                    return c
            self.prefix_index += 1
    def _filter_prefix(self, p):
        if prefix_is_redundant(p):
            return False
        if self.logic == "epr":
            ae_edges = copy.deepcopy(self.ae_edges)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), False)
            update_ae_edges(ae_edges, build_prefix_formula(p, And([])), True)
            return digraph_is_acyclic(ae_edges)
        if self.logic == "universal":
            return all(is_forall for (is_forall, _) in p)
        if self.logic == "existential":
            return all(not is_forall for (is_forall, _) in p)
        return True

if __name__ == "__main__":
    from interpret import interpret
    from parse import parse
    import sys

    if len(sys.argv) not in [1,2]:
        print("Usage: python3 separate.py [file.fol]")
        exit(1)

    file = "problems/node_has_edge.fol" if len(sys.argv) == 1 else sys.argv[1]
    (sig, axioms, conjectures, models) = interpret(parse(open(file).read()))

    f = separate(models, sig, 6)
    if f is not None:
        print("Formula is:", f)
    else:
        print("No formula found.")
