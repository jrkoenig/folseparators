
import separate, logic, itertools, z3

K = 4
L = 3
assert 1 <= L and L < K


sig = logic.Signature()
sig.sorts.add("S")
for name in 'ABCDEGHIJKFT':
    sig.relations[name] = tuple(["S"] * K)

def separable(models):
    solver = z3.Solver()
    collapsed = separate.CollapseCache(sig)
    for m in models:
        collapsed.add_model(m)
    for prefix in itertools.product(*([[(True, "S"), (False, "S")]] * K)):
        prefix_str = "".join([("∀" if is_forall else "∃") for (is_forall, sort) in prefix])
        x = separate.check_prefix(models, prefix, sig, collapsed, solver)
        if x:
            print("<S>", prefix_str)
        else:
            print("< >", prefix_str)

def make_model(label, N, specs):
    m = logic.Model(sig)
    m.label = label
    for i in range(N):
        m.add_elem(f"e{i}", "S")
    for t in itertools.product(*([range(N)] * K)):
        e = tuple(sorted(set(t)))
        if len(e) == len(t):
            m.add_relation(specs(e), tuple(f"e{ei}" for ei in t))
    return m

def subsetof(x,s):
    return all(e in s for e in x)

def clause(positive, c):
    def f(e):
        if e[K - 2] == K - 2:
            return c[e[K - 1] - (K - 1)]
        
        if positive:
            # F if e is in the first row, T otherwise
            if all([m in e for m in range(L)]):
                return 'F'
            return 'T'
        else:
            # F for the elements in the first rows ending with the variable elements (last len(c) elements)
            # T otherwise
            for elem in range(len(c)):
                if subsetof(list(range(L-1)) + [elem + K - 1], e):
                    return 'F'
            return 'T'
    return make_model("+" if positive else "-", K + len(c) - 1, f)

def uniformize(cnf):
    x = 0
    r = []
    for cl in cnf:
        if all(x.startswith("~") for x in cl) or all(not x.startswith("~") for x in cl):
            r.append(cl)
        else:
            v = f"x{x}"
            x+=1
            r.append([v] + [x for x in cl if not x.startswith("~")])
            r.append([v] + [x for x in cl if x.startswith("~")])
    return r
def pp(cnf):
    return " & ".join(("(" + " | ".join(l for l in c) + ")") for c in cnf)

def main():
    # UNSAT
    m = [clause(True, ["T"]), clause(True, ["T", "F"]), clause(False, ["F"]), clause(False, ["T", "F"]),
         clause(True, ["A"]), clause(True, ["B"]), clause(True, ["C"]), clause(False, ["A", "B", "C"])]
    # print("\n".join([str(mi) for mi in m]))
    print(pp(uniformize([['A'],['B'],['C'], ['~A','~B','~C']])))
    separable(m)

    # SAT
    m = [clause(True, ["T"]), clause(True, ["T", "F"]), clause(False, ["F"]), clause(False, ["T", "F"]),
         clause(True, ["A"]), clause(True, ["C"]), clause(False, ["A", "B", "C"])]
    print(pp(uniformize([['A'],['C'], ['~A','~B','~C']])))
    separable(m)

main()