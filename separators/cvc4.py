
import subprocess, z3, re, itertools
from .logic import Model, Signature, model_is_complete_wrt_sig
from .parse import Atom, Parens, AstNode, Input, parse
from typing import Tuple, Optional, List, Dict

# copied from mypyvy project
def cvc4_preprocess(z3str: str) -> str:
    lines = ['(set-logic UF)']
    for st in z3str.splitlines():
        st = st.strip()
        if st == '' or st.startswith(';') or st.startswith('(set-info '):
            continue
        # st = st.replace('member', 'member2') # Unecessary with (set-logic UF)
        assert '@' not in st, st
        if st.startswith('(declare-sort ') and not st.endswith(' 0)'):
            assert st.endswith(')'), st
            st = st[:-1] + ' 0)'
        lines.append(st)
    return '\n'.join(lines)

def _eval(env: Dict[str, str], value: AstNode) -> str:
    if isinstance(value, Atom):
        v = value.name()
        if v in env:
            return env[v]
        else:
            return v
    assert isinstance(value, Parens)
    head = value[0]
    assert isinstance(head, Atom)
    if head.name() == 'ite':
        assert len(value) == 4
        if _eval(env, value[1]) == 'true':
            return _eval(env, value[2])
        else:
            return _eval(env, value[3])
    elif head.name() == '=':
        assert len(value) == 3
        return 'true' if _eval(env, value[1]) == _eval(env, value[2]) else 'false'
    elif head.name() == 'and':
        assert len(value) > 1
        for i in value[1:]:
            if _eval(env, i) != 'true':
                return 'false'
        return 'true'
    elif head.name() == 'not':
        assert len(value) == 2
        return 'false' if _eval(env, value[1]) == 'true' else 'true'
    else:
        assert False, value

def _parse_model(sig: Signature, lines: List[str]) -> Model:
    print("\n".join(lines))
    m = Model(sig)

    # First, parse the elements from the constants
    last_sort = ''
    for l in lines:
        r = re.match(r"\(declare-sort ([^\s]+) 0\)", l)
        if r:
            last_sort = r.group(1)
            continue
        r = re.match(r"; rep: ([^\s]+)", l)
        if r:
            m.add_elem(r.group(1), last_sort)
    for sort in sig.sorts:
        if sort not in m.elems_of_sort:
            m.add_elem(f"@uc_{sort}_0", sort)
    modeln = parse("\n".join(lines))[0]
    assert isinstance(modeln, Parens)
    for item in modeln.children:
        if isinstance(item, Atom) and item.name() == 'model':
            pass
        elif isinstance(item, Parens) and isinstance(item[0], Atom) and item[0].name() == 'declare-sort':
            pass
        elif isinstance(item, Parens) and isinstance(item[0], Atom) and item[0].name() == 'define-fun':
            assert len(item) == 5
            print(item)
            [_, name, types, result, value] = item.children
            assert isinstance(name, Atom)
            assert isinstance(result, Atom)
            identifier = name.name()
            if identifier in sig.constants:
                assert isinstance(value, Atom)
                m.add_constant(identifier, value.name())
            if identifier in sig.relations:
                assert isinstance(result, Atom) and result.name() == "Bool"
                assert isinstance(types, Parens)
                bvs = [t[0].name() for t in types[:]] # type: ignore
                sorts = sig.relations[identifier]
                for t in itertools.product(*[m.elems_of_sort[sort] for sort in sorts]):
                    args = [m.names[x] for x in t]
                    e = _eval(dict(zip(bvs, args)), value)
                    #print(bvs, args, e)
                    if e == 'true':
                        m.add_relation(identifier, args)
            if identifier in sig.functions:
                sorts, ret_sort = sig.functions[identifier]
                assert isinstance(result, Atom) and result.name() == ret_sort
                assert isinstance(types, Parens)
                bvs = [t[0].name() for t in types[:]] # type: ignore
                for t in itertools.product(*[m.elems_of_sort[sort] for sort in sorts]):
                    args = [m.names[x] for x in t]
                    e = _eval(dict(zip(bvs, args)), value)
                    #print(bvs, args, e)
                    m.add_function(identifier, args, e)
        else:
            print(item)
            assert False

    # Perform model completion:
    for c in sig.constants.keys():
        if c not in m.constants:
            sort = sig.constants[c]
            v = m.names[m.elems_of_sort[sort][0]]
            m.add_constant(c, v)
    for rel, sorts in sig.relations.items():
        if rel not in m.relations:
            m.relations[rel] = dict()
        rep = m.relations[rel]
        for t in itertools.product(*[m.elems_of_sort[sort] for sort in sorts]):
            if t not in rep:
                rep[t] = False
    for f in sig.functions.keys():
        sorts, ret_sort = sig.functions[f]
        v = m.names[m.elems_of_sort[ret_sort][0]]
        if f not in m.functions:
            m.functions[f] = dict()
        for t in itertools.product(*[m.elems_of_sort[sort] for sort in sorts]):
            args = [m.names[x] for x in t]
            if t not in m.functions[f]:
                m.add_function(f, args, v)
    assert model_is_complete_wrt_sig(m, sig)
    return m

_cvc4_args= ['--lang=smtlib2.6', '--finite-model-find', '--full-saturate-quant', '--produce-models','--dump-models']

def solve_with_cvc4(s: z3.Solver, sig: Signature, timeout: float = 0.0) -> Tuple[z3.CheckSatResult, Optional[Model]]:
    smtlib = cvc4_preprocess(s.to_smt2())
    if timeout == 0.0 or timeout == float("+inf"):
        to = None
    else:
        to = timeout
    try:
        res = subprocess.run(['cvc4', *_cvc4_args], input=smtlib, encoding='utf8', stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=to)
        if res.returncode == 0:
            output = res.stdout
            lines = output.splitlines()
            if lines[0] == 'unsat':
                return (z3.unsat, None)
            elif lines[0] == 'unknown':
                return (z3.unknown, None)
            elif lines[0] == 'sat':
                return (z3.sat, _parse_model(sig, lines[1:]))
            else:
                assert False, "got weird: " + lines[0]
        else:
            print("Recieved non-zero return code from cvc4", res.returncode)
            print(res.stdout)
            print(res.stderr)
            return (z3.unknown, None)
    except subprocess.TimeoutExpired:
        return (z3.unknown, None)