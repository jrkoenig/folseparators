
from dataclasses import dataclass
from typing import Dict, Iterable, Sequence, Tuple, List, Union, Optional, Callable
from array import array

@dataclass
class Expr:
    def __rshift__(a, b: 'Expr') -> 'Expr':
        return Or(Not(a), b)
    def __lshift__(a, b: 'Expr') -> 'Expr':
        return Or(Not(b), a)
    def __invert__(a) -> 'Expr':
        return Not(a)
    def __or__(a, b: 'Expr') -> 'Expr':
        return Or(a, b)
    def __and__(a, b: 'Expr') -> 'Expr':
        return And(a, b)
    def __xor__(a, b: 'Expr') -> 'Expr':
        return Not(Iff(a, b))
    def __ne__(a, b: 'Expr') -> 'Expr': # type: ignore[override]
        return Not(Iff(a, b))
    def __eq__(a, b: 'Expr') -> 'Expr': # type: ignore[override]
        return Iff(a, b)


@dataclass(eq=False)
class Var(Expr):
    i: int
    def __str__(self) -> str: return f'v{self.i}'

@dataclass(eq=False)
class Val(Expr):
    b: bool
    def __str__(self) -> str: return 'true' if self.b else 'false'

@dataclass(eq=False)
class And(Expr):
    c: Tuple[Expr, ...]
    def __init__(self, *c: Expr):
        self.c = c
    def __str__(self) -> str: return f'And({", ".join(str(i) for i in self.c)})'

@dataclass(eq=False)
class Or(Expr):
    c: Tuple[Expr, ...]
    def __init__(self, *c: Expr):
        self.c = c
    def __str__(self) -> str: return f'Or({", ".join(str(i) for i in self.c)})'

@dataclass(eq=False)
class Not(Expr):
    a: Expr
    def __str__(self) -> str: return f'Not({str(self.a)})'

@dataclass(eq=False)
class Iff(Expr):
    a: Expr
    b: Expr
    def __str__(self) -> str: return f'Iff({str(self.a)}, {str(self.b)})'

_LitConst = Union[int, bool]

def _neg_of_litconst(x: _LitConst) -> _LitConst:
    if isinstance(x, bool): return not x
    return -x
        
class Reduction:
    def __init__(self, next_func: Callable[[], int]):
        self.clauses = array('i')
        self._fresh = next_func
    def reset(self) -> None:
        del self.clauses[:]

    def _add_clause(self, xs: Sequence[_LitConst]) -> None:
        cl = []
        for x in xs:
            if x is True:
                return
            if x is False:
                continue
            assert x != 0
            cl.append(x)
        self.clauses.extend(cl)
        self.clauses.append(0)
    def reduce(self, e: Expr) -> None:
        self._reduce(e, True)
    
    def _reduce_none(self, e: Expr) -> _LitConst:
        if isinstance(e, Val):
            return e.b
        elif isinstance(e, Var):
            return e.i
        if isinstance(e, (And, Or)) and len(e.c) == 0:
            return isinstance(e, And)
        if isinstance(e, (And, Or)) and len(e.c) == 1:
            return self._reduce_none(e.c[0])
        elif isinstance(e, Not):
            return _neg_of_litconst(self._reduce_none(e.a))
        elif isinstance(e, (And, Or, Iff)):
            x = self._fresh()
            self._reduce(e, x)
            return x
        assert False, e

    def _reduce(self, e: Expr, v: _LitConst) -> None:
        if isinstance(e, Val):
            value = e.b
            if isinstance(v, bool):
                self.clauses.extend([0] if value != v else [])
            else:
                self.clauses.extend([v if value else -v, 0])
        elif isinstance(e, Var):
            x = e.i
            if isinstance(v, bool):
                self.clauses.extend([x if v else -x, 0])
            else:
                self.clauses.extend([x, -v, 0, -x, v, 0])
        elif isinstance(e, And):
            if isinstance(v, bool):
                if v:
                    for c in e.c:
                        self._reduce(c, True)
                else:
                    self._reduce(Or(*(Not(c) for c in e.c)), True)
            else:
                xs = [self._reduce_none(c) for c in e.c]
                for x in xs:
                    self._add_clause([-v, x])
                self._add_clause([v, *(_neg_of_litconst(x) for x in xs)])
        elif isinstance(e, Or):
            # print(f"Reducing Or ({e}) against {v}")
            if isinstance(v, bool):
                if v:
                    self._add_clause([self._reduce_none(c) for c in e.c])
                else:
                    self._reduce(And(*(Not(c) for c in e.c)), True)
            else:
                xs = [self._reduce_none(c) for c in e.c]
                for x in xs:
                    self._add_clause([_neg_of_litconst(x), v])
                self._add_clause([-v, *xs])
        elif isinstance(e, Not):
            self._reduce(e.a, _neg_of_litconst(v))
        elif isinstance(e, Iff):
            if isinstance(v, bool):
                x = self._reduce_none(e.a)
                # print("Iff x is", x, 'b is', e.b)
                self._reduce(e.b, x if v else _neg_of_litconst(x))
            else:
                assert False
