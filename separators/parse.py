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

import re
import sys
from typing import List, Union, Tuple, Pattern, NoReturn, overload

class SyntaxError(Exception):
    def __init__(self, desc: str = "?"):
        self.desc = desc
    def __str__(self) -> str:
        return "Syntax Error: " + self.desc

SrcLoc = Tuple[int,int]
AstNode = Union['Atom', 'Parens']

class Atom(object):
    def __init__(self, name: str, src_loc: SrcLoc = (0,0)):
        self.n = name
        self.loc = src_loc
    def __repr__(self) -> str:
        return self.n
    def name(self) -> str:
        return self.n

class Parens(object):
    def __init__(self, children: List[AstNode], src_loc: SrcLoc = (0,0)):
        self.children = children
        self.loc = src_loc
    def __repr__(self) -> str:
        return "({})".format(" ".join(map(repr, self.children)))
    def __len__(self) -> int:
        return len(self.children)
    @overload
    def __getitem__(self, i: int) -> AstNode: ...
    @overload
    def __getitem__(self, i: slice) -> List[AstNode]: ...
    def __getitem__(self, i: Union[int, slice]) -> Union[AstNode, List[AstNode]]:
        return self.children[i]


class Input(object):
    def __init__(self, s: str):
        self.string = s
        self.index = 0
        self.line = 1
        self.column = 1
    def matches(self, r: Pattern) -> bool:
        return r.match(self.string[self.index:]) is not None
    def consume(self, r: Pattern, desc: str = "expected token not found") -> str:
        m = r.match(self.string[self.index:])
        if m is None:
            self.error(desc)
        consumed_str = m.group()
        self.index += len(consumed_str)
        # Keep track of physical source lines in the original code
        lines = consumed_str.count('\n')
        if lines > 0:
            self.line += lines
            self.column = len(consumed_str) - consumed_str.rfind('\n')
        else:
            self.column += len(consumed_str)
        return m.group()
    def loc(self) -> SrcLoc:
        return (self.line, self.column)
    def eof(self) -> bool:
        return self.index == len(self.string)
    def error(self, desc: str) -> NoReturn:
        s = 20
        context = self.string[self.index : self.index+s]
        if self.index + s < len(self.string):
            context += "..."
        raise SyntaxError("Syntax error, "+str(desc)+" (at "+str(self.line)+":"+str(self.column)+"): " +context)



def parse(s: str) -> List[AstNode]:
    ws = re.compile("^\s+")
    lparen = re.compile("^\\(")
    rparen = re.compile("^\\)")
    semicolon = re.compile("^;.*")
    ident = re.compile("([@$a-zA-Z_][-a-zA-Z0-9_!'.]*)|0|[1-9][0-9]*|[+-/*&^|<>=?~]+")

    def p_recur(input: Input) -> List[AstNode]:
        elems: List[AstNode] = []
        while True:
            if input.matches(lparen):
                start = input.loc()
                input.consume(lparen)
                elems.append(Parens(p_recur(input), start))
                input.consume(rparen, "expected )")
            elif input.matches(ident):
                loc = input.loc()
                elems.append(Atom(input.consume(ident), loc))
            elif input.matches(semicolon):
                input.consume(semicolon)
            elif input.matches(ws):
                input.consume(ws)
            else:
                return elems    
    input = Input(s)
    r = p_recur(input)
    if not input.eof():
        input.error("unexpected trailing tokens")
    return r
