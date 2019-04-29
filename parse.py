
import re
import sys

class Atom(object):
    def __init__(self, name, src_loc = (0,0)):
        self.n = name
        self.loc = src_loc
    def __repr__(self):
        return self.n
    def name(self):
        return self.n

class List(object):
    def __init__(self, children, src_loc = (0,0)):
        self.children = children
        self.loc = src_loc
    def __repr__(self):
        return "({})".format(" ".join(map(repr, self.children)))
    def __len__(self):
        return len(self.children)
    def __getitem__(self, i):
        return self.children[i]

class Input(object):
    def __init__(self, s):
        self.string = s
        self.index = 0
        self.line = 1
        self.column = 1
    def matches(self, r):
        return r.match(self.string[self.index:]) is not None
    def consume(self, r, desc = "expected token not found"):
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
    def loc(self):
        return (self.line, self.column)
    def eof(self):
        return self.index == len(self.string)
    def error(self, desc):
        s = 20
        context = self.string[self.index : self.index+s]
        if self.index + s < len(self.string):
            context += "..."
        raise RuntimeError("Syntax error, "+str(desc)+" (at "+str(self.line)+":"+str(self.column)+"): " +context)

ws = re.compile("^\s+")
lparen = re.compile("^\\(")
rparen = re.compile("^\\)")
semicolon = re.compile("^;.*")
ident = re.compile("(^[a-zA-Z_][a-zA-Z0-9_!'.]*)|[1-9][0-9]*|[+-/*&^|<>=?~]+")

def p_recur(input):
    elems = []
    while True:
        if input.matches(lparen):
            start = input.loc()
            input.consume(lparen)
            elems.append(List(p_recur(input), start))
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

def parse(s):
    input = Input(s)
    r = p_recur(input)
    if not input.eof():
        input.error("unexpected trailing tokens")
    return r

if __name__ == "__main__":
    print(parse(open(sys.argv[1]).read()))
