from enum import Enum
from typing import List



class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

########################################
# This bunch of code declare the syntax for the language MiniPy:
'''
B ::= + | - | * | / | == | != | > | < | >= | <=
E ::= n | x | E B E
S ::= pass
    | x = E
    | seq(S, S)
    | f(E1, ..., En)
    | if(E, S, S)
    | while(E, S)
F ::= f((x1, ..., xn), S, E)
'''


##################################
# bops
class Bop(Enum):
    ADD = "+"
    MIN = "-"
    MUL = "*"
    DIV = "/"
    EQ = "=="
    NE = "!="
    GT = ">"
    GE = ">="
    LT = "<"
    LE = "<="


##########################################
# expressions
class Expr:
    pass


class ExprNum(Expr):
    def __init__(self, n: int):
        self.num = n

    def __str__(self):
        return f"{self.num}"


class ExprVar(Expr):
    def __init__(self, var: str):
        self.var = var

    def __str__(self):
        return f"{self.var}"


class ExprBop(Expr):
    def __init__(self, left: Expr, right: Expr, bop: Bop):
        self.left = left
        self.right = right
        self.bop = bop

    def __str__(self):
        if isinstance(self.left, ExprBop):
            left_str = f"({self.left})"
        else:
            left_str = f"{self.left}"

        if isinstance(self.right, ExprBop):
            right_str = f"({self.right})"
        else:
            right_str = f"{self.right}"

        return f"{left_str} {self.bop.value} {right_str}"


###############################################
# statement
class Stmt:
    def __init__(self):
        self.level = 0

    def __repr__(self):
        return str(self)


class StmtAssign(Stmt):
    def __init__(self, var: str, expr: Expr):
        super().__init__()
        self.var = var
        self.expr = expr

    def __str__(self):
        indent_space = self.level * "\t"
        return f"{indent_space}{self.var} = {self.expr}\n"


class StmtIf(Stmt):
    def __init__(self, expr: Expr, then_stmts: List[Stmt], else_stmts: List[Stmt]):
        super().__init__()
        self.expr = expr
        self.then_stmts = then_stmts
        self.else_stmts = else_stmts

    def __str__(self):
        indent_space = self.level * "\t"

        for stm in self.then_stmts:
            stm.level = self.level + 1

        for stm in self.else_stmts:
            stm.level = self.level + 1

        then_stmts_str = "".join([str(stmt) for stmt in self.then_stmts])
        else_stmts_str = "".join([str(stmt) for stmt in self.else_stmts])

        then_str = (f"{indent_space}if {self.expr} :\n"
                    f"{then_stmts_str}")

        if self.else_stmts:
            return (f"{then_str}"
                    f"{indent_space}else:\n"
                    f"{else_stmts_str}")
        else:
            return then_str


class StmtWhile(Stmt):
    def __init__(self, expr: Expr, stmts: List[Stmt]):
        super().__init__()
        self.expr = expr
        self.stmts = stmts

    def __str__(self):
        indent_space = self.level * "\t"
        for stmt in self.stmts:
            stmt.level = self.level + 1

        stmts_str = "".join([str(stmt) for stmt in self.stmts])

        return (f"{indent_space}while {self.expr}:\n"
                f"{stmts_str}")


###############################################
# function
class Function:
    def __init__(self, name: str, args: List[str], stmts: List[Stmt], ret: Expr):
        self.name = name
        self.args = args
        self.stmts = stmts
        self.ret = ret

    def __str__(self):
        arg_str = ",".join(self.args)
        for stmt in self.stmts:
            stmt.level += 1

        stmts_str = "".join([str(stmt) for stmt in self.stmts])

        # exercise 1: Finish the magic methods __str__() method to get the
        # desired code-printing result：
        #
        # Your code here：

        raise Todo("exercise 1: please fill in the missing code.")


###############################################
# test

test_stmt = [StmtAssign('s', ExprNum(0)),
             StmtAssign('i', ExprNum(0)),
             StmtWhile(ExprBop(ExprVar('i'), ExprBop(ExprVar('n'), ExprNum(3), Bop.MIN), Bop.LE),
                       [StmtAssign('s', ExprBop(ExprVar('s'), ExprVar('i'), Bop.ADD)),
                        StmtAssign('i', ExprBop(ExprVar('i'), ExprNum(1), Bop.ADD)),
                        StmtIf(ExprBop(ExprVar('s'), ExprVar('i'), Bop.GT),
                               [StmtAssign("b", ExprBop(ExprVar('s'), ExprNum(1), Bop.MIN))],
                               [])
                        ]),
             StmtIf(ExprBop(ExprVar('s'), ExprVar('i'), Bop.GT),
                    [StmtAssign("s", ExprBop(ExprVar('i'), ExprNum(1), Bop.MIN))],
                    [StmtAssign("s", ExprBop(ExprVar('i'), ExprNum(1), Bop.ADD))])
             ]

test_func = Function(name='printer_test', args=['n'], stmts=test_stmt, ret=ExprVar('s'))


if __name__ == '__main__':
    # Your code should print:
    #
    # def printer_test(n):
    #     s = 0
    #     i = 0
    #     while i <= (n - 3):
    #         s = s + i
    #         i = i + 1
    #         if s > i:
    #             b = s - 1
    #     if s > i:
    #         s = i - 1
    #     else:
    #         s = i + 1
    #     return s
    #
    print(test_func)
