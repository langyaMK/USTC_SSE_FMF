from enum import Enum
from typing import List

from z3 import *

from counter import counter


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


##################################
# The abstract syntax for the Calc language:
'''
bop ::= + | - | * | /
E   ::= x | E bop E
S   ::= x=E
F   ::= f(x1, …, xn){S;* return E;}
'''


# binary operator
class BOp(Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"


# expression
class Expr:
    def __repr__(self):
        return self.__str__()


class ExprVar(Expr):
    def __init__(self, var: str):
        self.var = var

    def __str__(self):
        return f"{self.var}"


class ExprBop(Expr):
    def __init__(self, left: Expr, right: Expr, bop: BOp):
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


# statement
class Stmt:
    def __init__(self):
        self.level = 0

    def __repr__(self):
        return self.__str__()


class StmtAssign(Stmt):
    def __init__(self, var: str, expr: Expr):
        super().__init__()
        self.var = var
        self.expr = expr

    def __str__(self):
        indent_space = self.level * "\t"
        return f"{indent_space}{self.var} = {self.expr};\n"


# function:
class Function:
    def __init__(self, name: str, args: List[str], stmts: List[Stmt], ret: str):
        self.name = name
        self.args = args
        self.stmts = stmts
        self.ret = ret

    def __str__(self):
        arg_str = ",".join(self.args)
        for stm in self.stmts:
            stm.level += 1

        stmts_str = "".join([str(stmt) for stmt in self.stmts])

        return (f"{self.name}({arg_str}){{\n"
                f"{stmts_str}"
                f"\treturn {self.ret};\n"
                f"}}\n")


###############################################
# SSA conversion:

# take a function 'func', convert it to SSA
def to_ssa_func(func: Function) -> Function:
    # a map from variable to new variable:
    # init it by putting every argument into the map
    var_map = {arg: arg for arg in func.args}

    # fresh variable generator
    fresh_var = counter(prefix=f"calc_{func.name}")

    def to_ssa_expr(expr):
        if isinstance(expr, ExprVar):
            return ExprVar(var_map[expr.var])

        if isinstance(expr, ExprBop):
            return ExprBop(to_ssa_expr(expr.left), to_ssa_expr(expr.right), expr.bop)

    def to_ssa_stmt(stmt):
        if isinstance(stmt, StmtAssign):
            new_expr = to_ssa_expr(stmt.expr)
            new_var = next(fresh_var)
            var_map[stmt.var] = new_var
            return StmtAssign(new_var, new_expr)

    # to convert each statement one by one:
    new_stmts = [to_ssa_stmt(stmt) for stmt in func.stmts]

    return Function(func.name, func.args, new_stmts, var_map[func.ret])


###############################################
# Generate Z3 constraints:
def gen_cons_exp(expr: Expr):
    if isinstance(expr, ExprVar):
        return Const(expr.var, DeclareSort('S'))

    if isinstance(expr, ExprBop):
        if expr.bop is BOp.ADD:
            func_name = "f_add"
        elif expr.bop is BOp.SUB:
            func_name = "f_sub"
        elif expr.bop is BOp.MUL:
            func_name = "f_mul"
        elif expr.bop is BOp.DIV:
            func_name = "f_div"
        else:
            raise ValueError("unknown binary operator")

        left = gen_cons_exp(expr.left)
        right = gen_cons_exp(expr.right)

        return z3.Function(func_name,
                           DeclareSort('S'),
                           DeclareSort('S'),
                           DeclareSort('S')).__call__(left, right)


def gen_cons_stm(stmt):
    if isinstance(stmt, StmtAssign):
        return Const(stmt.var, DeclareSort('S')) == gen_cons_exp(stmt.expr)


def gen_cons_func(func):
    return [gen_cons_stm(stmt) for stmt in func.stmts]


# a sample program:
sample_f = Function('f',
                    ['s1', 's2', 't1', 't2'],
                    [StmtAssign('z', ExprBop(ExprBop(ExprVar('s1'), ExprVar('t1'), BOp.ADD),
                                             ExprBop(ExprVar('s2'), ExprVar('t2'), BOp.ADD),
                                             BOp.MUL)),
                     StmtAssign('z', ExprBop(ExprVar('z'), ExprVar('s1'), BOp.MUL))],
                    'z')

if __name__ == '__main__':
    # print the original program
    print(sample_f)
    # convert it to SSA
    new_f = to_ssa_func(sample_f)
    # print the converted program
    print(new_f)
    # generate Z3 constraints
    print(gen_cons_func(new_f))
