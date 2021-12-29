import unittest
from dataclasses import dataclass
from typing import Dict

from mini_py import *



class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# a concrete execution engine.


# exercise 2: Run the code below, which is the data model
# of concrete memory. Concrete execution memory model will store arguments
# and concrete values. Make sure you understand the model and you don't
# need to write any code here.

# concrete execution memory model will store arguments and concrete values
@dataclass
class Memory:
    args: List[str]
    concrete_memory: Dict[str, int]

    def __str__(self):
        arg_str = ",".join(self.args)
        concrete_str = "\n".join([f"\t{var}: {value}" for var, value in self.concrete_memory.items()])
        return (f"Arguments: {arg_str}\n"
                f"Concrete Values: \n"
                f"{concrete_str}\n")


#####################
#  concrete execution
def interpret_expr(memory, expr):
    if isinstance(expr, ExprNum):
        return expr.num

    if isinstance(expr, ExprVar):
        return memory.concrete_memory[expr.var]

    if isinstance(expr, ExprBop):
        if expr.bop is Bop.ADD:
            return interpret_expr(memory, expr.left) + interpret_expr(memory, expr.right)
        if expr.bop is Bop.MIN:
            return interpret_expr(memory, expr.left) - interpret_expr(memory, expr.right)
        if expr.bop is Bop.MUL:
            return interpret_expr(memory, expr.left) * interpret_expr(memory, expr.right)
        if expr.bop is Bop.DIV:
            return interpret_expr(memory, expr.left) / interpret_expr(memory, expr.right)
        if expr.bop is Bop.EQ:
            return interpret_expr(memory, expr.left) == interpret_expr(memory, expr.right)
        if expr.bop is Bop.NE:
            return interpret_expr(memory, expr.left) != interpret_expr(memory, expr.right)
        if expr.bop is Bop.GT:
            return interpret_expr(memory, expr.left) > interpret_expr(memory, expr.right)
        if expr.bop is Bop.GE:
            return interpret_expr(memory, expr.left) >= interpret_expr(memory, expr.right)
        if expr.bop is Bop.LT:
            return interpret_expr(memory, expr.left) < interpret_expr(memory, expr.right)
        if expr.bop is Bop.LE:
            return interpret_expr(memory, expr.left) <= interpret_expr(memory, expr.right)


def interpret_stm(memory, stmt):
    # exercise 3: Complete the code to interpret statement in MiniPy, by
    # following the big-step operational semantics rules from the lecture note.
    #
    # Your code here：

    raise Todo("exercise 3: please fill in the missing code.")
    return memory


def interpret_stmts(memory, stmts):
    for stmt in stmts:
        interpret_stm(memory, stmt)
    return memory


def interpret_func(func, params):
    assert len(func.args) == len(params), "The number of parameters does not match"
    memory = Memory(func.args, dict(zip(func.args, params)))
    interpret_stmts(memory, func.stmts)
    return interpret_expr(memory, func.ret)


#######################################
# test code
func_sum = Function('sum', ['n'],
                    [StmtAssign('s', ExprNum(0)),
                     StmtAssign('i', ExprNum(0)),
                     StmtWhile(ExprBop(ExprVar('i'), ExprVar('n'), Bop.LE),
                               [StmtAssign('s', ExprBop(ExprVar('s'), ExprVar('i'), Bop.ADD)),
                                StmtAssign('i', ExprBop(ExprVar('i'), ExprNum(1), Bop.ADD))
                                ])
                     ], ExprVar('s'))

func_max = Function("max", ["m", "n"],
                    [StmtAssign("c", ExprVar("m")),
                     StmtIf(ExprBop(ExprVar("n"), ExprVar("c"), Bop.GT),
                            [StmtAssign("c", ExprVar("n"))],
                            [])
                     ], ExprVar("c"))

func_gcd = Function("gcd", ["m", "n"],
                    [StmtWhile(ExprBop(ExprVar("m"), ExprVar("n"), Bop.NE),
                               [StmtIf(ExprBop(ExprVar("m"), ExprVar("n"), Bop.GE),
                                       [StmtAssign("m", ExprBop(ExprVar("m"), ExprVar("n"), Bop.MIN))],
                                       [StmtAssign("n", ExprBop(ExprVar("n"), ExprVar("m"), Bop.MIN))])
                                ])
                     ], ExprVar("m"))


class TestConcrete(unittest.TestCase):
    def test_interpret_exp(self):

        # 3 + 2 >= 3 * 2
        exp1 = ExprBop(ExprBop(ExprNum(3), ExprNum(2), Bop.ADD),
                       ExprBop(ExprNum(3), ExprNum(2), Bop.MUL),
                       Bop.GE)

        # 10 / 2 != 8 - 2
        exp2 = ExprBop(ExprBop(ExprNum(10), ExprNum(2), Bop.DIV),
                       ExprBop(ExprNum(8), ExprNum(2), Bop.MIN),
                       Bop.NE)

        self.assertEqual(interpret_expr({}, exp1), False)
        self.assertEqual(interpret_expr({}, exp2), True)

    def test_interpret_func_sum(self):
        # print(func_sum)
        self.assertEqual(interpret_func(func_sum, [100]), 5050)

    def test_interpret_func_max(self):
        # print(func_max)
        self.assertEqual(interpret_func(func_max, [10, 20]), 20)

    def test_interpret_func_gcd(self):
        # print(func_gcd)
        self.assertEqual(interpret_func(func_gcd, [60, 48]), 12)


if __name__ == '__main__':
    unittest.main()

