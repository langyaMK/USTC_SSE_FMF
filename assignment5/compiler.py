import unittest

from z3 import *

import calc
import tac
from counter import counter


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


###############################################
# a compiler from Calc to Tac.


def compile_func(func: calc.Function) -> tac.Function:
    tac_stmts = []
    fresh_var = counter(f"tmp_{func.name}")

    def compile_expr(expr):
        if isinstance(expr, calc.ExprVar):
            return expr.var
        # raise Todo("Exercise 9: compile Calc expressions to Tac statements")
        if isinstance(expr, calc.ExprBop):
            new_var_1 = compile_expr(expr.left)
            new_var_2 = compile_expr(expr.right)
            new_var = next(fresh_var)
            if expr.bop is calc.BOp.ADD:
                tac_stmts.append(tac.StmtAssignAdd(new_var, new_var_1, new_var_2))
                return new_var
            elif expr.bop is calc.BOp.SUB:
                tac_stmts.append(tac.StmtAssignSub(new_var, new_var_1, new_var_2))
                return new_var
            elif expr.bop is calc.BOp.MUL:
                tac_stmts.append(tac.StmtAssignMul(new_var, new_var_1, new_var_2))
                return new_var
            elif expr.bop is calc.BOp.DIV:
                tac_stmts.append(tac.StmtAssignDiv(new_var, new_var_1, new_var_2))
                return new_var
            else:
                raise ValueError("unknown binary operator")

    def compile_stmt(stmt):
        if isinstance(stmt, calc.StmtAssign):
            tac_stmts.append(tac.StmtAssignVar(stmt.var, compile_expr(stmt.expr)))

    for calc_stmt in func.stmts:
        compile_stmt(calc_stmt)

    return tac.Function(func.name, func.args, tac_stmts, func.ret)


def translation_validation(original_func: calc.Function, result_func: tac.Function):
    # TODO: for the compiler to be correct, you should prove this condition:
    # TODO:     orig_cons /\ result_cons -> x1==x2
    # TODO: your code here:
    original_func_ssa = calc.to_ssa_func(original_func)
    result_func_ssa = tac.to_ssa_func(result_func)

    original_cons = calc.gen_cons_func(original_func_ssa)
    result_cons = tac.gen_cons_func(result_func_ssa)

    solver = Solver()

    # raise Todo("Exercise 9: do the translation validation by proving this condition: orig_cons /\ result_cons -> x1==x2")
    # note that the z3.And() can accept list of constraints
    P1 = And(original_cons)
    P2 = And(result_cons)
    F = Implies(And(P1, P2), original_cons[-1] == result_cons[-1])
    solver.add(Not(F))

    return solver


###############################################
# Tests


class TestTV(unittest.TestCase):

    tac_func = compile_func(calc.sample_f)

    def test_compile(self):
        res = ("f(s1,s2,t1,t2){\n\t_tmp_f_0 = s1 + t1;\n\t_tmp_f_1 = s2 + t2;\n\t"
               "_tmp_f_2 = _tmp_f_0 * _tmp_f_1;\n\tz = _tmp_f_2;\n\t_tmp_f_3 = z * s1;\n\t"
               "z = _tmp_f_3;\n\treturn z;\n}\n")

        # f(s1, s2, t1, t2){
        #   _tac_f_0 = s1 + t1;
        #   _tac_f_1 = s2 + t2;
        #   _tac_f_2 = _tac_f_0 * _tac_f_1;
        #   _tac_f_3 = _tac_f_2;
        #   _tac_f_4 = _tac_f_3 * s1;
        #   _tac_f_5 = _tac_f_4;
        #   return _tac_f_5;
        # }
        print(tac.to_ssa_func(self.tac_func))
        self.assertEqual(str(self.tac_func), res)

    def test_tv(self):
        solver = translation_validation(calc.sample_f, self.tac_func)

        # [Not(Implies(And(_calc_f_0 ==
        #                  f_mul(f_add(s1, t1), f_add(s2, t2)),
        #                  _calc_f_1 == f_mul(_calc_f_0, s1),
        #                  _tac_f_0 == f_add(s1, t1),
        #                  _tac_f_1 == f_add(s2, t2),
        #                  _tac_f_2 == f_mul(_tac_f_0, _tac_f_1),
        #                  _tac_f_3 == _tac_f_2,
        #                  _tac_f_4 == f_mul(_tac_f_3, s1),
        #                  _tac_f_5 == _tac_f_4),
        #              _calc_f_1 == _tac_f_5))]
        print(solver)
        self.assertEqual(str(solver.check()), "unsat")


if __name__ == '__main__':
    unittest.main()
