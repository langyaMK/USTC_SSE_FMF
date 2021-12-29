import random
from dataclasses import dataclass
from typing import Dict

from z3 import *
from mini_py import *

from symbolic import check_cond, neg_exp, symbolic_expr, f1
from concrete import interpret_expr



class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# a concolic execution engine.

# concolic memory model will store arguments, concrete values, symbolic values and path condition
@dataclass
class Memory:
    args: List[str]
    concrete_memory: Dict[str, int]
    symbolic_memory: Dict[str, Expr]
    path_condition: List[Expr]

    def __str__(self):
        arg_str = ",".join(self.args)
        actual_str = ",".join([f"{var} = {value}" for var, value in self.concrete_memory.items()])
        expr_str = "\n".join([f"\t{var} = {value}" for var, value in self.symbolic_memory.items()])
        cond_str = ",".join([str(cond) for cond in self.path_condition])
        return (f"Arguments: {arg_str}\n"
                f"Path Condition: {cond_str}\n"
                f"Actual Table: {actual_str}\n"
                f"Symbol Table: \n"
                f"{expr_str}\n")


#####################
#  concolic execution
def concolic_stmt(memory, stmt):
    if isinstance(stmt, StmtAssign):
        # exercise 8: Deal with assign-statement, you need to maintain both a symbolic
        # memory and a concrete memory. You can directly use the corresponding functions
        # symbolic.py and concrete.py file.
        #
        # Your code here：

        raise Todo("exercise 8: please fill in the missing code.")

    elif isinstance(stmt, StmtIf):
        # exercise 8: Deal with if-statement, recall that concolic execution will do the
        # concrete execute on if-statement, but it need to store the path condition to the memory.
        #
        # Your code here：

        raise Todo("exercise 8: please fill in the missing code.")

    elif isinstance(stmt, StmtWhile):
        # exercise 9: Process the while-statement, what you need to do is execute the
        # loop expression by concrete execution to decide whether to continue,
        # and for the statements contained by while-statement, do the concolic
        # execution. Don't forget to add the loop judgment expression to the
        # path condition list for every loop.
        #
        # Your code here：

        raise Todo("exercise 9: please fill in the missing code.")

    return memory


def concolic_stmts(memory, stmts):
    for stmt in stmts:
        concolic_stmt(memory, stmt)

    return memory


def concolic_func(func, init_concrete):
    # init memory
    init_symbolic = dict(zip(func.args, [ExprVar(arg) for arg in func.args]))
    memory = Memory(func.args, init_concrete, init_symbolic, [])

    concolic_stmts(memory, func.stmts)
    return memory, interpret_expr(memory, func.ret)


def concolic_executor(func, init_params, try_times):
    init_concrete = dict(zip(func.args, init_params))
    print(f"First Try, Input Value: {init_concrete}")
    memory, _ = concolic_func(func, init_concrete.copy())
    print(memory)

    # random select and negate one condition from previous result
    # and use z3 to generate a input to do next concolic execution
    for try_time in range(2, try_times+1, 1):
        random_idx = random.randrange(0, len(memory.path_condition))
        memory.path_condition[random_idx] = neg_exp(memory.path_condition[random_idx])
        ret, solver = check_cond(memory)

        if ret == sat:
            # use z3 result update new input concrete values
            model = solver.model()
            for dec in model.decls():
                if dec.name() in func.args:
                    init_concrete[dec.name()] = model[dec].as_long()

            print(f"Try times: {try_time}, Input Value: {init_concrete}")
            memory, _ = concolic_func(func, init_concrete.copy())
            print(memory)
        else:
            print(f"Try times: {try_time}, Path conditions got UNSAT/UNKNOWN from z3")
            print(f"Conditions try to Solve: {solver}\n")


#####################
# test code
func_loop = Function("loop", ["m", "n"],
                     [StmtWhile(ExprBop(ExprVar("m"), ExprVar("n"), Bop.LT),
                                [StmtIf(ExprBop(ExprVar("m"), ExprNum(0), Bop.GT),
                                        [StmtAssign("m", ExprBop(ExprVar("m"), ExprNum(2), Bop.MUL))],
                                        [StmtAssign("m", ExprBop(ExprVar("m"), ExprNum(1), Bop.ADD))
                                         ])
                                 ])
                      ], ExprVar("m"))

# example for challenge
hard_stmt_1 = ExprBop(ExprBop(ExprBop(ExprVar("y"), ExprVar("y"), Bop.MUL), ExprVar("x"), Bop.MUL),
                      ExprBop(ExprVar("y"), ExprNum(23123), Bop.MUL), Bop.ADD)

func_foo = Function("foo", ["x", "y"],
                    [StmtAssign("m", hard_stmt_1),
                     StmtIf(ExprBop(ExprVar("m"), ExprVar("y"), Bop.LE),
                            [StmtAssign("s", ExprNum(1))],
                            [StmtAssign("s", ExprNum(2))])
                     ], ExprVar("s"))


if __name__ == '__main__':
    print(f1)

    # sample output(not the exactly output):
    # change the try_times as you want
    #
    # First Try, Input Value: {'a': 0, 'b': 0}
    # Arguments: a,b
    # Path Condition: a == 0
    # Actual Table: a = 0,b = 0,x = 1,y = 0
    # Symbol Table:
    # 	a = a
    # 	b = b
    # 	x = 1
    # 	y = 0
    #
    # Try times: 2, Input Value: {'a': 1, 'b': 0}
    # Arguments: a,b
    # Path Condition: a != 0,b == 0
    # Actual Table: a = 1,b = 0,x = 2,y = 4
    # Symbol Table:
    # 	a = a
    # 	b = b
    # 	x = 2 * (a + b)
    # 	y = 1 + 3
    #
    # Try times: 3, Input Value: {'a': 1, 'b': 1}
    # Arguments: a,b
    # Path Condition: a != 0,b != 0
    # Actual Table: a = 1,b = 1,x = 1,y = 4
    # Symbol Table:
    # 	a = a
    # 	b = b
    # 	x = 1
    # 	y = 1 + 3
    concolic_executor(f1, [0, 0], try_times=3)
    print(func_loop)

    # Should output:
    #
    # First Try, Input Value: {'m': 0, 'n': 4}
    # Arguments: m, n
    # Path Condition: m < n, m <= 0, (m + 1) < n, (m + 1) > 0, ((m + 1) * 2) < n, ((m + 1) * 2) > 0, (((m + 1) * 2) * 2) >= n
    # Actual Table: m = 4, n = 4
    # Symbol Table:
    #   m = ((m + 1) * 2) * 2
    #   n = n
    concolic_executor(func_loop, [0, 4], 1)
