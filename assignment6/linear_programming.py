from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()



# A linear programming problem (shorted as LP in the following)
# consists of two parts: the constraints  and the target function. And our goal is
# to get the minimal or the maximal values of under the constraint,
# both the constraints and the target function are of linear forms.
def lp_examples():
    # decal variable in Int or Real type
    x, y = Ints("x y")

    # not Solver as we do in LA,
    # to solve LP with Z3, we'll be using the Optimizer module
    opt_max = Optimize()

    # add the constraints is same with LA
    cons = [x < 2, (y - x) < 1]
    opt_max.add(cons)

    # use maximize() and minimize() method to add the target function
    opt_max.maximize(x + 2 * y)

    # check the Optimizer as we do with Solver
    if opt_max.check() == sat:
        print(opt_max.model())

    # LP of real number is also supported by Z3
    x, y = Reals("x y")

    opt_min = Optimize()
    cons = [x <= 4.3, (y - x) <= 1.1, y >= 2.3]
    opt_min.add(cons)

    # minimize() will get minimal value of the target function
    opt_min.minimize(x + y)

    if opt_min.check() == sat:
        print(opt_min.model())


def lp_exercise():
    opt = Optimize()
    # exercise 14: Given the constraints:
    #  x - y >= 2.1
    #  x + z <= 5.5
    #  y - z <= 1.1
    #
    # try to calculate the maximal value of
    #   x + y + z
    # by using LP in Z3
    # Your code here:
    # raise Todo("exercise 14: please fill in the missing code.")
    x, y, z = Reals("x y z")
    cons = [(x - y) > 2.1, (x + z) < 5.5, (y - z) < 1.1]
    opt.add(cons)

    # use maximize() and minimize() method to add the target function
    opt.maximize(x + y + z)

    # check the Optimizer as we do with Solver
    if opt.check() == sat:
        print(opt.model())


if __name__ == '__main__':
    lp_examples()

    # should output: [z = 23/20, y = 9/4, x = 87/20]
    lp_exercise()
