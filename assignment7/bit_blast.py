from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# In this part of the assignment, we'll implement the
# bit-blasting algorithm, as described in the class.


# First, let's define the basic data structures to represent
# the bit vector syntax:
#   E ::= c | x | E&E | E|E | ~E
#   R ::= E=E | E!=E
#   P ::= R | P/\P

# we use a functional programming style in this assigment.

###############################################################
# Part I: the bit vector syntax.
class Exp:
    # vars are the generated bit variables
    def __init__(self, gen_vars):
        self.gen_vars = gen_vars


class ExpConst(Exp):
    def __init__(self, c):
        super().__init__([])
        self.c = c


class ExpVar(Exp):
    def __init__(self, x):
        super().__init__([])
        self.x = x


class ExpBitwiseAnd(Exp):
    def __init__(self, left, right):
        super().__init__([])
        self.left = left
        self.right = right


class ExpBitwiseOr(Exp):
    def __init__(self, left, right):
        super().__init__([])
        self.left = left
        self.right = right


class ExpBitwiseNot(Exp):
    def __init__(self, e):
        super().__init__([])
        self.e = e


####
# relations
class Relation:
    pass


class RelationEq(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class RelationNe(Relation):
    def __init__(self, left, right):
        self.left = left
        self.right = right


####
# propositions
class Prop:
    pass


class PropSingle(Prop):
    def __init__(self, r):
        self.r = r


class PropAnd(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right


# printing facilities
# a flag to control whether or not to print the attached boolean variables
should_print_vars = False


def print_atomic(s):
    print(s, "", end="")


def print_exp(e):
    if isinstance(e, ExpConst):
        print_atomic(e.c)
    elif isinstance(e, ExpVar):
        print_atomic(e.x)
    elif isinstance(e, ExpBitwiseAnd):
        print_exp(e.left)
        print_atomic("&")
        print_exp(e.right)
    elif isinstance(e, ExpBitwiseOr):
        print_exp(e.left)
        print_atomic("|")
        print_exp(e.right)
    elif isinstance(e, ExpBitwiseAnd):
        print_atomic("~")
        print_exp(e.e)

    if should_print_vars:
        print(e.gen_vars, sep=', ')


def print_relation(r):
    if isinstance(r, RelationEq):
        print_exp(r.left)
        print_atomic("=")
        print_exp(r.right)
    elif isinstance(r, RelationNe):
        print_exp(r.left)
        print("!=")
        print_exp(r.right)


def print_prop(p):
    if isinstance(p, PropSingle):
        print_relation(p.r)
    elif isinstance(p, PropAnd):
        print_prop(p.left)
        print_atomic("/\\")
        print_prop(p.right)


# x=1 /\ y=2 /\ x&y=1
def gen_sample_prop():
    return PropAnd(PropAnd(PropSingle(RelationEq(ExpVar("x"),
                                                    ExpConst(1))),
                              PropSingle(RelationEq(ExpVar("y"),
                                                    ExpConst(2)))),
                      PropSingle(RelationEq(ExpBitwiseAnd(ExpVar("x"),
                                                          ExpVar("y")),
                                            ExpConst(1))))


###############################################################
# Part II: the bit blasting algorithm.

# the width, to make debugging simple, use smaller "L".
L = 2

# the counter, to generate nice variable names.
counter = 0


# a dictionary used to remember variables' boolean variable list
var_map = {}


def gen_var_list():
    global counter
    names = [Bool(f"x_{i}") for i in range(counter, counter+L)]
    counter = counter + L
    return names


# bit blasting a proposition
cons = []


# exercise challenge: implement the array elimination algorithm
def blast_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def blast_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def blast_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")


# pass #2: generate constraints
def gen_cons_exp_const(n, the_vars):
    raise Todo("exercise challenge: please fill in the missing code.")
        

def gen_cons_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def gen_equal_vars(l, r):
    raise Todo("exercise challenge: please fill in the missing code.")


def gen_cons_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def gen_cons_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")


# Input: a proposition
# output: a set of constraints, in "cons"
def bit_blast(p):
    raise Todo("exercise challenge: please fill in the missing code.")


if __name__ == '__main__':
    sample_prop = gen_sample_prop()
    print("the raw proposition:")
    print_prop(sample_prop)
    print("\nthe blasted proposition:")
    cons = bit_blast(sample_prop)
    print("the generated constraints:")
    print(cons)
    # send constraint to the SAT solver
    solver = Solver()
    solver.add(cons)
    res = solver.check()
    if res == sat:
        print(solver.model())
    else:
        print("\033[31munsat!\033[0m")



