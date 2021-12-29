from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# In this part of the assignment, we'll implement the
# array elimination algorithm, as described in the class.


# First, let's define the basic data structures to represent
# the bit vector syntax:
#   E ::= c | x | select(E, E) | update(E, E, E)
#   R ::= E=E | E!=E
#   P ::= R | P/\P

# we use a functional programming style in this assigment.

###############################################################
# Part I: the bit vector syntax.
class Exp:
    pass


class ExpConst(Exp):
    def __init__(self, c: str):
        self.c = c


class ExpVar(Exp):
    def __init__(self, x: str):
        self.x = x


class ExpSelect(Exp):
    def __init__(self, array, index):
        self.array = array
        self.index = index


class ExpUpdate(Exp):
    def __init__(self, array, index, element):
        self.array = array
        self.index = index
        self.element = element


class ExpCall(Exp):
    def __init__(self, f, x):
        self.f = f
        self.x = x


#############################
# relations, as before
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


class PropFalse(Prop):
    def __init__(self):
        pass


class PropTrue(Prop):
    def __init__(self):
        pass


class PropSingle(Prop):
    def __init__(self, r):
        self.r = r


class PropAnd(Prop):
    def __init__(self, left: Prop, right: Prop):
        self.left = left
        self.right = right


class PropForall(Prop):
    def __init__(self, var: str, prop: Prop):
        self.var = var
        self.prop = prop


# this is only used internally
class PropImply(Prop):
    def __init__(self, left: Prop, right: Prop):
        self.left = left
        self.right = right


# printing facilities
def print_atomic(s):
    print(s, "", end="")


def print_exp(e):
    if isinstance(e, ExpConst):
        print_atomic(e.c)
    elif isinstance(e, ExpVar):
        print_atomic(e.x)
    elif isinstance(e, ExpSelect):
        print_atomic("(")
        print_exp(e.array)
        print_atomic("[")
        print_exp(e.index)
        print_atomic("])")
    elif isinstance(e, ExpUpdate):
        print_atomic("(")
        print_exp(e.array)
        print_atomic("[")
        print_exp(e.index)
        print_atomic("] = ")
        print_exp(e.element)
        print_atomic(")")
    elif isinstance(e, ExpCall):
        print(e.f)
        print_atomic("(")
        print_atomic(e.x)
        print_atomic(")")


def print_relation(r):
    if isinstance(r, RelationEq):
        print_atomic("(")
        print_exp(r.left)
        print_atomic("=")
        print_exp(r.right)
        print_atomic(")")
    elif isinstance(r, RelationNe):
        print_atomic("(")
        print_exp(r.left)
        print_atomic("!=")
        print_exp(r.right)
        print_atomic(")")


def print_prop(p):
    if isinstance(p, PropFalse):
        print_atomic("F")
    elif isinstance(p, PropTrue):
        print_atomic("T")
    elif isinstance(p, PropSingle):
        print_relation(p.r)
    elif isinstance(p, PropAnd):
        print_atomic("(")
        print_prop(p.left)
        print_atomic("/\\")
        print_prop(p.right)
        print_atomic(")")
    elif isinstance(p, PropImply):
        print_prop(p.left)
        print_atomic("\n->\n")
        print_prop(p.right)
    elif isinstance(p, PropForall):
        print_atomic("(forall ")
        print_atomic(p.var)
        print_atomic(".")
        print_prop(p.prop)
        print_atomic(")")
    else:
        print(p.__class__)
        print_atomic("what???")
        exit(999)


# select(update(A, i, x), i) == x
def gen_sample_prop():
    return PropSingle(RelationEq(ExpSelect(ExpUpdate(ExpVar("A"),
                                                     ExpVar("i"),
                                                     ExpConst("x")),
                                           ExpVar("i")),
                                 ExpConst("x")))


###############################################################
# Part II: the array elimination algorithm.

# the counter, to generate nice variable names.
counter = 0


def fresh_var():
    global counter
    name = "x_%d" % counter
    counter = counter + 1
    return name


# newly generated propositions
props = []


# exercise challenge: implement the array elimination algorithm
def elim_update_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_update_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_update_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")


# this is the first step of pass #3: eliminate "forall"
# we collect all array variables and index variables
array_vars = set()


def emit_array(v: ExpVar):
    raise Todo("exercise challenge: please fill in the missing code.")


index_vars = set()


def emit_index(v: ExpVar):
    raise Todo("exercise challenge: please fill in the missing code.")


def collect_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def collect_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def collect_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")

# pass #3: eliminate forall
# e[x|->y]
def subst_exp(e, x, y):
    raise Todo("exercise challenge: please fill in the missing code.")


def subst_relation(r, x, y):
    raise Todo("exercise challenge: please fill in the missing code.")


# p[x|->y]
def subst_prop_0(p, x, y):
    raise Todo("exercise challenge: please fill in the missing code.")


def subst_prop(p, x: str):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_forall_prop_0(p: Prop):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_forall_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")


# pass #4: eliminate array "select"
def elim_select_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_select_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def elim_select_prop(p: Prop):
    raise Todo("exercise challenge: please fill in the missing code.")


# Input: an array proposition
# output: a EUF proposition
def array_elim(p):
    # pass #1: eliminate all array update "A[i] = e"
    p = elim_update_prop(p)
    print("\nthe proposition after array update elimination:")
    print_prop(p)
    # pass #2: eliminate "exists"
    # pass #3: eliminate "forall"
    p = elim_forall_prop(p)
    print(array_vars)
    print(index_vars)
    print_prop(p)

    # pass #4: eliminate array "select"
    p = elim_select_prop(p)
    print_prop(p)
    return p


# convert to Z3 format
def to_z3_exp(e):
    raise Todo("exercise challenge: please fill in the missing code.")


def to_z3_relation(r):
    raise Todo("exercise challenge: please fill in the missing code.")


def to_z3_prop(p):
    raise Todo("exercise challenge: please fill in the missing code.")

if __name__ == '__main__':
    sample_prop = gen_sample_prop()
    print("the raw proposition:")
    print_prop(sample_prop)
    p = array_elim(sample_prop)

    # convert to Z3 friendly format
    p = to_z3_prop(p)
    print("\n\nthe z3 proposition:")
    print(p)
    # send constraint to the SAT solver
    solver = Solver()
    solver.add(Not(p))
    res = solver.check()
    if res == sat:
        print(solver.model())
    else:
        print("\033[31munsat!\033[0m")
