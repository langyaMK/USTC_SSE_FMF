from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


#########################################
# Introduction

# Welcome to this assignment: the linear arithmetic (LA) and linear programming (LP).
# In this assignment, you'll be getting familiarized yourself with basic linear
# arithmetic and linear programming, by using the Z3 theorem prover/solver.

# This assignment consists of three parts:
#   1. the basic LA and LP theories;
#   2. the important applications of the LA and LP theories;
#   3. the algorithms behind the modern LA/LP theories.
#
# this is the first one.


#########################################
# Basic Linear Arithmetics

# Roughly speaking, Z3 can solve a group of equalities/inequalities, suppose
# we can have two numbers x and y on R domain, we can declare them in Z3 as:
x, y = Reals('x y')
# here, "Reals" is a class, representing the R domain.
# Now, suppose we want to check that whether or not the following constraints (a group of
# equalities) are satisfiable:
#  { x + y = 0.8
#  { x - y = 0.2
# then we can create a new solver:
solver = Solver()
# and add these constraints into this "solver":
solver.add(x + y == 0.8, x - y == 0.2)
# please note that: comparing with the above mathematical notation, there is only
# one minor difference, in math, we use the symbol "=", but in Z3, we use "==".
# We then drive Z3 to check these two constraints:
res = solver.check()
# and if Z3 return "sat" on these constraints, we can print the concrete values
# for variables "x" and "y".
print("result for problem 1:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)

# exercise 1: run the above code and check the result, is the result correct?
# you don't need to write any code, just make sure you understand the output.


# Of course, not all constraints are satisfiable, given two variables "x" and "y" on
# domain R, consider the following constraints:
#   { x + y = 0.8
#   { x + y = 0.2
# obviously, these constraints are unsatisfiable, and we let Z3 to check this fact:
x, y = Reals('x y')
solver.add(x + y == 0.8, x + y == 0.2)
res = solver.check()
print("result for problem 2:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)
# exercise 2: For the above constraints, please write down code that creating the
# solver and checking these constraints. Make sure your code outputs "unsat".
# raise Todo("exercise 2: please fill in the missing code.")


# Besides the domain real ("Reals"), Z3 also has decent support for the
# Integer domain. For instance, this code
x, y = Ints('x y')
solver = Solver()
solver.add(x + y == 8, x - y == 2)
res = solver.check()
print("result for problem 3:")
if res == sat:
    model = solver.model()
    print(model)
else:
    print(res)
# declares two integers "x" and "y".
# Similarly, we can ask Z3 to check constraints on Integers, for instance:
#   { x + y = 8
#   { x - y = 2
# exercise 3: please write code to check the above constraints, make sure
# your code should output some like "[x = 5, y = 3]'.
# raise Todo("exercise 3: please fill in the missing code.")


# To this point, as you can observe, the code fragment we already wrote
# has many duplications, so it's a good point to clean them by refactoring
# the common part.
# For this purpose, we write the following function "check_cons()", which
# takes a list of constraints, and output the checking result.
def check_cons(constraints):
    solver = Solver()
    solver.add(constraints)
    res = solver.check()
    if res == sat:
        model = solver.model()
        # print(model)
        return res, model
    else:
        # print(res)
        return res, None


def print_model(res, model):
    if res == sat:
        print(model)
        return
    print(res)
    return


# thus, we can simplify our previous implementation by just calling
# this function, as in:
x, y = Ints('x y')
res, model = check_cons([x + y == 20, x - y == 10])
print_model(res, model)

# One key point to note here is that: when we talk about the satisfiability of
# constraints, we must make it clear what domains (R, Z, or Q?) we are
# working on, because the satisfiability of constraints is dependent on
# the underlying domain.
# To understand this, let's consider the following example, given these
# constraints:
#  { x + y = 8
#  { x - y = 1
# we can conclude that these constraints are satisfiable on domain R, but not
# on domain Z.
# exercise 4: write code to check the above constraints are satisfiable
# domain R, but not on domain Z. You should finish your code, by calling
# the above "check_cons()" function.
x, y = Reals('x, y')
cons = [x + y == 8, x - y == 1]
# raise Todo("exercise 4: please fill in the missing code.")
print('result for problem 4:')
res, model = check_cons(cons)
print_model(res, model)

#########################################
# 0-1 Linear Arithmetic

# There is one important special case for the LA on domain Z, which
# is called the 0-1 integer linear arithmetics. In this case, all
# integer variables can only be of two values: 0 or 1, in this sense,
# they corresponds, perfectly, to boolean values (true or false).
# Let's study one concrete example, given the following constraints
# on integers Z:
x, y = Ints('x, y')
cons = [x + y == 8, x - y == 2]
# but we also require that both "x" and "y" can only be "0" or "1",
# this is given by the following two constraints:
cons_x = [Or(x == 1, x == 0)]
cons_y = [Or(y == 1, y == 0)]
# thus, we only need to check the union of these constraints, as in:
print("0-1 la result:")
res, model = check_cons(cons + cons_x + cons_y)
print_model(res, model)

# The 0-1 Integer LA (and also the 0-1 Integer LP) has many important
# applications, we'll discuss some in the future. But for now, let's
# consider one interesting problem, to let us appreciate its simplicity
# and power: suppose we are given a list of integers, and we want to
# write a program, to check that whether or not there is at least one
# zero (0) in this list.
# Here are some sample inputs and the expected outputs:
#   Input:            Output:
l1 = [1, 2, 4, 5]  # false
l2 = [3, 0, 8, 2]  # true
l3 = [4, 0, 3, 0]  # true


# First, let's warm up, by writing a normal version:
def check_zero_normal(l):
    for x in l:
        if x == 0:
            return True
    return False


# unit test the above function:
assert (not check_zero_normal(l1))
assert (check_zero_normal(l2))
assert (check_zero_normal(l3))


# Now, let's consider how to solve this problem using 0-1 integer LA,
# for this, let's first declare a list of auxiliary 0-1 integer variables
#   [x_1, x_2, ..., x_n]
# which satisfy:
#   x_1 + x_2 + ... + x_n = 1
# that is, there is just one 1 in this list.
# For the given input integer list (which is being searched for 0s):
#   [e_1, e_2, ..., e_n]
# we require that:
#   x_1*e_1 + x_2*e_2 + ... + x_n*e_n = 0
# exercise 5: why the above constraints can guarantee that there is
# one 0 in the input list of integers?

# Let's continue to turn the above constraints into code;
def check_zero_la(l):
    # create a list of auxiliary variables:
    # [x_0, ..., x_{n-1}]
    vars = [Int('x_%d' % i) for i in range(len(l))]
    # create the first group of constraints:
    #   all "vars" are 0-1 integers:
    cons_0_or_1 = []
    for i in range(len(vars)):
        cons_0_or_1.append(Or(vars[i] == 0, vars[i] == 1))
    # create the second group of constraints:
    #   x_1 + x2 + ... + xn = 1
    cons_sum = [sum(vars) == 1]
    # create the second group of constraints:
    #   x_1*e_1 + x_2*e_2 + ... + x_n*e_n = 0
    cons_exp = []
    # exercise 6: fill in the missing code to generate the above constraint,
    # and store it in the "cons_exp" variable.
    # Make sure your code passes all the following unit test.
    # raise Todo("exercise 6: please fill in the missing code.")
    i = 0
    con_e = []
    for e in l:
        con_e.append(vars[i] * e)
        i = i + 1

    cons_exp = [sum(con_e) == 0]
    # check these constraints:
    res, model = check_cons(cons_0_or_1 + cons_sum + cons_exp)
    if res == sat:
        print(model)
        return True
    return False


# unit test the above function:
assert (not check_zero_la(l1))
assert (check_zero_la(l2))
assert (check_zero_la(l3))

# challenge: please write a program to count the number of 0s in
# a given list of integers.
# Sample inputs and outputs:
#   Input:            Output:
l1 = [1, 2, 4, 5]  # 0
l2 = [3, 0, 8, 2]  # 1
l3 = [4, 0, 3, 0]  # 2

#########################################
# None-Linear arithmetic.

# In previous sections, we've always been talking about the linear
# arithmetics, but Z3 also support the satisfiability solving on
# non-linear constraints.
# Suppose we want to check the following constraints:
#   x * x = 2
# we can write (as we can expect):
x = Real('x')
res, model = check_cons([x * x == 2])
if res == sat:
    print(model)
else:
    print(res)

# exercise 7: write some code to check that this non-linear constraint,
# on two real numbers x and y, is unsat:
#   x*x + y*y < 0
# raise Todo("exercise 7: please fill in the missing code.")
x, y = Reals('x y')
res, model = check_cons([x * x + y * y < 0])
if res == sat:
    print(model)
else:
    print(res)

#########################################
# Constraints on rational domain Q.

# One important application of the non-linear linear arithmetic
# is to reason constraints on rational domain. Recall that we
# have studied linear arithmetic both on the real domain R and
# the integer domain Z, Z3 has built-in support for these two domains.
# However, the bad news is that Z3 does not support rational domain directly.
# To overcome this difficulty, we can use a very important
# property of rational numbers: suppose x is a rational number, then
# we have:
#      x = p/q     (1)
# where both p and q are integers, and q!=0. The formulae (1) can
# be rewritten into:
#      x*q = p     (2)
# please notice that the equation (2）is also non-linear.

# Let's study one example to see how this strategy works in practice,
# consider our previous example again, if we want to check the constraint
#      x*x = 2     (3)
# on rational domain (of course, it's unsatisfiable).
# exercise 8: please fill in the missing code to check the
# satisfiability of the equation (3).
x, p, q = Ints('x p q')
# raise Todo("exercise 8: please fill in the missing code.")
res, model = check_cons([x * x == 2, x*q == p])
if res == sat:
    print(model)
else:
    print(res)

# this completes the part of the assignment.

