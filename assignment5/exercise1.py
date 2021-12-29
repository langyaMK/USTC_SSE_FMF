from z3 import *

# Before we presenting the EUF theory, we first introduce some Z3's
# facilities to define terms and functions.

########################################
# Sort, term, formula

# In Z3, we can define sorts, we can simply think them as sets.
# This code declares a new sort (although abstract) called S.:
S = DeclareSort('S')

# The sort can contain constants:
e = Const('e', S)

# Z3 has some builtin sort:
# Bool, Int, Real, BitVec n, Array, Index, Elem, String, Seq S.
# which can be used directly.

# We can define functions:
f = Function('f', S, S)
g = Function('g', S, S, S)
# this is a unary function from sort S to sort S.
# we can solve the congruence rule:
# e is a constant from S.

# And e has some intrinsic property, for example, the reflexivity.
# Hence, the following proposition is unsat:
solve(e != e)

# the following propositions have solution:
solve(e == f(e))
solve(e == f(g(e, e)))

# the example from the lecture:
x1, x2, x3, x4, x5 = Consts('x1 x2 x3 x4 x5', S)
solve(x1 == x2, x2 == x3, x4 == x5, x5 != x1, f(x1) != f(x3))
# with the result "no solution".

# If we change the inequality to equality:
solve(x1 == x2, x2 == x3, x4 == x5, x5 != x1, f(x1) == f(x3))
# this will give the following solution:
'''
[x3 = S!val!1,
 x5 = S!val!0,
 x4 = S!val!0,
 x1 = S!val!1,
 x2 = S!val!1]
'''
# note that S!val!0, S!val!1 are distinct values.

# Let's study the translation validation we presented in the lecture:
x1, x2, y1, y2, t1, t2, z = Consts('x1 x2 y1 y2 t1 t2 z', S)
f = Function('f', S, S, S)
g = Function('g', S, S, S)
F1 = And(t1 == f(x1, y1), t2 == f(x2, y2), z == g(t1, t2))
F2 = And(z == g(f(x1, y1), f(x2, y2)))
F = Implies(F1, F2)
solve(Not(F))
solve(F)

# Let's try another example
# This code:
f = Function('f', S, S)
x1, x2, x3, x4, x5 = Consts('x1 x2 x3 x4 x5', S)
solve(x1 == x2, x2 == x3, x4 == x5, x5 != x1, f(x1) != f(x3))
# what's Z3's output? And why that output?