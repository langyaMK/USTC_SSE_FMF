import unittest

from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


# uninterrupted functions
S = Function("S", IntSort(), IntSort())
H = Function("H", IntSort(), IntSort())


# syntax of pointers
#
# T ::= x | T + E | &x | &*T | *T | NULL
# E ::= x | n | E + E | E - E | *T
# R ::= T = T | T < T | E = E | E < E
# P ::= R | ~R | P ∧ P
#
#
# Term based
class Term:
    def __repr__(self):
        return self.__str__()


# Expression based
class Expr:
    def __repr__(self):
        return self.__str__()


# Terms
class TVar(Term):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return self.name


class TAddE(Term):
    def __init__(self, term: Term, expr: Expr):
        self.term = term
        self.expr = expr

    def __str__(self):
        return f"{self.term} + ({self.expr})"


class TAddr(Term):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return f"&{self.name}"


class TAddrStar(Term):
    def __init__(self, term: Term):
        self.term = term

    def __str__(self):
        return f"&*{self.term}"


class TStar(Term):
    def __init__(self, term: Term):
        self.term = term

    def __str__(self):
        return f"*{self.term}"


class TNull(Term):
    def __str__(self):
        return "NULL"


# Expressions
class EVar(Expr):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name


class EConst(Expr):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return f"{self.value}"


class EAdd(Expr):
    def __init__(self, left: Expr, right: Expr):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} + {self.right})"


class EMinus(Expr):
    def __init__(self, left: Expr, right: Expr):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} - {self.right})"


class EStar(Expr):
    def __init__(self, term: Term):
        self.term = term

    def __str__(self):
        return f"*{self.term}"


# Relations
class Relation:
    def __repr__(self):
        return self.__str__()


class RTEq(Relation):
    def __init__(self, left: Term, right: Term):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} = {self.right})"


class RTLe(Relation):
    def __init__(self, left: Term, right: Term):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} < {self.right})"


class REEq(Relation):
    def __init__(self, left: Expr, right: Expr):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} = {self.right})"


class RELe(Relation):
    def __init__(self, left: Expr, right: Expr):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} < {self.right})"


# Formula
class Prop:
    def __repr__(self):
        return self.__str__()


class PRel(Prop):
    def __init__(self, rel: Relation):
        self.rel = rel

    def __str__(self):
        return f"{self.rel}"


class PNot(Prop):
    def __init__(self, rel: Relation):
        self.rel = rel

    def __str__(self):
        return f"~{self.rel}"


class PAnd(Prop):
    def __init__(self, left: Prop, right: Prop):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} /\\ {self.right})"


def count_stars(prop: Prop):
    # exercise 17: finish the missing code in `count_stars()` methods,
    # make it can count amount of star symbols (*) in our pointer logic .

    def term_count_stars(term: Term):
        # your code here
        # raise Todo("exercise 17: please fill in the missing code.")
        if isinstance(term, TStar) or isinstance(term, TAddrStar):
            return 1 + term_count_stars(term.term)
        if isinstance(term, TAddE):
            return term_count_stars(term.term) + expr_count_stars(term.expr)
        return 0

    def expr_count_stars(expr: Expr):
        # your code here
        # raise Todo("exercise 17: please fill in the missing code.")
        if isinstance(expr, EAdd) or isinstance(expr, EMinus):
            return expr_count_stars(expr.left) + expr_count_stars(expr.right)
        if isinstance(expr, EStar):
            return 1 + term_count_stars(expr.term)
        return 0

    def rel_count_stars(rel: Relation):
        # your code here
        # raise Todo("exercise 17: please fill in the missing code.")
        if isinstance(rel, RTEq) or isinstance(rel, RTLe):
            return term_count_stars(rel.left) + term_count_stars(rel.right)
        if isinstance(rel, REEq) or isinstance(rel, RELe):
            return expr_count_stars(rel.left) + expr_count_stars(rel.right)

    if isinstance(prop, PRel) or isinstance(prop, PNot):
        return rel_count_stars(prop.rel)
    if isinstance(prop, PAnd):
        return count_stars(prop.left) + count_stars(prop.right)


def to_z3(prop: Prop):
    # exercise 18: finish the missing code in `to_z3()` methods,
    # make it can translates pointer logic to z3's constraints.

    def term_to_z3(term: Term):
        # rules to eliminate a pointer T
        #
        # ⟦x⟧      =   H(S(x))
        # ⟦T + E⟧  =   ⟦T⟧ + ⟦E⟧
        # ⟦&x⟧     =   S(x)
        # ⟦&*T⟧    =   ⟦T⟧
        # ⟦*T⟧     =   H(⟦T⟧)
        # ⟦NULL⟧   =   0
        #
        # your code here
        # raise Todo("exercise 18: please fill in the missing code.")
        if isinstance(term, TVar):
            return H(S(Int(term.name)))
        if isinstance(term, TAddE):
            return term_to_z3(term.term) + expr_to_z3(term.expr)
        if isinstance(term, TAddr):
            return S(Int(term.name))
        if isinstance(term, TAddrStar):
            return term_to_z3(term.term)
        if isinstance(term, TStar):
            return H(term_to_z3(term.term))
        if isinstance(term, TNull):
            return 0

    def expr_to_z3(expr: Expr):
        # rules to eliminate an expression E
        #
        # ⟦n⟧      =   n
        # ⟦x⟧      =   H(S(x))
        # ⟦E + E⟧  =   ⟦E⟧ + ⟦E⟧
        # ⟦E − E⟧  =   ⟦E⟧ − ⟦E⟧
        # ⟦*T⟧     =   H(⟦T⟧)
        #
        # your code here
        # raise Todo("exercise 18: please fill in the missing code.")
        if isinstance(expr, EAdd):
            return expr_to_z3(expr.left) + expr_to_z3(expr.right)
        if isinstance(expr, EMinus):
            return expr_to_z3(expr.left) - expr_to_z3(expr.right)
        if isinstance(expr, EStar):
            return H(term_to_z3(expr.term))
        if isinstance(expr, EConst):
            return expr.value
        if isinstance(expr, EVar):
            return H(S(Int(expr.name)))

    def relation_to_z3(rel: Relation):
        # rules to eliminate a relation R
        #
        # ⟦T = T⟧   =   ⟦T⟧ = ⟦T⟧
        # ⟦T < T⟧   =   ⟦T⟧ < ⟦T⟧
        # ⟦E = E⟧   =   ⟦E⟧ = ⟦E⟧
        # ⟦E < E⟧   =   ⟦E⟧ < ⟦E⟧
        #
        # your code here
        # raise Todo("exercise 18: please fill in the missing code.")
        if isinstance(rel, RTEq):
            return term_to_z3(rel.left) == term_to_z3(rel.right)
        if isinstance(rel, RTLe):
            return term_to_z3(rel.left) < term_to_z3(rel.right)
        if isinstance(rel, REEq):
            return expr_to_z3(rel.left) == expr_to_z3(rel.right)
        if isinstance(rel, RELe):
            return expr_to_z3(rel.left) < expr_to_z3(rel.right)

    # rules to eliminate a proposition P
    #
    # ⟦R⟧      =   ⟦R⟧
    # ⟦~R⟧     =   ~⟦R⟧
    # ⟦P /\Q⟧  =   ⟦P⟧ / \ ⟦Q⟧
    #
    if isinstance(prop, PRel):
        return relation_to_z3(prop.rel)
    if isinstance(prop, PNot):
        return Not(relation_to_z3(prop.rel))
    if isinstance(prop, PAnd):
        return And(to_z3(prop.left), to_z3(prop.right))


######################
# unit test
p1 = PAnd(PRel(RTEq(TVar("p"),
                    TAddr("q"))
               ),
          PRel(REEq(EVar("q"),
                    EConst(1))
               )
          )

p2 = PRel(REEq(EStar(TVar("p")), EConst(1)))


p3 = PAnd(PRel(RTEq(TStar(TAddrStar(TVar("p"))),
                    TAddrStar(TStar(TVar("q"))))
               ),
          PRel(REEq(EStar(TStar(TStar(TVar("p")))),
                    EStar(TAddrStar(TAddE(TStar(TVar("q")), EConst(1)))))
               )
          )

# ((p = &q) /\ (q = 1)) -> (*p = 1)
print(f"{p1} -> {p2}")

# ((*&*p = &**q) /\ (***p = *&**q + (1)))
print(p3)


class TestPointer(unittest.TestCase):
    def test_count_starts(self):
        self.assertEqual((count_stars(p1)), 0)
        self.assertEqual((count_stars(p2)), 1)
        self.assertEqual((count_stars(p3)), 10)

    def test_to_z3(self):
        p = Implies(to_z3(p1), to_z3(p2))
        self.assertEqual(str(p), "Implies(And(H(S(p)) == S(q), H(S(q)) == 1), H(H(S(p))) == 1)")

        solver = Solver()
        solver.add(Not(p))
        self.assertEqual(solver.check(), unsat)


if __name__ == '__main__':
    unittest.main()
