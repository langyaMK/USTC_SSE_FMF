import threading
import unittest
from typing import List

from z3 import *

# In this problem, you will implement the DPLL algorithm as discussed
# in the class.


# a utility class to represent the code you should fill in.
class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


########################################
# This bunch of code declare the syntax for the propositional logic, we
# repeat here:
'''
P ::= p
    | T
    | F
    | P /\ P
    | P \/ P
    | P -> P
    | ~P
'''


class Prop:
    def __repr__(self):
        return self.__str__()


class PropVar(Prop):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return self.var

    def __hash__(self):
        return hash(self.var)

    def __eq__(self, other):
        return other.__class__ == self.__class__ and self.var == other.var


class PropTrue(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "True"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropFalse(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "False"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropAnd(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} /\\ {self.right})"


class PropOr(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} \\/ {self.right})"


class PropImplies(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} -> {self.right})"


class PropNot(Prop):
    def __init__(self, p):
        self.p = p

    def __str__(self):
        return f"~{self.p}"


# we can convert the above defined syntax into Z3's representation, so
# that we can check it's validity easily:
def to_z3(prop):
    if isinstance(prop, PropVar):
        return Bool(prop.var)
    if isinstance(prop, PropImplies):
        return Implies(to_z3(prop.left), to_z3(prop.right))

    # raise Todo("Exercise 3-1: try to complete the `to_z3` method")
    if isinstance(prop, PropOr):
        return Or(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropAnd):
        return And(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropNot):
        return Not(to_z3(prop.p))
    if isinstance(prop, PropTrue):
        return True
    if isinstance(prop, PropFalse):
        return False


#####################
# TODO: please implement the nnf(), cnf() and dpll() algorithm, as discussed
# in the class.
def nnf(prop: Prop) -> Prop:
    # raise Todo("Exercise 3-2: try to implement the `nnf` method")
    if isinstance(prop, PropAnd):
        return PropAnd(nnf(prop.left), nnf(prop.right))
    if isinstance(prop, PropOr):
        return PropOr(nnf(prop.left), nnf(prop.right))
    if isinstance(prop, PropImplies):
        return PropOr(PropNot(nnf(prop.left)), nnf(prop.right))
    if isinstance(prop, PropNot):
        if isinstance(prop.p, PropVar):
            return PropNot(nnf(prop.p))
        elif isinstance(prop.p, PropOr):
            return PropAnd(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))
        elif isinstance(prop.p, PropNot):
            return nnf(prop.p.p)
        elif isinstance(prop.p, PropAnd):
            return PropOr(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))
        elif isinstance(prop.p, PropTrue):
            return PropFalse()
        elif isinstance(prop.p, PropFalse):
            return PropTrue()
        elif isinstance(prop.p, PropImplies):
            return PropAnd(nnf(prop.p.left), nnf(PropNot(prop.p.right)))
    return prop


def is_atom(nnf_prop: Prop) -> bool:
    if isinstance(nnf_prop, PropOr) or isinstance(nnf_prop, PropAnd):
        return False
    return True


def cnf(nnf_prop: Prop) -> Prop:
    def cnf_d(left: Prop, right: Prop) -> Prop:
        if isinstance(left, PropAnd):
            return PropAnd(cnf_d(left.left, right), cnf_d(left.right, right))
        elif isinstance(right, PropAnd):
            return PropAnd(cnf_d(left, right.left), cnf_d(left, right.right))
        return PropOr(left, right)

    # raise Todo("Exercise 3-3: try to implement the `cnf`and `cnf_d` method")

    if isinstance(nnf_prop, PropVar):
        return nnf_prop
    if isinstance(nnf_prop, PropAnd):
        return PropAnd(cnf(nnf_prop.left), cnf(nnf_prop.right))
    if isinstance(nnf_prop, PropOr):
        return cnf_d(nnf_prop.left, nnf_prop.right)
    if isinstance(nnf_prop, PropNot):
        return PropNot(nnf_prop.p)
    return nnf_prop


def flatten(cnf_prop: Prop) -> List[List[Prop]]:
    """Flatten CNF Propositions to nested list structure .

    The CNF Propositions generated by `cnf` method is AST.
    This method can flatten the AST to a nested list of Props.
    For example: "((~p1 \\/ ~p3) /\\ (~p1 \\/ p4))" can be
    transfer to "[[~p1, ~p3], [~p1, p4]]".

    Parameters
    ----------
    cnf_prop : Prop
        CNF Propositions generated by `cnf` method.

    Returns
    -------
    List[List[Prop]
        A nested list of Props, first level lists are connected by `And`,
        and second level lists is connected by `Or`.

    """

    def get_atom_from_disjunction(prop: Prop) -> List[Prop]:
        if is_atom(prop):
            return [prop]

        if isinstance(prop, PropOr):
            return get_atom_from_disjunction(prop.left) + get_atom_from_disjunction(prop.right)

    if isinstance(cnf_prop, PropAnd):
        return flatten(cnf_prop.left) + flatten(cnf_prop.right)
    elif isinstance(cnf_prop, PropOr):
        return [get_atom_from_disjunction(cnf_prop)]
    elif is_atom(cnf_prop):
        return [[cnf_prop]]


def unitProp(prop):  # unit prop and simplify P
    if isinstance(prop, PropTrue) or isinstance(prop, PropFalse) or isinstance(prop, PropVar):
        return prop
    if isinstance(prop, PropAnd):
        if isinstance(prop.left, PropFalse) or isinstance(prop.right, PropFalse):
            return PropFalse()
        elif isinstance(prop.left, PropTrue):
            return unitProp(prop.right)
        elif isinstance(prop.right, PropTrue):
            return unitProp(prop.left)
        else:
            return PropAnd(unitProp(prop.left), unitProp(prop.right))
    if isinstance(prop, PropOr):
        if isinstance(prop.left, PropTrue) or isinstance(prop.right, PropTrue):
            return PropTrue()
        elif isinstance(prop.left, PropFalse):
            return unitProp(prop.right)
        elif isinstance(prop.right, PropFalse):
            return unitProp(prop.left)
        else:
            return PropOr(unitProp(prop.left), unitProp(prop.right))
    if isinstance(prop, PropNot):
        if isinstance(prop.p, PropTrue):
            return PropFalse()
        if isinstance(prop.p, PropFalse):
            return PropTrue()
        else:
            return prop
    return prop


def select_atomic(prop):
    # print(prop.__class__)
    # print(prop)
    if isinstance(prop, PropVar):
        return prop
    if isinstance(prop, PropNot):
        return select_atomic(prop.p)
    if not is_atom(prop):
        if not isinstance(select_atomic(prop.left), PropTrue) \
                and not isinstance(select_atomic(prop.left), PropFalse):
            return select_atomic(prop.left)
        if not isinstance(select_atomic(prop.right), PropTrue) \
                and not isinstance(select_atomic(prop.right), PropFalse):
            return select_atomic(prop.right)
    return prop


def set_var_value(prop, var, value):
    if isinstance(prop, PropVar):
        if prop.var == var.var:
            return value
    if isinstance(prop, PropNot):
        prop.p = set_var_value(prop.p, var, value)
        if isinstance(prop.p, PropTrue):  # after set value, maybe is "PropNot(PropTrue)"
            return PropFalse()
        if isinstance(prop.p, PropFalse):
            return PropTrue()
    if isinstance(prop, PropOr):
        prop.left = set_var_value(prop.left, var, value)
        prop.right = set_var_value(prop.right, var, value)
        if isinstance(prop.left, PropTrue) or isinstance(prop.right, PropTrue):
            return PropTrue()
        if isinstance(prop.left, PropFalse):
            return prop.right
        if isinstance(prop.right, PropFalse):
            return prop.left
    if isinstance(prop, PropAnd):
        prop.left = set_var_value(prop.left, var, value)
        prop.right = set_var_value(prop.right, var, value)
        if isinstance(prop.left, PropFalse) or isinstance(prop.right, PropFalse):
            return PropFalse()
        if isinstance(prop.left, PropTrue):
            return prop.right
        if isinstance(prop.right, PropTrue):
            return prop.left
    return prop


# 对命题进行拷贝，用于回溯
def copy(prop):
    if isinstance(prop, PropVar):
        return PropVar(prop.var)
    if isinstance(prop, PropAnd):
        return PropAnd(copy(prop.left), copy(prop.right))
    if isinstance(prop, PropOr):
        return PropOr(copy(prop.left), copy(prop.right))
    if isinstance(prop, PropNot):
        return PropNot(copy(prop.p))


def dpll(prop: Prop) -> dict:
    flatten_cnf = flatten(cnf(nnf(prop)))
    print(nnf(prop))
    print(cnf(nnf(prop)))
    print(flatten_cnf)

    # implement the dpll algorithm we've discussed in the lecture
    # you can deal with flattened cnf which generated by `flatten` method for convenience,
    # or, as another choice, you can process the original cnf destructure generated by `cnf` method
    #
    # your implementation should output the result as dict like :
    # {"p1": True, "p2": False, "p3": False, "p4": True} if there is solution;
    # output "unsat" if there is no solution
    #
    # feel free to add new method.
    # raise Todo("Exercise 3-4: try to implement the `dpll` algorithm")

    result = dict()
    # 初始化字典
    for props in flatten_cnf:
        for fc_prop in props:
            if isinstance(fc_prop, PropVar):
                result[fc_prop.var] = False
            if isinstance(fc_prop, PropNot):
                result[fc_prop.p.var] = False

    def dpll1(prop: Prop, assignment: Prop) -> Prop:
        unitProp(prop)
        if isinstance(prop, PropTrue):
            return prop
        elif isinstance(prop, PropFalse):
            return prop
        p = select_atomic(prop)
        if p is None:
            return prop
        if isinstance(assignment, PropTrue):
            result[p.var] = True
        elif isinstance(assignment, PropFalse):
            result[p.var] = False

        prop = set_var_value(prop, p, assignment)
        prop_copy = copy(prop)
        # print(prop_copy)
        # print(prop)
        if isinstance(dpll1(prop, PropTrue()), PropTrue):
            return PropTrue()
        return dpll1(prop_copy, PropFalse())

    newProp = cnf(nnf(prop))
    dpll1(newProp, PropTrue())
    print(result)
    return result


#####################
# test cases:

# p -> (q -> ~p)
test_prop_1 = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))

# ~((p1 \/ ~p2) /\ (p3 \/ ~p4))
test_prop_2 = PropNot(PropAnd(
    PropOr(PropVar("p1"), PropNot(PropVar("p2"))),
    PropOr(PropVar("p3"), PropNot(PropVar("p4")))
))

N = 10
# monster_prop = PropVar('b_0')
# for i in range(1, N):
#     monster_prop = PropAnd(monster_prop, PropVar('b_{}'.format(i)))
# print(select_atomic(monster_prop))

monster_prop = PropTrue()
for i in range(N):
    monster_prop = PropAnd(monster_prop, PropVar('b_{}'.format(i)))


# feed the large proposition to your solver. you can also
# generate other propositions.
test_prop_3 = monster_prop
# print(test_prop_3)


# #####################
class TestDpll(unittest.TestCase):

    def test_to_z3_1(self):
        self.assertEqual(str(to_z3(test_prop_1)), "Implies(p, Implies(q, p))")

    def test_to_z3_2(self):
        self.assertEqual(str(to_z3(test_prop_2)), "Not(And(Or(p1, Not(p2)), Or(p3, Not(p4))))")

    def test_nnf_1(self):
        self.assertEqual(str(nnf(test_prop_1)), "(~p \\/ (~q \\/ p))")

    def test_nnf_2(self):
        self.assertEqual(str(nnf(test_prop_2)), "((~p1 /\\ p2) \\/ (~p3 /\\ p4))")

    def test_cnf_1(self):
        self.assertEqual(str(cnf(nnf(test_prop_1))), "(~p \\/ (~q \\/ p))")

    def test_cnf_2(self):
        self.assertEqual(str(cnf(nnf(test_prop_2))),
                         "(((~p1 \\/ ~p3) /\\ (~p1 \\/ p4)) /\\ ((p2 \\/ ~p3) /\\ (p2 \\/ p4)))")

    def test_cnf_flatten_1(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_1)))), "[[~p, ~q, p]]")

    def test_cnf_flatten_2(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_2)))),
                         "[[~p1, ~p3], [~p1, p4], [p2, ~p3], [p2, p4]]")

    def test_dpll_1(self):
        s = Solver()
        res = dpll(test_prop_1)
        # print(res)
        s.add(Not(Implies(res["p"], Implies(res["q"], res["p"]))))
        self.assertEqual(str(s.check()), "unsat")

    def test_dpll_2(self):
        s = Solver()
        res = dpll(test_prop_2)
        s.add(Not(Not(And(Or(res["p1"], Not(res["p2"])), Or(res["p3"], Not(res["p4"]))))))
        self.assertEqual(str(s.check()), "unsat")

    def test_dpll_3(self):
        s = Solver()
        res = dpll(test_prop_3)

        print(res)
        # monster = res["b_0"]
        # for i in range(1, N):
        #     x = str('b_{}'.format(i))
        #     monster = And(monster, res[x])

        monster = True
        for i in range(N):
            x = str('b_{}'.format(i))
            monster = And(monster, res[x])

        print(monster)
        s.add(Not(monster))
        self.assertEqual(str(s.check()), "unsat")


if __name__ == '__main__':
    unittest.main()
