import os
import z3
from sqlalchemy import *



class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

############################################################
# This is the symbolic execution facilities.
# E ::= s | x | Concat(E, E)
class Exp:
    pass


class ExpStrConst(Exp):
    def __init__(self, s):
        self.s = s

    def __str__(self):
        return "Const(" + self.s + ")"


class ExpStrVar(Exp):
    def __init__(self, x):
        self.x = x

    def __str__(self):
        return "Var(" + self.x + ")"


class ExpStrConcat(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return "Concat(" + (self.left.__str__()) + ", " + (self.right.__str__()) + ")"


def exp2z3(e):
    if isinstance(e, ExpStrConst):
        return z3.StringVal(e.s)
    if isinstance(e, ExpStrVar):
        return z3.String(e.x)
    if isinstance(e, ExpStrConcat):
        return z3.Concat(exp2z3(e.left), exp2z3(e.right))


############################################################
# This is the symbolic execution facilities.
class SymStr(str):
    def __new__(cls, s, sym: Exp):
        return str.__new__(cls, s)

    def __init__(self, s, sym: Exp):
        super().__init__()
        self.sym = sym

    def __add__(self, other):
        return SymStr(self.__str__() + other.__str__(), ExpStrConcat(self.sym, other.sym))


def make_sym_str(s):
    return SymStr(s, ExpStrVar(s))


############################################################
# The Database-related code.
db = None
db_exists = False


def db_create_and_init():
    global db, db_exists
    db_file = 'victim.db'
    if os.path.exists('./%s' % db_file):
        db_exists = True
    db = create_engine('sqlite:///%s' % db_file, echo=False)
    # create a new table
    if db_exists:
        return
    db.execute("""
            create table users(
                user_name char(50),
                user_age int(32),
                user_gender char(10)
            )""")
    # insert some data
    db.execute("""
    insert into users (user_name, user_age, user_gender) values('Bob', 30, 'M')
    """)
    db.execute("""
    insert into users (user_name, user_age, user_gender) values('Alice', 20, 'F')
    """)
    db.execute("""
    insert into users (user_name, user_age, user_gender) values('Carol', 40, 'F')
    """)


# exercise 12: add a possible payload to drop the table "users".
payloads = []


def check_injection(sym):
    z3exp = exp2z3(sym)
    # print(z3exp)
    solver = z3.Solver()
    cons = []
    for s in payloads:
        cons.append(z3exp == z3.StringVal(s))
    solver.add(z3.Or(cons))
    res = solver.check()
    if res == z3.sat:
        print("Found a potential SQL injection vulnerability, you may trigger it with:")
        print(solver.model())
    else:
        print(res)


def execute_wrapper(query):
    s = query.__str__()
    sym = query.sym
    check_injection(sym)
    result_proxy = db.execute(s)
    return result_proxy


def db_select(name: SymStr):
    global db
    s1 = 'select * from users where user_name = \''
    query_str = SymStr(s1, ExpStrConst(s1)) + name + SymStr('\'', ExpStrConst('\''))
    result_proxy = execute_wrapper(query_str)
    res = result_proxy.fetchall()
    if len(res) == 0:
        print("\033[31mNo this user: %s\033[0m" % name)
        result_proxy.close()
        return
    print("\033[32mFound the user: %s\033[0m" % name)
    print(res)
    result_proxy.close()


if __name__ == '__main__':
    db_create_and_init()
    while True:
        print("\nPlease input a user name: ", sep='', end='')
        name = input()
        sym = make_sym_str(name)
        print("Your searched the user: ", name)
        db_select(sym)
