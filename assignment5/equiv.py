from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


# program equivalence:
# in the class, we present two implementation of the same algorithms, one
# is:
'''
int power3(int in){
  int i, out_a;
  out_a = in;
  for(i = 0; i < 2; i++)
    out_a = out_a * in;
  return out_a;
}
'''
# and the other one is:
'''
int power3_new(int in){
  int out_b;
  out_b = (in*in)*in;
  return out_b;
}

'''
# and with EUF, we can prove that these two algorithms are equivalent,
# that is:
# P1/\P2 -> out_a==out_b

# Please construct, manually, the propositions P1 and P2, and let Z3
# prove the above implication. (Note that you don't need to generate
# P1 or P2 automatically, just write down them manually.)

# raise Todo("Exercise 2: try to prove the algorithm 'power3' and 'power3_new' "
#            "are equivalent by using EUF theory")
S = DeclareSort('S')

_in, out_a_0, out_a_1, out_a_2, out_b = Consts('_in out_a_0 out_a_1 out_a_2 out_b', S)

f = Function('f', S, S, S)

P1 = And(out_a_0 == _in, out_a_1 == f(out_a_0, _in), out_a_2 == f(out_a_1, _in))
P2 = And(out_b == f(f(_in, _in), _in))

F = Implies(And(P1, P2), out_a_2 == out_b)

solve(Not(F))
