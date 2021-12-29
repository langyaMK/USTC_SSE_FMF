from z3 import *

N = 100000

prop = True

for i in range(N):
    prop = And(prop, Bool('b_{}'.format(i)))

# feed the large proposition to your solver. you can also
# generate other propositions.
print(prop)

