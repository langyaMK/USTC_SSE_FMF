""" The subset problem

The subset problem is a well-known satisfiability problem: given
a multiset (a multiset is like a normal set, expect for the
elements can be duplicated) S, whether or not there is a
non-empty subset T of S, such that:
  \sum T = 0

For example, given this set
  {-7, -3, -2, 9000, 5, 8}
the answer is yes because the subset
  {-3, -2, 5}
sums to zero.

This problem is NPC, and for more background information of the
subset problem, please refer to:
https://en.wikipedia.org/wiki/Subset_sum_problem

"""

from z3 import *
import time


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()



# LA-based solution
def subset_sum_la(target_set: list):
    solver = Solver()
    flags = [Int(f"x_{i}") for i in range(len(target_set))]

    # 0-1 ILA
    for flag in flags:
        solver.add(Or(flag == 0, flag == 1))

    # the selected set must be non-empty
    solver.add(sum(flags) != 0)

    # @exercise 9: please fill in the missing code to add
    # the following constraint into the solver.
    #       \sum_i flags[i]*target_set[i] = 0
    # raise Todo("exercise 9: please fill in the missing code.")
    i = 0
    con = []
    for t in target_set:
        con.append(t * flags[i])
        i = i + 1
    solver.add(sum(con) == 0)

    start = time.time()
    result = solver.check()
    print(f"time used in LA: {(time.time() - start):.6f}s")
    if result == sat:
        return True, [target_set[index] for index, flag in enumerate(flags) if solver.model()[flag] == 1]
    return False, result


# LA-based optimized solution
def subset_sum_la_opt(target_set: list):
    solver = Solver()

    # enable Pseudo-Boolean solver
    # to get more information about Pseudo-Boolean constraints
    # refer to https://theory.stanford.edu/~nikolaj/programmingz3.html
    solver.set("sat.pb.solver", "solver")

    # use Pseudo-Boolean constraints for each flag
    flags = [Bool(f"x_{i}") for i in range(len(target_set))]
    #solver.add(AtLeast(flags + [1]))
    # the selected set must be non-empty
    solver.add(PbGe([(flags[i], 1) for i in range(len(target_set))], 1))

    # selected set must sum to zero
    solver.add(PbEq([(flags[i], target_set[i]) for i in range(len(target_set))], 0))

    start = time.time()
    result = solver.check()
    print(f"time used in LA optimized: {(time.time() - start):.6f}s")

    if result == sat:
        return True, [target_set[index] for index, flag in enumerate(flags) if solver.model()[flag]]
    return False, result


# dynamic programming-based (DP) solution (don't confuse DP with LP):
def subset_sum_dp(target_set):
    def subset_sum_dp_do(the_set, target, index) -> Bool:
        if index == 0:
            return False
        if target == the_set[index - 1]:
            return True
        if subset_sum_dp_do(the_set, target, index - 1):
            return True
        return subset_sum_dp_do(the_set, target - the_set[index - 1], index - 1)

    start = time.time()
    result = subset_sum_dp_do(target_set, 0, len(target_set))
    print(f"time used in DP: {(time.time() - start):.6f}s")
    return result


def gen_large_test(n):
    nums = [10000] * n
    nums[len(nums) - 2] = 1
    nums[len(nums) - 1] = -1
    # print(nums)
    return nums


if __name__ == '__main__':
    # a small test case
    small_set = [-7, -3, -2, 9000, 5, 8]
    subset_sum_dp(small_set)
    print(subset_sum_la(small_set))
    print(subset_sum_la_opt(small_set))

    # a large test case
    max_nums = 20
    large_set = gen_large_test(max_nums)

    # @exercise 10: compare the efficiency of the DP and the
    # LP algorithm, by changing the value of "max_nums" to other
    # values, say, 200, 2000, 20000, 200000, ...
    # what's your observation? What conclusion you can draw from these data?
    # raise Todo("exercise 10: please fill in the missing code.")
    print(subset_sum_la(large_set))
    print(subset_sum_la_opt(large_set))
    print(subset_sum_dp(large_set))
