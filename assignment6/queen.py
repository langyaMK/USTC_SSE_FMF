"""N-queens puzzle

The  N-queens problem is about placing N chess queens on an N*N chessboard so that
no two queens threaten each other. A solution requires that no two queens share the
same row, column diagonal or anti-diagonal.The problem's target is try to find how
many solutions exist.

"""

import time
from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


def n_queen_la(board_size: int, verbose: bool = False) -> int:
    solver = Solver()
    n = board_size

    # Each position of the board is represented by a 0-1 integer variable:
    #   ...    ...    ...    ...
    #   x_2_0  x_2_1  x_2_2  ...
    #   x_1_0  x_1_1  x_1_2  ...
    #   x_0_0  x_0_1  x_0_2  ...
    #
    board = [[Int(f"x_{row}_{col}") for col in range(n)] for row in range(n)]
    # print(board)
    # only be 0 or 1 in board
    for row in board:
        for pos in row:
            solver.add(Or(pos == 0, pos == 1))

    # @exercise 11: please fill in the missing code to add
    # the following constraint into the solver:
    #   each row has just 1 queen,
    #   each column has just 1 queen,
    #   each diagonal has at most 1 queen,
    #   each anti-diagonal has at most 1 queen.
    # raise Todo("exercise 11: please fill in the missing code.")
    for row in board:
        solver.add(sum(row) == 1)  # 约束1：一行只有一个皇后
    for i in range(n):
        col = []
        for j in range(n):
            col.append(board[j][i])
        solver.add(sum(col) == 1)   # 约束2：一列只有一个皇后

    # 对角线元素放到dia数组里面
    for d in range(1 - n, n):
        dia = []
        for i in range(n):
            j = i - d
            # print(i, j, d)
            if 0 <= j < n:
                dia.append(board[i][j])
        solver.add(sum(dia) <= 1)   # 约束3：对角线最多只有一个皇后
    # 反对角线元素放到anti_dia数组里面
    for d in range(0, 2 * n - 1):
        anti_dia = []
        for i in range(n):
            j = d - i
            if 0 <= j < n:
                anti_dia.append(board[i][j])
                # current_anti_diagonal_list = [board[i][j]]
        solver.add(sum(anti_dia) <= 1)  # 约束4：反对角线最多只有一个皇后

    # count the number of solutions
    solution_count = 0

    start = time.time()
    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        if verbose:
            # print the solution
            print([(row_index, col_index) for row_index, row in enumerate(board)
                   for col_index, flag in enumerate(row) if model[flag] == 1])

        # generate constraints from solution
        solution_cons = [(flag == 1) for row in board for flag in row if model[flag] == 1]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))

    print(f"n_queen_la solve {board_size}-queens by {(time.time() - start):.6f}s")
    return solution_count


def n_queen_bt(board_size: int, verbose: bool = False) -> int:
    n = board_size
    solutions = [[]]

    def is_safe(col, solution):
        same_col = col in solution
        same_diag = any(abs(col - j) == (len(solution) - i) for i, j in enumerate(solution))

        return not (same_col or same_diag)

    start = time.time()
    for row in range(n):
        solutions = [solution + [col] for solution in solutions for col in range(n) if is_safe(col, solution)]
    print(f"n_queen_bt solve {board_size}-queens by {(time.time() - start):.6f}s")

    if verbose:
        # print the solutions
        for solution in solutions:
            print(list(enumerate(solution)))

    return len(solutions)


def n_queen_la_opt(board_size: int, verbose: bool = False) -> int:
    solver = Solver()
    n = board_size

    # We know each queen must be in a different row.
    # So, we represent each queen by a single integer: the column position
    # the q_i = j means queen in the row i and column j.
    queens = [Int(f"q_{i}") for i in range(n)]

    # each queen is in a column {0, ... 7 }
    solver.add([And(0 <= queens[i], queens[i] < n) for i in range(n)])

    # one queen per column
    solver.add([Distinct(queens)])

    # at most one for per anti-diagonal & diagonal
    solver.add([If(i == j, True, And(queens[i] - queens[j] != i - j, queens[i] - queens[j] != j - i))
                for i in range(n) for j in range(i)])

    # count the number of solutions
    solution_count = 0
    start = time.time()

    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        if verbose:
            # print the solutions
            print([(index, model[queen]) for index, queen in enumerate(queens)])

        # generate constraints from solution
        solution_cons = [(queen == model[queen]) for queen in queens]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))

    print(f"n_queen_la_opt solve {board_size}-queens by {(time.time() - start):.6f}s")

    return solution_count


if __name__ == '__main__':
    # 8-queen problem has 92 solutions
    n_queen_la(8)

    # @exercise 12: Try to compare the backtracking with the LA algorithms,
    # by changing the value of the chessboard size to other values,
    # which one is faster? What conclusion you can draw from the result?
    # raise Todo("exercise 12: please fill in the missing code.")
    # n_queen_bt(8)

    # @exercise 13: Try to compare the efficiency of n_queen_la_opt() method
    # with your n_queen_la() method.
    # What's your observation? What conclusion you can draw?
    # raise Todo("exercise 13: please fill in the missing code.")
    # n_queen_la_opt(8)

    # 三种算法解决N皇后问题效率的比较： 用回溯法最快、LA优化算法其次、LA算法最慢
