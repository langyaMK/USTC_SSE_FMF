import time

from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


def four_queen():
    solver = Solver()
    # the basic data structure:
    N = 100
    board = [[Bool('b_{}_{}'.format(i, j)) for i in range(N)]
             for j in range(N)]
    # print(board[0][1])
    # constraint 1: each row has just one queen:
    rows = []
    for i in range(N):
        current_row = []
        for j in range(N):
            current_row_list = [board[i][j]]
            for k in range(N):
                if k != j:
                    current_row_list.append(Not(board[i][k]))
            current_row.append(And(current_row_list))
        rows.append(Or(current_row))
    # print(And(rows))
    solver.add(And(rows))

    # constraint 2: each column has just one queen:
    # raise Todo("Challenge: add constraints which describe each column has just one queen")
    columns = []
    for i in range(N):
        current_column = []
        for j in range(N):
            current_column_list = [board[j][i]]
            for k in range(N):
                if k != j:
                    current_column_list.append(Not(board[k][i]))
            current_column.append(And(current_column_list))
        columns.append(Or(current_column))
    # print(And(columns))
    solver.add(And(columns))

    # constraint 3: each diagonal has at most one queen:
    # raise Todo("Challenge: add constraints which describe each diagonal has at most one queen")
    diagonals = []
    for d in range(1-N, N):
        current_diagonal = []
        for i in range(N):
            j = i - d
            # print(i, j, d)
            if 0 <= j < N:
                current_diagonal_list = [board[i][j]]
                for k in range(N):
                    if k != i:
                        j = k - d
                        # print(i, j, d, k)
                        if 0 <= j < N:
                            current_diagonal_list.append(Not(board[k][j]))
                current_diagonal.append(And(current_diagonal_list))

        current_diagonal_list = []
        for i in range(N):
            j = i - d
            # print(i, j, d)
            if 0 <= j < N:
                current_diagonal_list.append(Not(board[i][j]))
        current_diagonal.append(And(current_diagonal_list))

        diagonals.append(Or(current_diagonal))
    # print(And(diagonals))
    solver.add(And(diagonals))

    # constraint 4: each anti-diagonal has at most one queen:
    # raise Todo("Challenge: add constraints which describe each anti-diagonal has at most one queen")
    anti_diagonals = []
    for d in range(0, 2*N-1):
        current_anti_diagonal = []
        for i in range(N):
            j = d - i
            # print(i, j, d)
            if 0 <= j < N:
                current_anti_diagonal_list = [board[i][j]]
                for k in range(N):
                    if k != i:
                        j = d - k
                        # print(i, j, d, k)
                        if 0 <= j < N:
                            current_anti_diagonal_list.append(Not(board[k][j]))
                current_anti_diagonal.append(And(current_anti_diagonal_list))

        current_anti_diagonal_list = []
        for i in range(N):
            j = d - i
            # print(i, j, d)
            if 0 <= j < N:
                current_anti_diagonal_list.append(Not(board[i][j]))
        current_anti_diagonal.append(And(current_anti_diagonal_list))

        anti_diagonals.append(Or(current_anti_diagonal))
    # print(And(anti_diagonals))
    solver.add(And(anti_diagonals))

    solution_count = 0

    start = time.time()
    while solver.check() == sat:
        solution_count += 1
        model = solver.model()

        # print the solution
        # print([(row_index, col_index) for row_index, row in enumerate(board)
        #        for col_index, flag in enumerate(row) if model[flag]])

        # generate constraints from solution
        solution_cons = [flag for row in board for flag in row if model[flag]]

        # add solution to the solver to get new solution
        solver.add(Not(And(solution_cons)))

    print(f"n_queen_la solve {N}-queens by {(time.time() - start):.6f}s")
    return solution_count


if __name__ == '__main__':
    # Four Queen should have 2 set of solutions
    print(four_queen())
