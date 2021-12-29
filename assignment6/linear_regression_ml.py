import numpy as np
from sklearn.linear_model import LinearRegression


def sklearn_lr(xs, ys):
    reg = LinearRegression().fit(np.array(list(zip(xs, [0] * len(xs)))), ys)
    return reg.coef_[0], reg.intercept_


if __name__ == '__main__':
    sklearn_lr([1.0, 2.0, 3.0, 4.0], [1.0, 3.0, 5.0, 7.0])
