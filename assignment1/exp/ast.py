class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


class Exp:

    def __repr__(self):
        return self.__str__()


class ExpVar(Exp):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


class ExpAdd(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} + {self.right}"


class ExpMinus(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} - {self.right}"


class ExpMulti(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} * {self.right}"


class ExpDiv(Exp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"{self.left} / {self.right}"


class ExpPar(Exp):
    def __init__(self, exp):
        self.exp = exp

    def __str__(self):
        return f"({self.exp})"


def eval_value(exp: Exp):
    if isinstance(exp, ExpVar):
        return exp.value
    if isinstance(exp, ExpAdd):
        return eval_value(exp.left) + eval_value(exp.right)
    if isinstance(exp, ExpMinus):
        return eval_value(exp.left) - eval_value(exp.right)
    if isinstance(exp, ExpDiv):
        return eval_value(exp.left) / eval_value(exp.right)
    if isinstance(exp, ExpMulti):
        return eval_value(exp.left) * eval_value(exp.right)
    if isinstance(exp, ExpPar):
        return eval_value(exp.exp)
