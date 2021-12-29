from enum import Enum
# 有限状态自动机实现词法分析

# 状态
class State(Enum):
    IniState = 0
    LeftBracketState = 1
    RightBracketState = 2
    NumState = 3
    NumSpaceState = 4
    BinSignState = 5


# 符号分类
class Sign(Enum):
    Number = 0
    BinSign = 1  # 二元运算符
    Space = 2
    LeftBracket = 3
    RightBracket = 4
    IllSign = 5


class Word:
    def __init__(self, char, number, sign):
        self.char = char
        self.number = number
        self.sign = sign

    def __str__(self):
        if self.sign == Sign.Number:
            return str(self.number)
        else:
            return str(self.char)


def JudgeSign(char):
    if char == ' ':
        return Sign.Space
    elif char == '+' or char == '-' or char == '/' or char == '*':
        return Sign.BinSign
    elif '0' <= char <= '9':
        return Sign.Number
    elif char == '(':
        return Sign.LeftBracket
    elif char == ')':
        return Sign.RightBracket
    else:
        return Sign.IllSign


# 状态是否为终结状态
def JudgeEndState(state):
    if state == State.NumState or state == State.NumSpaceState or state == State.RightBracketState:
        return True
    return False


# 更新数字字符数组
def numTempUpdate(numTemp, words):
    if len(numTemp) > 0:
        s = ""
        for i in numTemp:
            s += i
        words.append(Word(0, s, Sign.Number))
        return words, True
    return words, False


def lexer(s):
    transfer = {
        State.IniState: {
            Sign.Space: State.IniState,
            Sign.LeftBracket: State.LeftBracketState,
            Sign.Number: State.NumState,
        },
        State.LeftBracketState: {
            Sign.Space: State.LeftBracketState,
            Sign.LeftBracket: State.LeftBracketState,
            Sign.Number: State.NumState,
        },
        State.NumState: {
            Sign.Number: State.NumState,
            Sign.Space: State.NumSpaceState,
            Sign.BinSign: State.BinSignState,
            Sign.RightBracket: State.RightBracketState,
        },
        State.NumSpaceState: {
            Sign.Space: State.NumSpaceState,
            Sign.BinSign: State.BinSignState,
            Sign.RightBracket: State.RightBracketState,
        },
        State.RightBracketState: {
            Sign.Space: State.RightBracketState,
            Sign.RightBracket: State.RightBracketState,
            Sign.BinSign: State.BinSignState,
        },
        State.BinSignState: {
            Sign.Space: State.BinSignState,
            Sign.LeftBracket: State.LeftBracketState,
            Sign.Number: State.NumState,
        },
    }
    state = State.IniState
    leftBracketSize = 0  # 当前未匹配的左括号数
    numTemp = []
    words = []
    for c in s:
        sign = JudgeSign(c)
        if sign == Sign.IllSign:
            raise print("算术表达式含有非法符号!")
        elif sign == Sign.LeftBracket:
            leftBracketSize += 1
        elif sign == Sign.RightBracket:
            leftBracketSize -= 1

        if leftBracketSize < 0:
            raise print("算术表达式括号匹配错误!")
        if sign != Sign.Number:
            words, flag = numTempUpdate(numTemp, words)
            if flag:
                numTemp = []
            if sign != Sign.Space:
                words.append(Word(c, 0, sign))
        else:
            numTemp.append(c)
        flag = sign in transfer[state]
        if not flag:
            raise print("算术表达式逻辑错误!")
        # 状态转移
        state = transfer[state][sign]
    if leftBracketSize != 0:
        raise print("算术表达式括号匹配错误!")

    if JudgeEndState(state):
        words, _ = numTempUpdate(numTemp, words)
        return words
    else:
        raise print("算术表达式逻辑错误!")
