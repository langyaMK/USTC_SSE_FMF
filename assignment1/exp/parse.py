from exp.lexer import *
from exp.ast import *

isp = {"#": 0, "(": 1, ")": 6, "+": 3, "-": 3, "*": 5, "/": 5}  # 定义栈内优先级
icp = {"#": 0, "(": 6, ")": 1, "+": 2, "-": 2, "*": 4, "/": 4}  # 定义栈外优先级


# 中序表达式转后序表达式
def expressToPostfix(words):
    postfix, stack = [], []
    stack.append(Word("#", 0, Sign.IllSign))
    for word in words:
        if word.sign == Sign.Number:
            postfix.append(word)
        elif isp[stack[-1].char] < icp[word.char]:
            stack.append(word)
        else:
            while isp[stack[-1].char] > icp[word.char]:
                postfix.append(stack.pop())
            if word.char == ")":
                stack.pop()
            else:
                stack.append(word)
    stack.reverse()
    stack.pop()
    postfix.extend([i for i in stack])
    return postfix


# 通过后序表达式转语法树
def postfixBuildTree(postfix):
    treeList = []
    for word in postfix:
        if word.sign == Sign.Number:
            treeList.append(ExpVar(int(word.number)))
        elif word.char == '+':
            newTreeNode = ExpAdd(treeList[-2], treeList[-1])
            treeList = treeList[:len(treeList) - 2]
            treeList.append(newTreeNode)
        elif word.char == '-':
            newTreeNode = ExpMinus(treeList[-2], treeList[-1])
            treeList = treeList[:len(treeList) - 2]
            treeList.append(newTreeNode)
        elif word.char == '*':
            newTreeNode = ExpMulti(treeList[-2], treeList[-1])
            treeList = treeList[:len(treeList) - 2]
            treeList.append(newTreeNode)
        elif word.char == '/':
            newTreeNode = ExpDiv(treeList[-2], treeList[-1])
            treeList = treeList[:len(treeList) - 2]
            treeList.append(newTreeNode)
    return treeList[0]


def parse(s):
    words = lexer(s)
    postfix = expressToPostfix(words)
    return postfixBuildTree(postfix)
