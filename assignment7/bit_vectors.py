import re
import time

from z3 import *


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()

# In this part of the assignment, you'll be familiarizing
# yourself with the theory to reason about bit vectors.

# Z3 has built-in full support for bit vectors.
# To declare two bit vectors "x" and "y", we use the
# "BitVecs" class, as in:
x, y = BitVecs('x y', 2)
# this code specifies that the bit vectors are of width 2.
# We then create a solver:
solver = Solver()
# and ask whether or not the following constraint is satisfiable:
solver.add(x + y == 9)
res = solver.check()
if res == sat:
    print(solver.model())
else:
    print(res)


# exercise 1: Run the code above, what output do you get?
# Is the number "9" representable using just 2 bits? And explain
# to yourself how the modulo semantics work here. You don't
# need to write any code here.

# 9 的后两位是01 原式等价于 x+y=1


# exercise 2: In this exercise, you will write a function to
# count the number of 1 in the bit-vector.
#
# BitVecVal(1, 32)   :  1
# BitVecVal(-1, 32)  :  2
def count_one_in_bit_vector(x):
    # raise Todo("exercise 2: please fill in the missing code.")
    n = x.size()
    time = 0
    # print(type(simplify(x & 1).as_long()))
    for i in range(n):
        time += simplify(x & 1).as_long()
        x >>= 1
    return time


def check_count():
    a = BitVecVal(5, 2)
    if count_one_in_bit_vector(a) != 1:
        print("Wrong!")

    b = BitVecVal(5, 3)
    if count_one_in_bit_vector(b) != 2:
        print("Wrong!")

    c = BitVecVal(-1, 16)
    if count_one_in_bit_vector(c) != 16:
        print("Wrong!")

    d = BitVecVal(1, 16)
    if count_one_in_bit_vector(d) != 1:
        print("Wrong!")


check_count()


# Recall that in the class, we discussed a buggy
# version of the binary search algorithm, as the
# following Java code shows:

# // To search the value "target", in the input array "arr".
# // Return the index when searching succeeded, or return -1 when failed.
# int binarySearch(int[] arr, int target){
#     int low = 0;
#     int high = arr.length - 1;
#
#     while(low <= high){
#         int middle = (low + high)/2;
#
#         if(arr[middle] == target)
#             return middle;
#
#         if(arr[middle] > target)
#             high = middle - 1;
#         else
#             low = middle + 1;
#     }
#     return -1;
# }

# exercise 3: In this exercise, you're required to find
# the bug about the integer overflow in the
# Java code showing above and using z3's bit-vector to
# reproduce the bug.

# Given two bit vectors, to compute their average:
def int_average_v1(x, y):
    # raise Todo("exercise 3: please fill in the missing code.")
    return (x & y) + ((x ^ y) >> 1)


# To compute the correct result of integer average, we've
# given this correct implementation for you.
# Make sure you understand this code before continuing.
# Warned: this is a special hack, you should not copy
# this code as your implementation.
def int_average_correct(x, y):
    ex = SignExt(1, x)
    ey = SignExt(1, y)
    result_correct = (ex + ey) / 2
    return Extract(31, 0, result_correct)


# To check whether or not a given input function "f" is correct.
# Input: "f": the given function
#        "is_non_negative": whether or not the arguments should be non-negative
#                           that is x>=0 && y>=0

# Declare a variable "result" to store z3's output.
result = ''


def check_average(f, is_non_negative):
    x, y = BitVecs('x y', 32)
    result_correct = int_average_correct(x, y)
    result1 = f(x, y)
    solver = Solver()
    solver.add(result_correct != result1)

    # add extra constraints, for non-negative arguments
    if is_non_negative:
        solver.add(x >= 0, y >= 0)
    res = solver.check()

    if is_non_negative:
        sign_str = "non-negative"
    else:
        sign_str = "negative"

    if res == sat:
        print(f"\033[31mFAILED!\033[0m Found a bug with {sign_str} input in the function: {f.__name__}")
        print(solver.model())
        global result
        result = solver.model()
    else:
        print(f"\033[32mSUCCESS!\033[0m There is NO bug with {sign_str} input in the function: {f.__name__}")


# exercise 4: To check whether or not the above function is correct.
# Does Z3 complain? Why or why not?
check_average(int_average_v1, True)


# Given a Java source code which accepts two parameters provided by z3,
# that is provided by z3 after running the function check_func():
#
# public class IntAverage {
#     public static void main(String[] args) {
#         String x = args[0];
#         String y = args[1];
#
#         int_average(Integer.parseInt(x), Integer.parseInt(y));
#     }
#
#     private static int int_average(int x, int y) {
#         int z = (x + y) / 2;
#         assert z >= 0 : "Generating a integer overflow bug!";
#         return z;
#     }
# }

# Exercise 5: We build the Java source code into a Jar and provide
# a python function to automatically get the z3's output and invoke
# this Jar. Run the code, and what's your observation? What conclusion
# you can draw from this code.

def invoke_java_int_average():
    arr = re.findall("\d+", str(result))
    if not arr:
        return
    x = arr[0]
    y = arr[1]
    os.system("java -jar -ea int_average.jar " + x + " " + y)


invoke_java_int_average()


# Joshua J. Bloch proposed the following solution to solve integer overflow problem：
def int_average_v2(x, y):
    return x + (y - x) / 2


# exercise 6: To check whether or not the above function is correct.
# Does Z3 complain? Why or why not?
check_average(int_average_v2, False)
# 当x和y异号时，可能发生溢出


# Joshua J. Bloch proposed a second solution to solve integer
# overflow problem:
#  (x+y) >>> 1
#
# exercise 7: Complete the missing part to implement it.
def int_average_v3(x, y):
    # raise Todo("exercise 7: please fill in the missing code.")
    return LShR(x+y, 1)


check_average(int_average_v3, False)


# exercise 8: To check whether or not the above function is correct.
# Does Z3 complain? Why or why not?
check_average(int_average_v3, True)


# exercise 9: To compute the average of two arbitrary
# integers (negative or non-negative). We've give you a correct
# implementation of the integer average, you can read it
# for some idea, but you must write you own code,
# and don't copy the version we provide.

# Hint 1: this exercise is harder than you may imagine, you may want to
# search online for the correct implementation of average on fix-width
# integers. For instance, you can refer to the
# Hacker's Delight book (page 9, section 2.5) by Henry S. Warren
# (this is a very good book containing many delighting programming tricks).
def int_average(x, y):
    # raise Todo("exercise 9: please fill in the missing code.")
    t = (x & y) + ((x ^ y) >> 1)
    return t + (LShR(t, 31) & (x ^ y))


check_average(int_average, False)
check_average(int_average, True)


# Integer overflows are a notorious source of bugs and are very difficult to
# debug. Read the following C code:
#
# int myfunction(int * array, int len){
#       int * myarray, i;
#
#       myarray = malloc(len * sizeof(int)); / *[1] * /
#       if (myarray == NULL)
#       {
#           return -1;
#       }
#
#       for (i = 0; i < len; i++){ / * [2] * /
#           myarray[i] = array[i];
#       }
#
#       return myarray;
#   }


# exercise 10: Read the assigned code, to understand how we can use
# Z3 to justify the existence of overflows. You don't need
# to write any code in this exercise.
def multi_overflow():
    x, y = BitVecs('x y', 32)
    solver = Solver()
    solver.add(x >= 1, y == 4, x * y < 0)
    res = solver.check()
    if res == sat:
        print('found an poc for integer overflow: ', solver.model())
    else:
        print('success!')


multi_overflow()
# 可能发生两个整数相乘结果溢出为负的情况

# exercise 11: Given two bit vectors, computer their multiplication,
# return two value: an overflow flag, and the result (after rounding).
# For instance, for x=1, y=2, return (False, 2).
# for x=0x80000000, y=2, return (True, 0)

def detect_multi_overflow(x, y):
    # raise Todo("exercise 11: please fill in the missing code.")
    # print(type(simplify(BVMulNoOverflow(x, y, signed=True))))
    # print(not simplify(BVMulNoOverflow(x, y, signed=True)))
    # print(simplify(x * y))
    return not simplify(BVMulNoOverflow(x, y, signed=True)), simplify(x * y)


def check_multi():
    # some unit tests
    x = BitVecVal(1, 32)
    y = BitVecVal(2, 32)
    is_overflow, res = detect_multi_overflow(x, y)
    if not ((not is_overflow) and res == 2):
        print("Wrong!")
    else:
        print("multi_with_overflow pass test case 1")

    x = BitVecVal(0x80000000, 32)
    y = BitVecVal(2, 32)
    is_overflow, res = detect_multi_overflow(x, y)
    if not (is_overflow and res == 0):
        print("Wrong!")
    else:
        print("multi_with_overflow pass test case 2")


check_multi()


# We given an example for the special case of Fermat's Last Theorem when n==2,
# that is, we ask Z3 to show that x*x+y*y=z*z does have solutions.
def fermat_2(x, y, z):
    cons = []
    cons.append(x & 0xffffff00 == 0)
    cons.append(y & 0xffffff00 == 0)
    cons.append(z & 0xffffff00 == 0)
    cons.append(x != 0)
    cons.append(y != 0)
    cons.append(z != 0)
    cons.append(x * x + y * y == z * z)
    return cons


# Fermat's last theorem:
# exercise 12: write a function for arbitrary n:
def fermat(x, y, z, n):
    # raise Todo("exercise 12: please fill in the missing code.")
    cons = []
    cons.append(x & 0xfffffc00 == 0)
    cons.append(y & 0xfffffc00 == 0)
    cons.append(z & 0xfffffc00 == 0)
    cons.append(x != 0)
    cons.append(y != 0)
    cons.append(z != 0)
    xx , yy, zz = x, y, z
    for i in range(n-1):
        xx *= x
        yy *= y
        zz *= z
    cons.append(xx + yy == zz)
    return cons

def check_fermat():
    # check for n = 2
    x, y, z = BitVecs('x y z', 32)
    solver = Solver()
    solver.add(fermat_2(x, y, z))
    res = solver.check()
    if res == sat:
        print(f"When n = 2, Fermat's Last Theorem does NOT held: {solver.model()}")
    else:
        print("When n = 2, Fermat's Last Theorem does held")

    # check for n == 3
    n = 3
    solver = Solver()
    solver.add(fermat(x, y, z, n))
    start = time.time()
    res = solver.check()
    end = time.time()
    print('时间：', end-start, 's')
    if res == sat:
        print(f"When n = {n}, found a counter example, Fermat's Last Theorem does NOT held: {solver.model()}")
    else:
        print("We are more confident that Fermat's Last Theorem does held, although we don't have a rigorous proof yet")


check_fermat()
