import os
import time
import multiprocessing as mp
from collections import namedtuple
from datetime import datetime


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


Timer = namedtuple('Timer', ('pid', 'time'))


# exercise 4: Run the code below,  which will start two timers which record the time
# at different time intervals. It use multiprocessing.Queue which allows multiple producers
# to gather the results. You do not need to write any code in this exercise.

def timer(interval, result_queue):
    # a timer sleep interval seconds and record the datetime into result queue for 5 times
    for i in range(5):
        time.sleep(interval)
        result_queue.put(Timer(os.getpid(), str(datetime.now())), block=False)


if __name__ == '__main__':
    # Start two timers which record time with different
    # intervals, use Queue to gather the result.

    # a process shared queue
    p = mp.Queue(maxsize=10)

    # start sub-process timer with 1 second interval
    p1 = mp.Process(target=timer, args=(1, p))

    # start sub-process timer with 2 second interval
    p2 = mp.Process(target=timer, args=(2, p))

    # start the two timer
    p1.start()
    p2.start()

    # wait for the two timer finish
    p1.join()
    p2.join()

    # get the recorder from result queue
    while not p.empty():
        print(p.get())
