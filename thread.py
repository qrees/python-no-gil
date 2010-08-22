#pdb.set_trace()

import thread
import time

def myfunc(i):
    value = 1
    while True:
        value = value + 1
        print "%d, %d" % (i, value)
        time.sleep(0.1)

#for i in range(10):
thread.start_new_thread(myfunc, (1,))
thread.start_new_thread(myfunc, (2,))
thread.start_new_thread(myfunc, (3,))
time.sleep(10000)
