import pdb
pdb.set_trace()

import threading

def myfunc(i):
    print "sleeping 5 sec from thread %d" % i

#for i in range(10):
t = threading.Thread(target=myfunc, args=(1,))
t.start()

