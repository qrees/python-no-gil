#import gc
#import time
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_SAVEALL)
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE| gc.DEBUG_UNCOLLECTABLE)

print "----------------------"
print "start of program"
i = 0
def fun():
    a = 1

while True:
    fun()
#    print "iteration:", i
    i += 1
#    time.sleep(0.01)

