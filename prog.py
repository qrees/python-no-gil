#import gc
#import time
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_SAVEALL)
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE| gc.DEBUG_UNCOLLECTABLE)

print "----------------------"
print "start of program"
i = 0
while True:
    b = {}
    a = {}
#    print "iteration:", i
    i += 1
    a['b'] = b
    b['a'] = a
#    time.sleep(0.01)

