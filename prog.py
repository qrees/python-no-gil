#import gc
#import time
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_SAVEALL)
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE| gc.DEBUG_UNCOLLECTABLE)

i = 0
def fun():
    a = 1

while i < 1000000:
    fun()
    i += 1

