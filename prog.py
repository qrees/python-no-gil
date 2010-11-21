#import gc
#import time
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_SAVEALL)
#gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE| gc.DEBUG_UNCOLLECTABLE)

i = 0
while i < 10000000:
    i += 1
    a = []
    del a
