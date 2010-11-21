import timeit

repeats = 10

timer = timeit.Timer('os.system("./python prog.py")', 'import os')
timer2 = timeit.Timer('os.system("../Python-2.6.4/python prog.py")', 'import os')

print timer.timeit(repeats) / repeats
print timer2.timeit(repeats) / repeats
