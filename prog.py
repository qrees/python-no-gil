globals()['__lltrace__'] = 1
a = 1
print a
for k, v in globals().items():
    print k, "=", v
