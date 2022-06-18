def g(z, x):
    f = lambda a : a + x + z
    x = 10
    # y = 12
    return f

t = g(20, 0)
print(t(12))