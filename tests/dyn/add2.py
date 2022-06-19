def add1(x):
    return x + 1

y = input_int()
g = lambda x: x - 10
f = add1 if input_int() == 0 else g   # add1 must be translate to closure
print(f(41))