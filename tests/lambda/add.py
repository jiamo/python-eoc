def g(z : int, x: int)-> int:
    x = 0
    y = 0
    f: Callable[[int], int] = lambda a : a + x + z
    h: Callable[[int], int] = lambda x:  x + y
    x = 10
    y = 12
    return f(y)

print(g(20, 0))