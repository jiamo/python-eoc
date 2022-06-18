

# lambda is working.....
def g(z:int, x:int)-> Callable[[int],int]:
    f: Callable[[int], int]= lambda a: a + x + z
    x = 10
    # y = 12
    return f

t = g(20, 0)
print(t(12))