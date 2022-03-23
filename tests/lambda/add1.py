def f(x:int)-> Callable[[int],int] :
  y = 4
  f: Callable[[int], int] = lambda z : x + y + z
  return f
g = f(5)
h = f(3)
print(g(11) + h(15))