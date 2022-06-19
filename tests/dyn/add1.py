def t(x):
  y = 10
  f = lambda z: x + y + z
  return f
g = t(10)
print(g(22))