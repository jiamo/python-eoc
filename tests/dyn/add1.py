def f(x:int):
  y = 4
  f = lambda z,a,b,c,d,e,f,g : x + y + z + a + b + c + d + e + f + g
  return f
g = f(5)
h = f(3)
print(g(11, 0,0,0,0,0,0,0) + h(15, 0,0,0,0,0,0,0))