g = 3 + 4
def add(x:int,y:int,x1:int,y1:int, x2:int,y2:int, x3:int,y3:int)-> int:
    if x > 0:
        return x + y + x1 + y1 + x2 + y2 + x3 + y3
    else:
        return add(40, 2, 0, 0, 0, 0, 0, 0)


print(add(40, 2, 0, 0, 0, 0,0, 0))
x = 4