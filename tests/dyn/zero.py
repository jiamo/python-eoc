def tail_sum(n, s):
    if n == 0:
        return s
    else:
        return tail_sum(n-1, n+s)

print(tail_sum(3, 0) + 36)