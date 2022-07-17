from ast import *
from interp_Cif import InterpCif
from utils import *

class InterpCtup(InterpCif):

  def interp_exp(self, e, env):
    match e:
      case Tuple(es, Load()):
        return tuple([self.interp_exp(e, env) for e in es])
      case Subscript(tup, index, Load()):
        t = self.interp_exp(tup, env)
        n = self.interp_exp(index, env)
        return t[n]
      case Allocate(length, typ):
        array = [None] * length
        return array
      case Begin(ss, e):
        self.interp_stmts(ss, env)
        return self.interp_exp(e, env)
      case GlobalValue(name):
        return 0 # bogus
      case Call(Name('len'), [tup]):
        t = self.interp_exp(tup, env)
        return len(t)
      case _:
        return super().interp_exp(e, env)

  def interp_stmts(self, ss, env):
    if len(ss) == 0:
      return
    match ss[0]:
      case Collect(size):
        return self.interp_stmts(ss[1:], env)
      case Assign([Subscript(tup, index)], value):
        tup = self.interp_exp(tup, env)
        index = self.interp_exp(index, env)
        tup[index] = self.interp_exp(value, env)
        return self.interp_stmts(ss[1:], env)
      case _:
        return super().interp_stmts(ss, env)
