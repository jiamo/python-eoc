from ast import *
from interp_Lfun import Function
from interp_Llambda import InterpLlambda, ClosureTuple
from interp_Ldyn import Tagged
from utils import *
    
class InterpLany(InterpLlambda):

  def type_to_tag(self, typ):
      match typ:
        case FunctionType(params, rt):
          return 'function'
        case TupleType(fields):
          return 'tuple'
        case t if t == int:
          return 'int'
        case t if t == bool:
          return 'bool'
        case IntType():
          return 'int'
        case BoolType():
          return 'int'
        case _:
          raise Exception('type_to_tag unexpected ' + repr(typ))

  def arity(self, v):
    match v:
      case Tagged(val, tag):
        return super().arity(val)
      case Function(name, params, body, env):
        return len(params)
      case ClosureTuple(args, arity):
        return arity
      case _:
        raise Exception('Lany arity unexpected ' + repr(v))

  def apply_fun(self, fun, args, e):
      match fun:
        case Function(name, xs, body, env):
          # breakpoint()
          trace(f"{fun} {args=} {e} {name} {xs=} {body} {env}")
          new_env = {x: v for (x,v) in env.items()}
          for (x,arg) in zip(xs, args):
              new_env[x] = arg
          return self.interp_stmts(body, new_env)
        case Tagged(val, tag):
           #print("YYYY {}".format(v))
           return super().apply_fun(val, args, e)
        case _:
          raise Exception('apply_fun: unexpected: ' + repr(fun))

  def interp_exp(self, e, env):

    match e:
      case Inject(value, typ):
        v = self.interp_exp(value, env)
        return Tagged(v, self.type_to_tag(typ))
      case Project(value, typ):
        trace(".....{} {}".format(value, typ))
        v = self.interp_exp(value, env)
        trace("#### {}".format(v))
        match v:
          case Tagged(val, tag) if self.type_to_tag(typ) == tag:
            # print("YYYY {}".format(v))
            return val
          case _:
            raise Exception('interp project to ' + repr(typ) \
                            + '  unexpected ' + repr(v))
      case Call(Name('any_tuple_load'), [tup, index]):
        tv = self.interp_exp(tup, env)
        n = self.interp_exp(index, env)
        match tv:
          case Tagged(v, tag):
            return v[n]
          case _:
            raise Exception('interp any_tuple_load unexpected ' + repr(tv))
      case Call(Name('any_tuple_store'), [tup, index, value]):
        tv = self.interp_exp(tup, env)
        n = self.interp_exp(index, env)
        val = self.interp_exp(value, env)
        match tv:
          case Tagged(v, tag):
            v[n] = val
            return None # ??
          case _:
            raise Exception('interp any_tuple_load unexpected ' + repr(tv))
      case Call(Name('any_len'), [value]):
        v = self.interp_exp(value, env)
        match v:
          case Tagged(value, tag):
            return len(value)
          case _:
            raise Exception('interp any_len unexpected ' + repr(v))
      case Call(Name('make_any'), [value, tag]):
        v = self.interp_exp(value, env)
        t = self.interp_exp(tag, env)
        return Tagged(v, t)
      case Call(Name('arity'), [fun]):
        f = self.interp_exp(fun, env)
        return self.arity(f)
      case Call(Name('exit'), []):
        trace('exiting!')
        exit(0)
      case TagOf(value):
        v = self.interp_exp(value, env)
        match v:
          case Tagged(val, tag):
            return tag
          case _:
            raise Exception('interp TagOf unexpected ' + repr(v))
      case ValueOf(value, typ):
        v = self.interp_exp(value, env)
        match v:
          case Tagged(val, tag):
            return val
          case _:
            raise Exception('interp ValueOf unexpected ' + repr(v))
      case AnnLambda(params, returns, body):
        return Function('lambda', [x for (x,t) in params], [Return(body)], env)
      case _:
        trace("xxxx tttt {} {}".format(e, type(e)))
        return super().interp_exp(e, env)
