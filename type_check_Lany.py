import ast
from ast import *
from type_check_Llambda import TypeCheckLlambda
from utils import *
import typing

class TypeCheckLany(TypeCheckLlambda):

  def check_type_equal(self, t1, t2, e):
    if t1 == Bottom() or t2 == Bottom():
      return
    match t1:
      case AnyType():
        return
      case FunctionType(ps1, rt1):
        match t2:
          case FunctionType(ps2, rt2):
            for (p1, p2) in zip(ps1, ps2):
              self.check_type_equal(p1, p2, e)
              self.check_type_equal(rt1, rt2, e)
          case _:
            if isinstance(t2, AnyType):
              # t2 was AnyType we can match any
              return
            raise Exception('error: ' + repr(t1) + ' != ' + repr(t2) \
                            + ' in ' + repr(e))
      case _:
        if isinstance(t2, AnyType):
          return
        super().check_type_equal(t1, t2, e)

  def type_check_exp(self, e, env):
    match e:
      case Inject(value, typ):
        self.check_exp(value, typ, env)
        return AnyType()
      case Project(value, typ):
        self.check_exp(value, AnyType(), env)
        return typ
      case Call(Name('any_tuple_load'), [tup, index]):
        self.check_exp(tup, AnyType(), env)
        return AnyType()
      case Call(Name('any_len'), [tup]):
        self.check_exp(tup, AnyType(), env)
        return IntType()
      case Call(Name('arity'), [fun]):
        ty = self.type_check_exp(fun, env)
        match ty:
          case FunctionType(ps, rt):
            return IntType()
          case TupleType([FunctionType(ps,rs)]):
            return IntType()
          case _:
            raise Exception('type_check_exp arity unexpected ' + repr(ty))
      case Call(Name('make_any'), [value, tag]):
        self.type_check_exp(value, env)
        self.check_exp(tag, IntType(), env)
        return AnyType()
      case ValueOf(value, typ):
        self.check_exp(value, AnyType(), env)
        return typ
      case TagOf(value):
        self.check_exp(value, AnyType(), env)
        return IntType()
      case Call(Name('exit'), []):
        return Bottom()
      case AnnLambda(params, returns, body):
        new_env = {x:t for (x,t) in env.items()}
        for (x,t) in params:
            new_env[x] = t
        return_t = self.type_check_exp(body, new_env)
        self.check_type_equal(returns, return_t, e)
        return FunctionType([t for (x,t) in params], return_t)
      case Constant(value) if isinstance(value, TagOf):
        # return self.type_check_exp(value, env)
        return IntType()
      case _:
        return super().type_check_exp(e, env)

  def type_check_stmts(self, ss, env):
    if len(ss) == 0:
      return
    match ss[0]:
      case Assign([v], value) if isinstance(v, Name):
        t = self.type_check_exp(value, env)
        if v.id in env:
          self.check_type_equal(env[v.id], t, value)
        else:
          env[v.id] = t

        v.has_type = env[v.id]
        return self.type_check_stmts(ss[1:], env)
      case Expr(Call(Name('print'), [arg])):
        t = self.type_check_exp(arg, env)
        self.check_type_equal(t, AnyType(), arg)   # we make all return is AnyType now
        return self.type_check_stmts(ss[1:], env)
      case _:
        return super().type_check_stmts(ss, env)

  def check_exp(self, e, ty, env):
    match e:
      case Lambda(params, body):
        e.has_type = ty
        if isinstance(params, ast.arguments):
          new_params = [a.arg for a in params.args]
          e.args = new_params
        else:
          new_params = params
        match ty:
          case FunctionType(params_t, return_t):
            new_env = {x: t for (x, t) in env.items()}
            for (p, t) in zip(new_params, params_t):
              new_env[p] = t
            self.check_exp(body, return_t, new_env)
          case Bottom():
            pass
          case _:
            raise Exception('lambda does not have type ' + str(ty))
      case _:

        t = self.type_check_exp(e, env)
        self.check_type_equal(t, ty, e)

  #   t = self.type_check_exp(e, env)
  #   self.check_type_equal(t, ty, e)
        
  def type_check(self, p):
    #trace('*** type check Llambda')
    match p:
      case Module(body):
        env = {}
        for s in body:
            match s:
              case FunctionDef(name, params, bod, dl, returns, comment):
                if isinstance(params, ast.arguments):
                    params_t = [self.parse_type_annot(p.annotation) \
                                for p in params.args]
                    returns_t = self.parse_type_annot(returns)
                else:
                    params_t = [t for (x,t) in params]
                    returns_t = returns
                env[name] = FunctionType(params_t, returns_t)
        self.check_stmts(body, AnyType(), env)
      case _:
        raise Exception('type_check: unexpected ' + repr(p))


  def check_stmts(self, ss, return_ty, env):
    if len(ss) == 0:
      return
    #trace('*** check_stmts ' + repr(ss[0]) + '\n')
    match ss[0]:
      case FunctionDef(name, params, body, dl, returns, comment):
        #trace('*** tc_check ' + name)
        new_env = {x: t for (x,t) in env.items()}
        if isinstance(params, ast.arguments):
            new_params = [(p.arg, self.parse_type_annot(p.annotation)) for p in params.args]
            ss[0].args = new_params
            new_returns = self.parse_type_annot(returns)
            ss[0].returns = new_returns
        else:
            new_params = params
            new_returns = returns
        for (x,t) in new_params:
            new_env[x] = t
        rt = self.check_stmts(body, new_returns, new_env)
        self.check_stmts(ss[1:], return_ty, env)
      case Return(value):
        #trace('** tc_check return ' + repr(value))
        self.check_exp(value, return_ty, env)
      case Assign([v], value) if isinstance(v, Name):
        if v.id in env:
          self.check_exp(value, env[v.id], env)
        else:
           t = self.type_check_exp(value, env)
           env[v.id] = t
           if isinstance(value, Inject) and isinstance(value.typ, FunctionType):
             env[v.id] = value.typ  #
           elif isinstance(value, Call):
             if isinstance(value.args[0], AnnLambda):
               env[v.id] = value.args[0].convert_to_typ()# pass
        v.has_type = env[v.id]
        # trace(env)
        self.check_stmts(ss[1:], return_ty, env)
      case Assign([Subscript(tup, Constant(index), Store())], value):
        tup_t = self.type_check_exp(tup, env)
        match tup_t:
          case TupleType(ts):
            self.check_exp(value, ts[index], env)
          case Bottom():
            pass
          case _:
            raise Exception('check_stmts: expected a tuple, not ' \
                            + repr(tup_t))
        self.check_stmts(ss[1:], return_ty, env)
      case AnnAssign(v, ty, value, simple) if isinstance(v, Name):
        ty_annot = self.parse_type_annot(ty)
        ss[0].annotation = ty_annot
        if v.id in env:
            self.check_type_equal(env[v.id], ty_annot)
        else:
            env[v.id] = ty_annot
        v.has_type = env[v.id]
        self.check_exp(value, ty_annot, env)
        self.check_stmts(ss[1:], return_ty, env)
      case _:
        self.type_check_stmts(ss, env)
