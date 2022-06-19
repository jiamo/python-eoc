from ast import *
from utils import *
from type_check_Ctup import TypeCheckCtup
import copy
from graph import UndirectedAdjList, transpose, topological_sort
from x86_ast import Jump, JumpIf


class TypeCheckCfun(TypeCheckCtup):

  def check_type_equal(self, t1, t2, e):
    if t1 == Bottom() or t2 == Bottom():
      return
    match t1:
      case FunctionType(ps1, rt1):
        match t2:
          case FunctionType(ps2, rt2):
            for (p1,p2) in zip(ps1, ps2):
              self.check_type_equal(p1, p2, e)
              self.check_type_equal(rt1, rt2, e)
          case _:
            raise Exception('error: ' + repr(t1) + ' != ' + repr(t2) \
                            + ' in ' + repr(e))
      case _:
        super().check_type_equal(t1, t2, e)
  
  def type_check_exp(self, e, env):
    match e:
      case FunRef(id, arity):
        return env[id]
      case Call(Name('input_int'), []):
        return super().type_check_exp(e, env)      
      case Call(Name('len'), [tup]):
        return super().type_check_exp(e, env)      
      case Call(func, args):
        func_t = self.type_check_exp(func, env)
        args_t = [self.type_check_exp(arg, env) for arg in args]
        match func_t:
          case FunctionType(params_t, return_t):
            for (arg_t, param_t) in zip(args_t, params_t):
                self.check_type_equal(param_t, arg_t, e)
            return return_t
          case Bottom():
            return Bottom()
          case _:
            raise Exception('type_check_exp: in call, unexpected ' + \
                            repr(func_t))
      case TailCall(func, args):
        func_t = self.type_check_exp(func, env)
        args_t = [self.type_check_exp(arg, env) for arg in args]
        match func_t:
          case FunctionType(params_t, return_t):
            for (arg_t, param_t) in zip(args_t, params_t):
                self.check_type_equal(param_t, arg_t, e)
            return return_t
          case Bottom():
            return Bottom()
          case _:
            raise Exception('type_check_exp: in call, unexpected ' + \
                            repr(func_t))
      case _:
        return super().type_check_exp(e, env)

  def type_check_def(self, d, env):
    match d:
      case FunctionDef(name, params, blocks, dl, returns, comment):
        new_env = {x: t for (x,t) in env.items()}
        for (x,t) in params:
            new_env[x] = t
        cfg = UndirectedAdjList()
        for label, body in blocks.items():
            for i in body:
                if isinstance(i, Jump) or isinstance(i, JumpIf):
                    # breakpoint()
                    cfg.add_edge(label, i.label)


        sort_cfg = topological_sort(cfg)

        while True:
            old_env = copy.deepcopy(new_env)
            for l in reversed(sort_cfg):
                ss = blocks[l]
                # should handing by top_logic.......
                # trace("handing....... {}".format(l))
                self.type_check_stmts(ss, new_env)
            # trace('type_check_Cfun iterating ' + repr(new_env))
            if new_env == old_env:
                break
        # todo check return type
        d.var_types = new_env
        # trace('type_check_Cfun var_types for ' + name)
        # trace(d.var_types)
      case _:
        raise Exception('type_check_def: unexpected ' + repr(d))

  def type_check_stmt(self, s, env):
    match s:
      case Return(value):
        self.type_check_exp(value, env)
      case TailCall(func, args):
        self.type_check_exp(Call(func, args), env)
      case _:
        super().type_check_stmt(s, env)
    
  def type_check(self, p):
    match p:
      case CProgramDefs(defs):
        env = {}
        for d in defs:
            match d:
              case FunctionDef(name, params, bod, dl, returns, comment):
                params_t = [t for (x,t) in params]
                env[name] = FunctionType(params_t, returns)
        for d in defs:
            self.type_check_def(d, env)
      case _:
        raise Exception('type_check: unexpected ' + repr(p))

