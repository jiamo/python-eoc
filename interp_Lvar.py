from ast import *
from utils import input_int, trace
from interp_Lint import InterpLint


class InterpLvar(InterpLint):
    def interp_exp(self, e, env):
        match e:
            case Name(id):
                # arith????
                return env[id]
                # return env[id] if id in env else getattr(self, id)
            case _:
                return super().interp_exp(e, env)

    def interp_stmts(self, ss, env):
        if len(ss) == 0:
            return
        match ss[0]:
            case Assign([lhs], value):
                trace("{}".format(ss[0]))
                env[lhs.id] = self.interp_exp(value, env)
                return self.interp_stmts(ss[1:], env)
            case _:
                return super().interp_stmts(ss, env)

    def interp(self, program):
        # breakpoint()
        match program:
            case Module(body):
                trace("interp_Lvar {}".format(body))
                self.interp_stmts(body, {})
            case _:
                raise Exception('interp: unexpected ' + repr(program))


if __name__ == "__main__":
    eight = Constant(8)
    neg_eight = UnaryOp(USub(), eight)
    read = Call(Name('input_int'), [])
    ast1_1 = BinOp(read, Add(), neg_eight)
    pr = Expr(Call(Name('print'), [ast1_1]))
    p = Module([pr])
    interp = InterpLvar()
    interp.interp_Lvar(p)
