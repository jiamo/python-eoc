import ast
from ast import *
from re import T
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        # YOUR CODE HERE
        match e:
            case Name(id):
                return e, []
            case BinOp(left, op, right):
                print(left, op, right)
                l_expr, l_tmps = self.rco_exp(left, True)
                r_expr, r_tmps = self.rco_exp(right, True)
                tmp = Name(generate_name("tmp"))
                l_tmps.extend(r_tmps)
                l_tmps.append((tmp, BinOp(l_expr, op, r_expr)))
                return tmp, l_tmps
            case UnaryOp(USub(), v):
                # one by one
                v_expr, v_tmps = self.rco_exp(v, True)
                print(v_expr, v_tmps)
                tmp = Name(generate_name("tmp"))
                v_tmps.append((tmp, UnaryOp(USub(), v_expr)))
                return tmp, v_tmps
            case Constant(value):
                return e, []
            case Call(Name('input_int'), []):
                return e, []  # beachse match e was
            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))
    
    def rco_stmt(self, s: stmt) -> List[stmt]:
        # YOUR CODE HERE
        result = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                arg_expr, arg_tmps = self.rco_exp(arg, True)
                for name, expr in arg_tmps:
                    result.append(Assign([name], expr))
                result.append(Call(Name('print'), [arg_expr]))
            case Expr(value):
                expr, tmps = self.rco_exp(value, True)
                print(expr, tmps)
                for name, expr in tmps:
                    result.append(Assign([name], expr))
                result.append(Expr(expr))

            case Assign([lhs], value):
                v_expr, tmps = self.rco_exp(value, True)
                print(v_expr, tmps)
                for name, t_expr in tmps:
                    result.append(Assign([name], t_expr))
                result.append(Assign([lhs], v_expr))
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(e))
        return result

    def remove_complex_operands(self, p: Module) -> Module:
        # YOUR CODE HERE
        match p:
            case Module(body):
                print(body)
                result = Module([self.rco_stmt(s) for s in body])
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        breakpoint()
        return result
    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        pass        

    def select_stmt(self, s: stmt) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass        

    def assign_homes_instr(self, i: instr,
                           home: Dict[location, arg]) -> instr:
        # YOUR CODE HERE
        pass        

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[location, arg]) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

