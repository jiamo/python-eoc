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
                l_tmps.extend(r_tmps)
                return_expr = BinOp(l_expr, op, r_expr)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    l_tmps.append((tmp, return_expr))
                    return tmp, l_tmps
                else:
                    return return_expr, l_tmps
            case UnaryOp(USub(), v):
                # one by one
                v_expr, v_tmps = self.rco_exp(v, True)
                print(v_expr, v_tmps)
                return_expr = UnaryOp(USub(), v_expr)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    v_tmps.append((tmp, return_expr))
                    return tmp, v_tmps
                else:
                    return return_expr, v_tmps
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
                result.append(Expr(Call(Name('print'), [arg_expr])))
            case Expr(value):
                expr, tmps = self.rco_exp(value, False)
                print(expr, tmps)
                for name, expr in tmps:
                    result.append(Assign([name], expr))
                result.append(Expr(expr))

            case Assign([lhs], value):
                v_expr, tmps = self.rco_exp(value, False)
                print(v_expr, tmps)
                for name, t_expr in tmps:
                    result.append(Assign([name], t_expr))
                result.append(Assign([lhs], v_expr))
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(e))
        return result

    def remove_complex_operands(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        result = []
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    result.extend(self.rco_stmt(s))
                result = Module(result)
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        # breakpoint()
        trace(result)
        return result
    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        match e:
            case Name(name):
                return Variable(name)
            case Constant(value):
                return Immediate(value)
            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))

    def select_stmt(self, s: stmt) -> List[instr]:
        # YOUR CODE HERE
        result = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                arg = self.select_arg(arg)
                result.append(Instr('movq', [arg, Reg("rdi")]))
                result.append(Callq(label_name("print_int"), 1))
            case Expr(value):
                # don't need do more on value
                result.append(Instr('movq', [value, Reg("rax")]))
            case Assign([lhs], BinOp(left, Add(), right)):
                # breakpoint()
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                lhs = self.select_arg(lhs)
                if lhs == left_arg:
                    result.append(Instr('addq', [right_arg, lhs]))
                elif lhs == right_arg:
                    result.append(Instr('addq', [left_arg, lhs]))
                else:
                    result.append(Instr('movq', [left_arg, lhs]))
                    result.append(Instr('addq', [right_arg, lhs]))
            case Assign([lhs], BinOp(left, Sub(), right)):
                # breakpoint()
                left_arg = self.select_arg(left)
                right_arg = self.select_arg(right)
                lhs = self.select_arg(lhs)
                if lhs == left_arg:
                    result.append(Instr('subq', [right_arg, lhs]))
                elif lhs == right_arg:
                    result.append(Instr('subq', [left_arg, lhs]))
                else:
                    result.append(Instr('movq', [left_arg, lhs]))
                    result.append(Instr('subq', [right_arg, lhs]))
            case Assign([lhs], UnaryOp(USub(), v)):
                arg = self.select_arg(v)
                lhs = self.select_arg(lhs)
                if arg == lhs:
                    result.append(Instr('negq', [lhs]))
                else:
                    result.append(Instr('movq', [arg, lhs]))
                    result.append(Instr('negq', [lhs]))
            case Assign([lhs], Call(Name('input_int'), [])):
                lhs = self.select_arg(lhs)
                result.append(Callq(label_name("read_int"), 0))
                result.append(Instr('movq', [Reg('rax'), lhs]))
            case Assign([lhs], value):
                lhs = self.select_arg(lhs)
                arg = self.select_arg(value)
                result.append(Instr('movq', [arg, lhs]))
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        return result
        pass        

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE

        instr_body = []
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    instr_body.extend(self.select_stmt(s))
            case _:
                raise Exception('interp: unexpected ' + repr(p))


        x86 = X86Program(instr_body)
        # breakpoint()
        return x86

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

