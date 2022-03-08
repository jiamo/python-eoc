import ast
from ast import *
from re import T
from utils import *
from x86_ast import *
import os
from graph import UndirectedAdjList
from priority_queue import PriorityQueue
from typing import List, Tuple, Set, Dict
from interp_x86.eval_x86 import interp_x86

Binding = Tuple[Name, expr]
Temporaries = List[Binding]

caller_saved_regs = {Reg('rax'), Reg('rcx'), Reg('rdx'), Reg('rsi'),Reg('rdi'),Reg('r8'),Reg('r9'),
                    Reg("r10"), Reg('r11')}
callee_saved_regs = {Reg('rsp'), Reg('rbp'), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"),Reg("r15")}
arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]



class Compiler:

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def shrink_exp(self, e: expr) -> expr:
        # YOUR CODE HERE
        # breakpoint()
        match e:
            case BoolOp(And(), expr):
                return IfExp(expr[0], expr[1], Constant(False))
            case BoolOp(Or(), expr):
                return IfExp(expr[0], Constant(True), expr[1])
            case _:
                return e
            # case Name(id):
            #     return e, []
            # case BinOp(left, op, right):
            #     print(left, op, right)
            #     l_expr, l_tmps = self.rco_exp(left, True)
            #     r_expr, r_tmps = self.rco_exp(right, True)
            #     l_tmps.extend(r_tmps)
            #     return_expr = BinOp(l_expr, op, r_expr)
            #     if need_atomic:
            #         tmp = Name(generate_name("tmp"))
            #         l_tmps.append((tmp, return_expr))
            #         return tmp, l_tmps
            #     else:
            #         return return_expr, l_tmps
            # case UnaryOp(USub(), v):
            #     # one by one
            #     v_expr, v_tmps = self.rco_exp(v, True)
            #     print(v_expr, v_tmps)
            #     return_expr = UnaryOp(USub(), v_expr)
            #     if need_atomic:
            #         tmp = Name(generate_name("tmp"))
            #         v_tmps.append((tmp, return_expr))
            #         return tmp, v_tmps
            #     else:
            #         return return_expr, v_tmps
            # case Constant(value):
            #     return e, []
            # case Call(Name('input_int'), []):
            #     return e, []  # beachse match e was
            # case _:
            #     raise Exception('error in rco_exp, unexpected ' + repr(e))

    def shrink_stmt(self, s: stmt) -> stmt:
        # YOUR CODE HERE
        match s:
            case Expr(Call(Name('print'), [arg])):
                arg_expr = self.shrink_exp(arg)
                result = Expr(Call(Name('print'), [arg_expr]))
            case Expr(value):
                s_value = self.shrink_exp(value)
                result= Expr(s_value)
            case Assign([lhs], value):
                s_value = self.shrink_exp(value)
                result = Assign([lhs], s_value)
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        return result

    def shrink(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        result = []
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    result.append(self.shrink_stmt(s))
                result = Module(result)
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        # breakpoint()
        trace(result)
        return result


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
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
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
        # print("......")
        # interp_x86(x86)
        # print("......")
        return x86

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Variable(name):
                if a in home:
                    return home[a]
                index = len(home) + 1
                location = -(index * 8)
                arg = Deref("rbp", location)
                home[a] = arg
                return arg
            case Immediate(value):
                return a
            case Reg(value):
                return a
            case _:
                raise Exception('error in assign_homes_arg, unexpected ' + repr(a))
        pass        

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match(i):
            case Instr(instr, args):
                new_args = []
                for arg in args:
                    new_args.append(self.assign_homes_arg(arg, home))
                return Instr(instr, new_args)
            case Callq(func, num_args):
                return i
            case _:
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
        pass        

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        result = []
        for s in ss:
            ns = self.assign_homes_instr(s, home)
            result.append(ns)
        return result

    # def assign_homes(self, p: X86Program) -> X86Program:
    #     # YOUR CODE HERE
    #     match(p):
    #         case X86Program(body):
    #             home = {}
    #             result = self.assign_homes_instrs(body, home)
    #     # breakpoint()
    #     return X86Program(result)

    def read_var(self, i: instr) -> Set[location]:
        match (i):
            case Instr(op, [Variable(s), t]):
                return {i.args[0]}
            case Instr(op, [Reg(s), t]):
                return {i.args[0]}
            case Instr(op, [Variable(s)]):
                return {i.args[0]}
            case Instr(op, [Reg(s)]):
                return {i.args[0]}
            case Callq(func, num_args):
                return set(arg_regs[:num_args])
            case _:
                return set()

    def write_var(self, i) -> Set[location]:
        match (i):
            case Instr("movq", [s, t]):
                return {i.args[1]}
            case Callq(func, num_args):
                return set(callee_saved_regs)
            case _:
                return set()

    def uncover_live(self, ss: List[instr]) -> Dict[instr, Set[location]]:

        pre_instr_set = set()
        pre_instr = ss[-1]
        live_after = {
            ss[-1]: set()
        }
        for s in list(reversed(ss))[1:]:
            pre_instr_set = (pre_instr_set - self.write_var(pre_instr)).union(self.read_var(pre_instr))
            pre_instr = s
            live_after[s] = pre_instr_set

        return live_after


    def build_interference(self, ss: List[instr]) -> UndirectedAdjList:
        live_after = self.uncover_live(ss)
        interference_graph = UndirectedAdjList()
        print("live_after ", live_after)
        for s in ss:
            match (s):
                case Instr("movq", [si, d]):
                    # si = s.args[0]
                    for v in live_after[s]:
                        if v != d and v != si:
                            interference_graph.add_edge(d, v)
                # case Instr("movq", [Reg(x), t]):
                #     si = s.args[0]
                #     for v in live_after[si]:
                #         if v != d and v != si:
                #             interference_graph.add_edge(d, v)
                case _:
                    wset = self.write_var(s)
                    for d in wset:
                        for v in live_after[s]:
                            if v != d:
                                interference_graph.add_edge(d, v)
        return interference_graph

    def color_graph(self, ss: List[instr], k=100) -> Dict[location, int]:
        # first make it k big enough
        valid_colors = list(range(0, k))  # number of colar
        color_map = {}
        saturated = {}

        def less(u, v):
            nonlocal saturated
            # breakpoint()
            if v not in saturated:
                return True
            return len(saturated[u]) < len(saturated[v])

        queue = PriorityQueue(less)
        interference_graph = self.build_interference(ss)
        # dot = interference_graph.show()
        # breakpoint()
        # dot.view()
        # breakpoint()
        vsets = interference_graph.vertices()
        for v in vsets:
            saturated[v] = set()
        for v in vsets:
            queue.push(v)

        while not queue.empty():

            u = queue.pop()
            print("handing", u)
            adj_colors = {color_map[v] for v in interference_graph.adjacent(u) if v in color_map}
            print(u, adj_colors)
            if left_color := set(valid_colors) - adj_colors:
                color = min(left_color)
                color_map[u] = color
                for v in interference_graph.adjacent(u):
                    saturated[v].add(color)
            # else:
            #     spill.add(u)
        # breakpoint()
        return color_map

    def allocate_registers(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        result = []
        self.color_regs = [Reg("rbx"), Reg("rcx"), Reg("rdx"), Reg("rsi"), Reg("rdi"), Reg("r8"), Reg("r9"), Reg("r10")]
        self.color_regs = [Reg("rbx"), Reg("rcx")]
        self.color_regs = [Reg("rbx")]
        self.color_regs = [Reg("rcx")]

        self.alloc_callee_saved_regs = list(set(self.color_regs).intersection(callee_saved_regs))
        self.C = len(self.alloc_callee_saved_regs)
        # used_regs = 1
        color_regs_map = {i:reg for i, reg in enumerate(self.color_regs)}
        self.real_color_map = {}

        match(p):
            case X86Program(body):
                color_map = self.color_graph(body)
                self.S = len(set(color_map.values())) - len(self.color_regs)

                print("color_map", color_map)

                for color in sorted(set(color_map.values())):
                    if color in self.real_color_map:
                        continue
                    if color in color_regs_map:
                        self.real_color_map[color] = color_regs_map[color]
                    else:
                        # Yes
                        self.real_color_map[color] = Deref("rbp", -8*(color-len(self.color_regs) + self.C + 1))

                print("real_color_map", self.real_color_map)

                for s in body:
                    match(s):
                        case Instr(op, [source, target]):
                            if (color := color_map.get(source)) is not None:
                                source = self.real_color_map[color]
                            if (color := color_map.get(target)) is not None:
                                target = self.real_color_map[color]
                            result.append(Instr(op, [source, target]))
                        case Instr(op, [source]):
                            if (color := color_map.get(source)) is not None:
                                source = self.real_color_map[color]
                            result.append(Instr(op, [source]))
                        case _:
                            result.append(s)

        # breakpoint()
        # breakpoint()

        self.rsp_sub = align(8 * self.S + 8 * self.C, 16) - 8 * self.C

        return X86Program(result)



    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match(i):
            case Instr(instr, [x, y]) if x == y:
                return []
            case Instr(instr, [Deref("rbp", x), Deref("rbp", y)]):
                return [
                    Instr("movq", [Deref("rbp", x), Reg("rax")]),
                    Instr("movq", [Reg("rax"), Deref("rbp", y)])
                ]
            case Instr(instr, args):
                return [i]
            case Callq(func, num_args):
                return [i]
            case _:
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
        pass        

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        result = []
        for s in ss:
            ns = self.patch_instr(s)
            result.extend(ns)
        return result

    def patch_instructions(self, p: X86Program) -> X86Program:
        match(p):
            case X86Program(body):
                result = self.patch_instrs(body)
        # breakpoint()
        return X86Program(result)

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        result = []


        # The spilled variables must b placed lower on the stackthan the saved callee
        # because there is rsp betweent it
        extra_saved_regs = list(set(self.alloc_callee_saved_regs) - {Reg("rbp")})
        # breakpoint()
        match (p):
            case X86Program(body):
                result.extend([
                    Instr("pushq", [Reg("rbp")]),
                    Instr("movq", [Reg("rsp"), Reg("rbp")]),

                ])
                # save
                for reg in extra_saved_regs:
                    result.append(Instr("pushq", [reg]))
                result.extend([ Instr("subq", [Immediate(self.rsp_sub), Reg("rsp")])])

                result.extend(body)
                result.extend([ Instr("addq", [Immediate(self.rsp_sub), Reg("rsp")]),])

                # recover
                for reg in extra_saved_regs[::-1]:
                    result.append(Instr("popq", [reg]))

                result.extend([
                    Instr("popq", [Reg("rbp")]),
                    Instr("retq", []),
                ])


        # breakpoint()
        return X86Program(result)

