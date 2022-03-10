import ast
from ast import *
from re import T
from utils import *
from x86_ast import *
from collections import deque
from functools import reduce
import os
from graph import UndirectedAdjList, transpose, topological_sort
from priority_queue import PriorityQueue
import interp_Cif
from typing import List, Tuple, Set, Dict
from interp_x86.eval_x86 import interp_x86

Binding = Tuple[Name, expr]
Temporaries = List[Binding]

caller_saved_regs = {Reg('rax'), Reg('rcx'), Reg('rdx'), Reg('rsi'),Reg('rdi'),Reg('r8'),Reg('r9'),
                    Reg("r10"), Reg('r11')}
callee_saved_regs = {Reg('rsp'), Reg('rbp'), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"),Reg("r15")}
arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]
op_dict = {
    "==": "e",
    "<=": "le",
    "<": "l",
    ">=": "ge",
    ">": "g",
    "!=": "ne",
}


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
            case If(test, body, orelse):
                test_expr = self.shrink_exp(test)
                body = [self.shrink_stmt(s) for s in body]
                orelse =  [self.shrink_stmt(s) for s in orelse]
                result = If(test_expr, body, orelse)
            case While(test, body, []):
                test_expr = self.shrink_exp(test)
                body = [self.shrink_stmt(s) for s in body]
                result = While(test_expr, body, [])
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
            case UnaryOp(op, v):
                # one by one
                v_expr, v_tmps = self.rco_exp(v, True)
                print(v_expr, v_tmps)
                return_expr = UnaryOp(op, v_expr)
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
            case Compare(left, [cmp], [right]):
                left_expr, left_tmps = self.rco_exp(left, True)
                right_expr, right_tmps = self.rco_exp(right, True)
                left_tmps.extend(right_tmps)
                return_expr = Compare(left_expr, [cmp], [right_expr])
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    left_tmps.append((tmp, return_expr))
                    return tmp, left_tmps
                else:
                    return return_expr, left_tmps

            case IfExp(expr_test, expr_body, expr_orelse):
                test_expr, test_tmps = self.rco_exp(expr_test, False)
                body, body_tmps = self.rco_exp(expr_body, False)
                orelse_expr, orelse_tmp = self.rco_exp(expr_orelse, False)

                wrap_body = Begin([ Assign([name], expr)for name,expr in body_tmps], body)
                wrap_orelse = Begin([Assign([name], expr) for name, expr in orelse_tmp], orelse_expr)
                return_expr = IfExp(test_expr, wrap_body, wrap_orelse)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    test_tmps.append((tmp, return_expr))
                    return tmp, test_tmps
                else:
                    return return_expr, test_tmps

            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))
    
    def rco_stmt(self, s: stmt) -> List[stmt]:
        # YOUR CODE HERE
        result = []
        # breakpoint()
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
            case If(test, body, orelse):
                test_expr, test_tmps = self.rco_exp(test, False)
                body_stmts = []
                for name, t_expr in test_tmps:
                    result.append(Assign([name], t_expr))
                for s in body:
                    body_stmts.extend(self.rco_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.extend(self.rco_stmt(s))
                result.append(If(test_expr, body_stmts, orelse_stmts))
            case While(test, body, []):
                test_expr, test_tmps = self.rco_exp(test, False)
                body_stmts = []
                for name, t_expr in test_tmps:
                    result.append(Assign([name], t_expr))
                for s in body:
                    body_stmts.extend(self.rco_stmt(s))
                result.append(While(test_expr, body_stmts, []))
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


    def explicate_assign(self, rhs: expr, lhs: Variable, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                goto_cont = create_block(cont, basic_blocks)
                body_list = self.explicate_assign(body, lhs, [goto_cont], basic_blocks)
                orelse_list = self.explicate_assign(orelse, lhs, [goto_cont], basic_blocks)
                return self.explicate_pred(test, body_list, orelse_list, basic_blocks)

            case Begin(body, result):
                print("yyyy")
                new_body = [Assign([lhs], result)] + cont
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body
            case _:
                if str(lhs.id) == 'tmp.0':
                    print("xxxx")
                return [Assign([lhs], rhs)] + cont


    def explicate_effect(self, e: expr, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case IfExp(test, body, orelse):
                goto_cont = create_block(cont, basic_blocks)
                body = self.explicate_effect(body, [goto_cont], basic_blocks)
                orelse = self.explicate_effect(orelse, [goto_cont], basic_blocks)
                return self.explicate_pred(test, body, orelse, basic_blocks)
            case Call(func, args):
                print("#####", e)
                return [Expr(e)] + cont
            case Begin(body, result):
                new_body = self.explicate_effect(result, cont, basic_blocks) + [cont]
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body
            case _:
                print("......", e)
                return []

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Compare(left, [op], [right]):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                return [If(cnd, [goto_thn], [goto_els])]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case IfExp(test, body, orelse):
                # TODO

                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                body = self.explicate_pred(body, [goto_thn], [goto_els], basic_blocks)
                orelse = self.explicate_pred(orelse, [goto_thn], [goto_els], basic_blocks)
                goto_thn_out = create_block(body, basic_blocks)
                goto_els_out = create_block(orelse, basic_blocks)
                return [If(test, [goto_thn_out], [goto_els_out])]

            case Begin(body, result):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                new_body = [If(result, [goto_thn], [goto_els])]
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body
            case _:
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                        [create_block(els, basic_blocks)],
                        [create_block(thn, basic_blocks)])]


    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                goto_cont = create_block(cont, basic_blocks)
                new_body = [goto_cont]
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)

                new_orelse = [goto_cont]
                for s in reversed(orelse):
                    # the new_body was after s we need do the new_body
                    new_orelse = self.explicate_stmt(s, new_orelse, basic_blocks)

                return self.explicate_pred(test, new_body, new_orelse, basic_blocks)
            case While(test, body, []):
                # after_while = create_block(cont, basic_blocks)
                # goto_after_while = [after_while]
                test_label = label_name(generate_name('block'))
                new_body = [Goto(test_label)]
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                test_stmts =  self.explicate_pred(test, new_body, cont, basic_blocks)
                basic_blocks[test_label] = test_stmts
                return [Goto(test_label)]
            # case Expr(Call(Name('print'), [arg])):
            #     return [s] + cont

    def explicate_control(self, p):
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                # 也许这里是一个 newblock conclude = block(Return(Constant(0))])
                # create_block 是 goto 那个 bloc
                # conclude 这里是从那里 goto 到这里
                basic_blocks = {}
                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks[label_name('start')] = new_body
                result = CProgram(basic_blocks)
        f = interp_Cif.InterpCif().interp
        # breakpoint()
        return result

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        match e:
            case Name(name):
                return Variable(name)
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Constant(value):
                return Immediate(value)
            case _:
                raise Exception('error in select_arg, unexpected ' + repr(e))

    def select_compare(self, expr, then_label, else_label) -> List[instr]:
        # e | ne | l | le | g | ge

        match expr:
            case Compare(x, [op], [y]):
                # breakpoint()
                x = self.select_arg(x)
                y = self.select_arg(y)
                return [
                    Instr('cmpq', [y, x]),
                    # Instr('j{}'.format(op_dict[str(op)]), [then_label]),
                    JumpIf(op_dict[str(op)], then_label),
                    Jump(else_label)
                    # Instr('jmp', [else_label])
                ]

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
            case Assign([lhs], UnaryOp(Not(), rhs)) if rhs == rhs:
                lhs = self.select_arg(lhs)
                result.append(Instr('xorq',[Immediate(1), lhs]))
            case Assign([lhs], UnaryOp(Not(), rhs)):
                lhs = self.select_arg(lhs)
                arg = self.select_arg(rhs)
                result.append(Instr('movq',[arg, lhs]))
                result.append(Instr('xorq', [Immediate(1), lhs]))
            case Assign([lhs], Compare(x, [op], [y])):
                lhs = self.select_arg(lhs)
                l = self.select_arg(x)
                r = self.select_arg(y)
                result.append(Instr('cmpq', [l, r]))
                result.append(Instr('set{}'.format(op_dict[str(op)]), [ByteReg('bl')]))
                result.append(Instr('movzbq', [ByteReg('bl'), lhs]))
                pass
            case Assign([lhs], value):
                lhs = self.select_arg(lhs)
                arg = self.select_arg(value)
                result.append(Instr('movq', [arg, lhs]))
            case Return(Constant(value)):
                result.append(Instr('movq', [self.select_arg(Constant(value)), Reg('rax')]))
                result.append(Instr('retq', []))
            case Goto(label):
                result.append(Jump(label))
            case If(expr, [Goto(then_label)], [Goto(else_label)]):
                if_ = self.select_compare(expr, then_label, else_label)
                result.extend(if_)
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))
        return result
        pass        

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE


        blocks = {}
        match p:
            case CProgram(basic_blocks):
                for label, body in basic_blocks.items():
                    instr_body = []
                    for s in body:
                        instr_body.extend(self.select_stmt(s))
                    blocks[label] = instr_body
            case _:
                raise Exception('interp: unexpected ' + repr(p))


        x86 = X86Program(blocks)
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
            case Instr(op, [ByteReg(s)]):
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

    def uncover_live(self, ss: List[instr], live_before_block) -> Dict[instr, Set[location]]:

        # pre_instr_set = set()
        pre_instr = ss[-1]

        match ss[-1]:
            case Jump(label):
                pre_instr_set = live_before_block[label]
            case JumpIf(label):
                # jumpif 在最后是没有接着的指令的
                print("Never happened")
                pre_instr_set = set()
            case _:
                pre_instr_set = set()

        live_after = {
            ss[-1]: pre_instr_set
        }
        for s in list(reversed(ss))[1:]:
            match s:
                case Jump(label):
                    pre_instr_set = live_before_block[label]
                case JumpIf(cc, label):
                    tmp = (pre_instr_set - self.write_var(pre_instr)).union(self.read_var(pre_instr))
                    pre_instr_set = tmp.union(live_before_block[label])
                case _:
                    pre_instr_set = (pre_instr_set - self.write_var(pre_instr)).union(self.read_var(pre_instr))

            pre_instr = s
            live_after[s] = pre_instr_set

        return live_after


    def analyze_dataflow(self, G, transfer, bottom, join):
        trans_G = transpose(G)
        mapping = dict((v, bottom) for v in G.vertices())
        worklist = deque(G.vertices)
        while worklist:
            node = worklist.pop()
            inputs = [mapping[v] for v in trans_G.adjacent(node)]
            input = reduce(join, inputs, bottom)
            output = transfer(node, input)
            if output != mapping[node]:
                worklist.extend(G.adjacent(node))

    def build_interference(self, blocks) -> UndirectedAdjList:
        cfg = UndirectedAdjList()
        for label, body in blocks.items():
            for i in body:
                if isinstance(i, Jump) or isinstance(i, JumpIf):
                    # breakpoint()
                    cfg.add_edge(label, i.label)

        t_cfg = transpose(cfg)
        interference_graph = UndirectedAdjList()
        self.sort_cfg = topological_sort(cfg)
        live_before_block = {}
        live_after = {}

        for label in reversed(self.sort_cfg):
            ss = blocks[label]
            tmp = self.uncover_live(ss, live_before_block)
            # live update bind instr with
            # flow 分析解决的是 block 的分析问题。
            # 在解决 block 的
            live_before_block[label] = tmp[ss[0]]
            live_after.update(tmp)

        print("live_after ", live_after)
        for label, ss in blocks.items():
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

    #def color_graph(self, ss: List[instr], k=100) -> Dict[location, int]:
    def color_graph(self, blocks, k=100) -> Dict[location, int]:
        # first make it k big enough
        valid_colors = list(range(0, k))  # number of colar
        # Rdi 的保存问题
        color_map = {Reg('rax'): -1, Reg('rsp'): -2, Reg('rdi'): -3, ByteReg('bl'): -4}
        # color_map = {}
        saturated = {}

        def less(u, v):
            nonlocal saturated
            # breakpoint()
            if v not in saturated:
                return True
            return len(saturated[u]) < len(saturated[v])

        queue = PriorityQueue(less)
        interference_graph = self.build_interference(blocks)
        dot = interference_graph.show()
        # breakpoint()
        # dot.view()
        # breakpoint()
        vsets = interference_graph.vertices()
        # breakpoint()
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
                if u not in color_map:
                    color_map[u] = color
                for v in interference_graph.adjacent(u):
                    saturated[v].add(color)
            # else:
            #     spill.add(u)
        # breakpoint()
        return color_map

    def allocate_registers(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE

        # ? RDI
        self.color_regs = [Reg("rbx"), Reg("rcx"), Reg("rdx"), Reg("rsi"), Reg("rdi"), Reg("r8"), Reg("r9"), Reg("r10")]
        self.color_regs = [Reg("rbx"), Reg("rcx")]
        self.color_regs = [Reg("rbx")]
        # rcx as tmp
        self.color_regs = [Reg("rbx"), Reg("rcx")]

        self.alloc_callee_saved_regs = list(set(self.color_regs).intersection(callee_saved_regs))
        self.C = len(self.alloc_callee_saved_regs)
        # used_regs = 1
        color_regs_map = {i: reg for i, reg in enumerate(self.color_regs)}
        color_regs_map[-1] = Reg('rax')
        color_regs_map[-2] = Reg('rsp')
        color_regs_map[-3] = Reg('rdi')
        color_regs_map[-4] = ByteReg("bl")
        self.real_color_map = {}

        match(p):
            case X86Program(blocks):

                # breakpoint()
                new_blocks = {}
                color_map = self.color_graph(blocks)
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

                for label in self.sort_cfg:
                    ss = blocks[label]
                    result = []
                    for s in ss:
                        match(s):
                            case Instr(op, [source, target]):
                                # breakpoint()
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
                    new_blocks[label] = result

        # breakpoint()
        # breakpoint()

        self.rsp_sub = align(8 * self.S + 8 * self.C, 16) - 8 * self.C

        return X86Program(new_blocks)



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
            case Instr('cmpq', [x, Immediate(v)]):
                return [
                    Instr("movq", [Immediate(v), Reg("rax")]),
                    Instr("cmpq", [x, Reg("rax")])
                ]
            case Instr('movzbq', [ByteReg('bl'), Deref("rbp", y)]):
                return [
                    Instr("movzbq", [ByteReg('bl'), Reg("rax")]),
                    Instr("movq", [Reg("rax"), Deref("rbp", y)])
                ]
            case Instr(instr, args):
                return [i]
            case Callq(func, num_args):
                return [i]
            case _:
                return [i]
        pass

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        result = []
        for s in ss:
            ns = self.patch_instr(s)
            result.extend(ns)
        return result

    def patch_instructions(self, p: X86Program) -> X86Program:
        new_blocks = {}
        match(p):
            case X86Program(blocks):
                for label, body in blocks.items():
                    result = self.patch_instrs(body)
                    new_blocks[label] = result
        # breakpoint()
        return X86Program(new_blocks)

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        main = []
        conclusion = []
        # The spilled variables must b placed lower on the stackthan the saved callee
        # because there is rsp betweent it
        print("alloc_callee_saved_regs ", self.alloc_callee_saved_regs)
        extra_saved_regs = list(set(self.alloc_callee_saved_regs) - {Reg("rbp")})
        # breakpoint()

        match (p):
            case X86Program(blocks):
                main.extend([
                    Instr("pushq", [Reg("rbp")]),
                    Instr("movq", [Reg("rsp"), Reg("rbp")]),

                ])
                # save
                for reg in extra_saved_regs:
                    main.append(Instr("pushq", [reg]))
                main.extend([ Instr("subq", [Immediate(self.rsp_sub), Reg("rsp")])])
                main.append(Jump(label_name("start")))
                blocks[label_name("main")] = main
                # for label , body in blocks.items():
                #     pass

                conclusion.extend([ Instr("addq", [Immediate(self.rsp_sub), Reg("rsp")]),])
                for reg in extra_saved_regs[::-1]:
                    conclusion.append(Instr("popq", [reg]))

                conclusion.extend([
                    Instr("popq", [Reg("rbp")]),
                    Instr("retq", []),
                ])
                blocks[label_name("conclusion")] = conclusion

                blocks[self.sort_cfg[-1]][-1] = Jump(label_name("conclusion"))


        # breakpoint()
        return X86Program(blocks)

