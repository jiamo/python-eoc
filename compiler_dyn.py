import ast
from ast import *
from re import T

import x86_ast
from utils import *

from x86_ast import *
import bitarray
import bitarray.util
from collections import deque
from functools import reduce
import os
from graph import UndirectedAdjList, transpose, topological_sort
from priority_queue import PriorityQueue
import interp_Cif
from typing import List, Set, Dict
from typing import Tuple as Tupling
import type_check_Ltup
from interp_x86.eval_x86 import interp_x86
import type_check_Ctup
import type_check_Lfun
import type_check_Cfun
import type_check_Llambda
import type_check_Lany
import type_check_Clambda
import type_check_Cany


Binding = Tupling[Name, expr]
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

"""
tagof (IntType()) = 001   1 
tagof (BoolType()) = 100   4
tagof (TupleType(ts)) = 010  2
tagof (FunctionType(ps, rt))= 011 3  
tagof (type(None)) = 101  5
"""

def tagof(ty):
    match ty:
        case IntType():
            return 1
        case BoolType():
            return 4
        case TupleType(ts):
            return 2
        case FunctionType(ps, rt):
            return 3
        case _:
            return 5


def calculate_tag(size, ty, arith=None):
    tag = bitarray.bitarray(64, endian="little")
    tag.setall(0)
    p_mask = 7
    tag[0] = 1
    for i, type in enumerate(ty.types):
        # breakpoint()
        if isinstance(type, TupleType):
            tag[p_mask + i] = 1
        else:
            tag[p_mask + i] = 0
    tag[1:7] = tag[1:7] | bitarray.util.int2ba(size, length=6, endian='little')
    if arith:
        tag[57:62] = bitarray.util.int2ba(arith, length=5, endian='little')
    # print("tags", bitarray.util.ba2base(2, tag))
    return bitarray.util.ba2int(tag)

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
            case Lambda(params, body):
                params = [arg.arg for arg in params.args]
                return Lambda(params, body)

            case _:
                return e

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
            case Return(value):
                s_value = self.shrink_exp(value)
                result = Return(s_value)

            case AnnAssign(lhs, typ, value, simple):
                # breakpoint()
                s_value = self.shrink_exp(value)
                return AnnAssign(lhs, typ, s_value, simple)
            case _:
                raise Exception('error in shrink_stmt, unexpected ' + repr(s))
        return result

    def convert_type(self, t):
        match t:
            case Name('int'):
                return IntType()
            case IntType():
                return t
            case Subscript(Name('Callable'), Tuple([ps, rt]), Load()):
                t = FunctionType([self.convert_type(t) for t in ps.elts],
                              self.convert_type(rt))

                return t
            case _:
                return t

    def shrink(self, p: Module) -> Module:
        # YOUR CODE HERE
        # type_check_Llambda.TypeCheckLlambda().type_check(p)
        trace(p)
        result = []
        # breakpoint()
        main_stmts = []
        match p:
            case Module(body):
                print(body)

                for s in body:
                    match s:
                        case FunctionDef(name, args, stmts, dl, returns, comment):
                            # breakpoint()
                            args = [(arg.arg, self.convert_type(arg.annotation)) for arg in args.args]
                            result.append(
                                FunctionDef(name, args, [self.shrink_stmt(s) for s in stmts], dl,
                                            self.convert_type(returns), comment))
                        case _:
                            main_stmts.append(self.shrink_stmt(s))

            case _:
                raise Exception('interp: unexpected ' + repr(p))
        # for type typec
        main_stmts.append(Return(Constant(0)))
        main_def = FunctionDef("main", [], main_stmts, [], IntType(), None)

        result.append(main_def)

        # breakpoint()
        trace(result)
        return Module(result)

    def uniquify_exp(self, e, sym_map):
        match e:
            case Call(Name('input_int'), []):
                return e
            case Call(Name(fun), args):
                if fun in sym_map:
                    fun = sym_map.get(fun)
                args = [self.uniquify_exp(i, sym_map) for i in args]
                return Call(Name(fun), args)
            case Constant(v):
                return e
            case Name(id):
                # print(".... ", sym_map)
                if id in sym_map:
                    return Name(sym_map[id])
                else:
                    return e
            case BinOp(left, op, right):
                l_expr = self.uniquify_exp(left, sym_map)
                r_expr = self.uniquify_exp(right, sym_map)
                return_expr = BinOp(l_expr, op, r_expr)
                return return_expr
            case UnaryOp(op, v):
                # one by one
                v_expr = self.uniquify_exp(v, sym_map)
                return UnaryOp(op, v_expr)
            case Compare(left, [cmp], [right]):
                left_expr = self.uniquify_exp(left, sym_map)
                right_expr = self.uniquify_exp(right, sym_map)
                return Compare(left_expr, [cmp], [right_expr])

            case IfExp(expr_test, expr_body, expr_orelse):
                test_expr = self.uniquify_exp(expr_test, sym_map)
                body = self.uniquify_exp(expr_body, sym_map)
                orelse_expr  = self.uniquify_exp(expr_orelse, sym_map)
                return IfExp(test_expr, body, orelse_expr)
            case Subscript(value, slice, ctx):
                value_expr = self.uniquify_exp(value, sym_map)
                slice_expr = self.uniquify_exp(slice, sym_map)
                return Subscript(value_expr, slice_expr, ctx)
            case Tuple(exprs, ctx):
                # breakpoint()
                return Tuple([self.uniquify_exp(i, sym_map) for i in exprs], ctx)
                # return Subscript(new_value, slice, ctx)
            case Lambda(params, body):
                # lambda params have not type
                save_func_map = dict(sym_map)
                new_params = []
                for arg in params:
                    uname = generate_name(arg)
                    save_func_map[arg] = uname
                    new_params.append(uname)

                return Lambda(new_params, self.uniquify_exp(body, save_func_map))
            # case Begin(body, result):
            #     pass
            # case Call()
            case _:
                raise Exception('limit: unexpected ' + repr(e))

    def uniquify_stmt(self, stmt, sym_map):
        match stmt:
            case Expr(Call(Name('print'), [arg])):
                new_arg = self.uniquify_exp(arg, sym_map)
                return Expr(Call(Name('print'), [new_arg]))
            case Expr(value):
                expr = self.uniquify_exp(value, sym_map)
                return Expr(expr)
            case Assign([Name(name)], value):
                if name in sym_map:
                    uname = sym_map.get(name)
                else:
                    uname = generate_name(name)
                    sym_map[name] = uname

                v_expr = self.uniquify_exp(value, sym_map)
                return Assign([Name(uname)], v_expr)
            case If(test, body, orelse):
                test_expr = self.uniquify_exp(test, sym_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.uniquify_stmt(s, sym_map))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.uniquify_stmt(s, sym_map))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.uniquify_exp(test, sym_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.uniquify_stmt(s, sym_map))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.uniquify_exp(expr, sym_map)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                # breakpoint()
                if name in sym_map:
                    uname = sym_map.get(name)
                else:
                    uname = generate_name(name)
                    sym_map[name] = uname

                s_value = self.uniquify_exp(value, sym_map)
                return AnnAssign(Name(uname), typ, s_value, simple)
            # case _:
            #     return stmt

    def uniquify(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        result = []
        match p:
            case Module(body):

                # breakpoint()
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            new_args = []
                            sym_map = {}  # 是不是每一个函数都需要
                            for arg in args:
                                uname = generate_name(arg[0])
                                # breakpoint()
                                sym_map[arg[0]] = uname
                                new_args.append((uname, arg[1]))
                            new_body = [self.uniquify_stmt(s, sym_map) for s in stmts]
                            s.args = new_args
                            s.body = new_body
                            result.append(s)
            case _:
                raise Exception('uniquify: unexpected ' + repr(p))
        print(result)
        return Module(result)


    def reveal_functions_exp(self, exp, func_map):
        match exp:
            case Call(Name(x), args) if x not in builtin_functions :
                # no matter it was define or not it should be transform
                n = len(args)  # TODO may be there is default args
                return Call(FunRef(x, n), args)
                # return exp
            case BinOp(left, op, right):
                # breakpoint()
                left = self.reveal_functions_exp(left, func_map)
                # breakpoint()
                right = self.reveal_functions_exp(right, func_map)
                return BinOp(left, op, right)
            case _:
                return exp

    def reveal_functions_stmt(self, stmt, func_map):
        match stmt:
            case Expr(Call(Name('input'), [])):
                # new_arg = self.reveal_functions_exp(arg, func_map)
                # breakpoint()
                return Expr(Call(Name('input'), []))   # may be build in function
            case Expr(Call(Name('print'), [arg])):
                new_arg = self.reveal_functions_exp(arg, func_map)
                return Expr(Call(Name('print'), [new_arg]))
            case Expr(value):
                expr = self.reveal_functions_exp(value, func_map)
                return Expr(expr)
            case Assign([lhs], value):
                v_expr = self.reveal_functions_exp(value, func_map)
                return Assign([lhs], v_expr)
            case If(test, body, orelse):
                test_expr = self.reveal_functions_exp(test, func_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.reveal_functions_stmt(s, func_map))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.reveal_functions_stmt(s, func_map))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.reveal_functions_exp(test, func_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.reveal_functions_stmt(s, func_map))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.reveal_functions_exp(expr, func_map)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                value = self.reveal_functions_exp(value, func_map)
                return AnnAssign(Name(name), typ, value, simple)
            # case _:
            #     return stmt


    def reveal_functions(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        result = []
        self.func_map = {}
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            n = len(args.args) if isinstance(args, arguments) else len(args)
                            self.func_map[x] = FunRef(x, n)
                            result.append(s)
            case _:
                raise Exception('reveal_functions: unexpected ' + repr(p))
        result = []
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            result.append(
                                FunctionDef(x, args, [self.reveal_functions_stmt(s, self.func_map) for s in stmts], dl, returns, comment))
            case _:
                raise Exception('reveal_functions: unexpected ' + repr(p))
        # breakpoint()
        trace(result)
        return Module(result)

    def assigned_vars_stmt(self, stmt):
        match stmt:
            case Assign([Name(x)], value):
                # breakpoint()
                self.name_type_dict[x] = stmt.targets[0].has_type
                return {x}
            case _:
                return set()

    def free_in_stmt(self, bindings, s):
        match s:
            case Assign([Name(l)], value):
                # nolocal
                # 这里 如果是赋值 也是内部变量
                # 不需要逃逸成参数
                bindings.append(l)
                return self.free_in_exp(bindings, value)
            case _:
                return set()

    def free_in_exp(self, bindings, e):
        # 查找 free_in_exp
        match e:
            case Name(id):
                print("free_in_exp .... ", id, bindings)
                if id in bindings:
                    return set()
                else:
                    # breakpoint()
                    self.name_type_dict[id] = e.has_type
                    return {id}
            case TagOf(value):
                return set()
            case ValueOf(value, t):
                return self.free_in_exp(bindings, value)
            case Constant(value):
                return set()
            case BinOp(left, op, right):
                l = self.free_in_exp(bindings, left)
                r = self.free_in_exp(bindings, right)
                return l | r
            case UnaryOp(op, v):
                # one by one
                return self.free_in_exp(bindings, v)

            case Compare(left, [cmp], [right]):
                l = self.free_in_exp(bindings, left)
                r = self.free_in_exp(bindings, right)
                return l | r

            case IfExp(expr_test, expr_body, expr_orelse):
                # 所有的这种表达式可以用 children 来做
                t = self.free_in_exp(bindings, expr_test)
                b = self.free_in_exp(bindings, expr_body)
                e = self.free_in_exp(bindings, expr_orelse)
                return t | b | e
            case Subscript(value, slice, ctx):
                v = self.free_in_exp(bindings, value)
                s = self.free_in_exp(bindings, slice)
                return v | s
            case Tuple(exprs, ctx):
                # breakpoint()
                return set().union(*[self.free_in_exp(bindings, i) for i in exprs])
                # return Subscript(new_value, slice, ctx)
            case Lambda(params, body):
                # lambda params have not type
                return self.free_in_exp(params | bindings, body)
            case Call(name, args):
                return set().union(*[self.free_in_exp(bindings, i) for i in args])
            case Begin(stmts, expr):
                r = [self.free_in_stmt(bindings, i) for i in stmts] + [self.free_in_exp(bindings, expr)]
                return set().union(*r)
            case _:
                raise Exception('free_in_exp: unexpected ' + repr(e))

    def free_in_lambda_stmt(self, stmt):
        # lambda can be in any stmt
        # print(stmt)
        # breakpoint()
        match stmt:
            # 先假定这个是 只有 lambda
            case AnnAssign(Name(name), typ, Lambda(params, body), simple):
                # var not in params are free in bdoy
                # breakpoint()
                params_types = typ.param_types
                for i, j in zip(params, params_types):
                    # breakpoint()
                    self.name_type_dict[i] = j  # name have be unify
                return self.free_in_exp(params, body)
            case Assign([Name(x)], Call(Name('make_any'), [AnnLambda(params, returns, body), tag])):
                # breakpoint()
                for p in params:
                    self.name_type_dict[p[0]] = p[1]
                    # breakpoint()
                self.name_type_dict[x] = stmt.targets[0].has_type
                bindings = [i[0] for i in params]
                print("binding ", bindings)
                return self.free_in_exp(bindings, body)
            case Assign([Name(x)], value):
                # breakpoint()
                self.name_type_dict[x] = stmt.targets[0].has_type
                return set()
            case _:
                return set()

    def cast_insert_exp(self, e):
        match e:
            # case Call(Name('input_int'), []):
            #     return Call(Project(e.func, FunctionType([], AnyType())), [])
            case FunRef(name, airth):
                args_types = [AnyType() for i in range(airth)]
                return Inject(e, FunctionType(args_types, AnyType()))
            case Call(Name('input_int'), args):
                return Inject(e, IntType())
            case Call(x, args):
                x = self.cast_insert_exp(x)
                args = [self.cast_insert_exp(i) for i in args]
                args_types = [AnyType() for i in args]
                return Call(Project(x, FunctionType(args_types, AnyType())), args)
            case Constant(v):
                # breakpoint()
                if v is True or v is False:
                    return Inject(e, BoolType())
                elif isinstance(v, int):
                    return Inject(e, IntType())
                # elif isinstance(v, Function):
                #     return Inject(v, 'function')
                # elif isinstance(v, list):
                #     return Tagged(v, 'tuple')
                # elif isinstance(v, type(None)):
                #     return Tagged(v, 'none')
                else:
                    raise Exception('tag: unexpected ' + repr(v))
            case Name(id):
                # print(".... ", sym_map)
                return e
            case BinOp(left, op, right):
                left = self.cast_insert_exp(left)
                right = self.cast_insert_exp(right)
                return Inject(BinOp(Project(left, IntType()), op, Project(right, IntType())), IntType())
            case UnaryOp(op, v) if isinstance(op, USub):
                v = self.cast_insert_exp(v)
                v = Project(v, IntType())
                return Inject(UnaryOp(op, v), IntType())
            case UnaryOp(op, v) if isinstance(op, Not):
                # one by one
                v = self.cast_insert_exp(v)
                v = Project(v, BoolType())
                return Inject(UnaryOp(op, v), BoolType())
            case Compare(left, [cmp], [right]):
                left = self.cast_insert_exp(left)
                left = Project(left, IntType())
                right = self.cast_insert_exp(right)
                right = Project(right, IntType())
                return Inject(Compare(left, [cmp], [right]), BoolType())
            case IfExp(expr_test, expr_body, expr_orelse):
                t = self.cast_insert_exp(expr_test)
                t = Project(t, BoolType())
                b = self.cast_insert_exp(expr_body)
                e = self.cast_insert_exp(expr_orelse)
                return IfExp(t, b, e)
            case Subscript(value, slice, ctx):
                v = self.cast_insert_exp(value)
                s = self.cast_insert_exp(slice)
                return Call(Name('any_tuple_load'), [v, Project(s, IntType())])
            case Tuple(exprs, ctx):
                exprs = [self.cast_insert_exp(i) for i in exprs]
                exprs_types = [AnyType() for i in exprs]
                return Inject(Tuple(exprs, ctx), TupleType(exprs_types))
            case Lambda(params, body):
                params = [x for x in params]
                params_types = [AnyType() for x in params]
                body = self.cast_insert_exp(body)
                return Inject(Lambda(params, body), FunctionType(params_types, AnyType()))

    def cast_insert_stmt(self, stmt):
        match stmt:
            case Expr(Call(Name('print'), [arg])):
                # Find bug need cast_insert_stmt for all
                new_arg = self.cast_insert_exp(arg)
                # new_arg = Project(new_arg, IntType())
                return Expr(Call(Name('print'), [new_arg]))
            case Expr(Call(Name('input_int'), [])):
                # Find bug need cast_insert_stmt for all
                # new_arg = self.cast_insert_exp(arg)
                # new_arg = Project(new_arg, IntType())
                return stmt
            case Expr(value):
                expr = self.cast_insert_exp(value)
                return Expr(expr)
            case Assign([Name(x)], value):
                v_expr = self.cast_insert_exp(value)
                return Assign(stmt.targets, v_expr)
            case If(test, body, orelse):
                test_expr = self.cast_insert_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.cast_insert_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.cast_insert_stmt(s))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.cast_insert_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.cast_insert_stmt(s))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.cast_insert_exp(expr)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                value = self.cast_insert_exp(value)
                return AnnAssign(Name(name), typ, value, simple)

    def cast_insert(self, p):
        # YOUR CODE HERE
        trace(p)
        result = []
        match p:
            case Module(body):
                # breakpoint()
                for s in body:
                    # breakpoint()
                    match s:
                        case FunctionDef(fun, args, stmts, dl, returns, comment):
                            new_stmts = []
                            args = [(i[0], AnyType()) for i in args]
                            for s in stmts:
                                new_stmts.append(self.cast_insert_stmt(s))
                            # For type check!!!
                            returns = AnyType() # ?
                            result.append(FunctionDef(fun, args, new_stmts, dl, returns, comment))
                result = Module(result)
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        trace(result)
        return result

    def reveal_casts_exp(self, e):
        match e:
            case Project(e, ftype):
                match ftype:
                    case BoolType() | IntType():
                        tmp = Name(generate_name("tmp"))
                        e = self.reveal_casts_exp(e)
                        return Begin([Assign([tmp], e)],
                                     IfExp(Compare(TagOf(tmp), [Eq()], [Constant(tagof(ftype))]),
                                           ValueOf(tmp, ftype),
                                           Call(Name('exit'), [])))
                    case TupleType(t):
                        tmp = Name(generate_name("tmp"))
                        e = self.reveal_casts_exp(e)
                        return Begin([Assign([tmp], e)],
                                     IfExp(Compare(TagOf(tmp), [Eq()], [Constant(tagof(ftype))]),
                                           IfExp(
                                               Compare(
                                                   Call(Name('len'), [ValueOf(tmp, ftype)]),
                                                   [Eq()],
                                                   [Constant(len(t))]),
                                               ValueOf(tmp, ftype),
                                               Call(Name('exit'), [])),
                                           Call(Name('exit'), [])))
                    case FunctionType(args, returns):
                        tmp = Name(generate_name("tmp"))
                        e = self.reveal_casts_exp(e)
                        return Begin([Assign([tmp], e)],
                                     IfExp(Compare(TagOf(tmp), [Eq()], [Constant(tagof(ftype))]),
                                           IfExp(Compare(Call(Name('arity'), [ValueOf(tmp, ftype)]), [Eq()],
                                                         [Constant(len(args))]),
                                                  ValueOf(tmp, ftype),
                                                  Call(Name('exit'), [])),
                                           Call(Name('exit'), [])))
            case Inject(x, ftype):
                # breakpoint()
                x = self.reveal_casts_exp(x)
                return Call(Name('make_any'), [x, Constant(tagof(ftype))])
            case FunRef(name, airth):
                return e
            case Call(Name('any_tuple_load'), [e1,e2]):
                breakpoint()
                tmp1 = Name(generate_name('tmp'))
                tmp2 = Name(generate_name("tmp"))
                e1 = self.cast_insert_exp(e1)
                e2 = self.cast_insert_exp(e2)
                return Begin(
                    [Assign([tmp1], e1), Assign([tmp2], e2)],
                    IfExp(Compare(TagOf(tmp1), [Eq()], [Constant(2)]),
                          IfExp(Compare(tmp2, [Lt()], [Call(Name('any_len'), [tmp1])]),
                                Call(Name('any_tuple_load_unsafe'), [tmp1, tmp2]),
                                Call(Name('exit'), [])),
                          Call(Name('exit'), []))
                )
            case Call(x, args):
                x = self.reveal_casts_exp(x)
                args = [self.reveal_casts_exp(i) for i in args]
                return Call(x, args)
            case Constant(v):
                return e
            case Name(id):
                # print(".... ", sym_map)
                return e
            case BinOp(left, op, right):
                left = self.reveal_casts_exp(left)
                right = self.reveal_casts_exp(right)
                return BinOp(left, op, right)
            case UnaryOp(op, v):
                v = self.reveal_casts_exp(v)
                return UnaryOp(op, v)
            case Compare(left, [cmp], [right]):
                left = self.reveal_casts_exp(left)
                right = self.reveal_casts_exp(right)
                return Compare(left, [cmp], [right])
            case IfExp(expr_test, expr_body, expr_orelse):
                t = self.reveal_casts_exp(expr_test)
                b = self.reveal_casts_exp(expr_body)
                e = self.reveal_casts_exp(expr_orelse)
                return IfExp(t, b, e)
            case Subscript(value, slice, ctx):
                v = self.reveal_casts_exp(value)
                s = self.reveal_casts_exp(slice)
                return Subscript(v, s, ctx)
            case Tuple(exprs, ctx):
                exprs = [self.reveal_casts_exp(i) for i in exprs]
                return Tuple(exprs, ctx)
            case Lambda(params, body):
                # The real type is knowing.....?
                params = [(x, AnyType()) for x in params]
                # breakpoint()
                body = self.reveal_casts_exp(body)
                # breakpoint()
                return AnnLambda(params, AnyType(), body)
            case _:
                raise Exception('interp: reveal_casts_exp ' + repr(e))

    def reveal_casts_stmt(self, stmt):
        match stmt:
            case Expr(Call(Name('print'), [arg])):
                new_arg = self.reveal_casts_exp(arg)
                return Expr(Call(Name('print'), [new_arg]))
            case Expr(value):
                expr = self.reveal_casts_exp(value)
                return Expr(expr)
            case Assign([Name(x)], value):
                v_expr = self.reveal_casts_exp(value)
                return Assign(stmt.targets, v_expr)
            case If(test, body, orelse):
                test_expr = self.reveal_casts_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.reveal_casts_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.reveal_casts_stmt(s))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.reveal_casts_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.reveal_casts_stmt(s))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.reveal_casts_exp(expr)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                value = self.reveal_casts_exp(value)
                return AnnAssign(Name(name), typ, value, simple)
            case _:
                raise Exception('interp: reveal_casts_stmt ' + repr(stmt))


    def reveal_casts(self, p):
        # YOUR CODE HERE
        trace(p)
        result = []
        match p:
            case Module(body):
                # breakpoint()
                for s in body:
                    # breakpoint()
                    match s:
                        case FunctionDef(fun, args, stmts, dl, returns, comment):
                            new_stmts = []
                            for s in stmts:
                                new_stmts.append(self.reveal_casts_stmt(s))
                            result.append(FunctionDef(fun, args, new_stmts, dl, returns, comment))
                result = Module(result)
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        trace(result)
        # type_check_Lany.TypeCheckLany().type_check(p)
        return result

    def convert_assignments_exp(self, e):
        match e:
            case Call(Name('input_int'), []):
                return e
            case Call(x, args):
                args = [self.convert_assignments_exp(i) for i in args]
                return Call(x, args)
            case Constant(v):
                return e
            case TagOf(value):
                value = self.convert_assignments_exp(value)
                return TagOf(value)
            case ValueOf(value, typ):
                value = self.convert_assignments_exp(value)
                return ValueOf(value, typ)
            case Name(id):
                # print(".... ", sym_map)
                if id not in self.box_dict:
                    return e
                else:
                    return Subscript(Name(self.box_dict[id]), Constant(0), Load())
            case BinOp(left, op, right):
                left = self.convert_assignments_exp( left)
                right = self.convert_assignments_exp( right)
                return BinOp(left, op, right)
            case Begin(stmts, result):
                stmts = [self.convert_assignments_stmt(i) for i in stmts]
                result = self.convert_assignments_exp(result)
                return Begin(stmts, result)
            case UnaryOp(op, v):
                # one by one
                v = self.convert_assignments_exp(v)
                return UnaryOp(op, v)
            case Compare(left, [cmp], [right]):
                left = self.convert_assignments_exp(left)
                right = self.convert_assignments_exp(right)
                return Compare(left, [cmp], [right])

            case IfExp(expr_test, expr_body, expr_orelse):
                # 所有的这种表达式可以用 children 来做
                t = self.convert_assignments_exp(expr_test)
                b = self.convert_assignments_exp(expr_body)
                e = self.convert_assignments_exp(expr_orelse)
                return IfExp(t, b, e)
            case Subscript(value, slice, ctx):
                v = self.convert_assignments_exp(value)
                s = self.convert_assignments_exp(slice)
                return Subscript(v, s, ctx)
            case Tuple(exprs, ctx):
                # breakpoint()
                exprs = [self.convert_assignments_exp(i) for i in exprs]
                return Tuple(exprs, ctx)
                # return Subscript(new_value, slice, ctx)
            case Lambda(params, body):
                # lambda params have not type
                body = self.convert_assignments_exp(body)
                return Lambda(params, body)
            case AnnLambda(params, returns, body):
                # lambda params have not type
                # breakpoint()
                body = self.convert_assignments_exp(body)
                return AnnLambda(params, returns, body)
            case _:
                raise Exception('interp: convert_assignments_exp ' + repr(e))

    def convert_assignments_stmt(self, stmt):
        # lambda can be in any stmt
        match stmt:
            case Expr(Call(Name('print'), [arg])):
                new_arg = self.convert_assignments_exp(arg)
                return Expr(Call(Name('print'), [new_arg]))
            case Expr(value):
                expr = self.convert_assignments_exp(value)
                return Expr(expr)
            case Assign([Name(x)], value):
                v_expr = self.convert_assignments_exp(value)
                if x in self.box_dict:
                    return Assign([Subscript(Name(self.box_dict[x]), Constant(0), Store())], v_expr)
                else:
                    return Assign(stmt.targets, v_expr)
            case If(test, body, orelse):
                test_expr = self.convert_assignments_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.convert_assignments_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.convert_assignments_stmt(s))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.convert_assignments_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.convert_assignments_stmt(s))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.convert_assignments_exp(expr)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                value = self.convert_assignments_exp(value)
                return AnnAssign(Name(name), typ, value, simple)


    def convert_assignments(self, p: Module) -> Module:
        result = []
        type_check_Lany.TypeCheckLany().type_check(p)
        self.name_type_dict = {}
        self.top_funs = set()
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            self.top_funs.add(x)
                            params = {i[0] for i in args}
                            assigned_vars = set()
                            lambda_free_variables = set()
                            for s in stmts:
                                s_assign_vars = self.assigned_vars_stmt(s)
                                s_lambda_free_vars = self.free_in_lambda_stmt(s)
                                # breakpoint()
                                assigned_vars = assigned_vars.union(s_assign_vars)
                                lambda_free_variables = lambda_free_variables.union(s_lambda_free_vars)

                            box_names = assigned_vars.intersection(lambda_free_variables)
                            # if x  == "g":
                            #     breakpoint()
                            # if x == "main":
                            #     breakpoint()
                            init_box = []
                            self.box_dict = {}
                            for name in box_names:
                                box_name = name[:-2]
                                if name in params:
                                    init_box.append(Assign([Name(box_name)], Tuple([Name(name)], Load())))
                                else:
                                    # todo we don't infer the type of name
                                    init_box.append(Assign([Name(box_name)], Tuple([Uninitialized(self.name_type_dict[name])], Load())))
                                self.box_dict[name] = box_name

                            stmts = [self.convert_assignments_stmt(i) for i in stmts]
                            # returns = None  # need the lambda typ
                            result.append(FunctionDef(x, args, init_box + stmts, dl, returns, comment))
            case _:
                raise Exception('convert_assignments: unexpected ' + repr(p))
        # breakpoint()
        # trace(result)
        r = Module(result)
        trace(r)
        return r

    def convert_to_closures_exp(self, e):
        match e:
            # case Call(Name('input_int'), []):
            case Call(Name(x), cargs) if x == 'make_any' and isinstance(cargs[0], AnnLambda):
                # breakpoint()
                f = self.convert_to_closures_exp(cargs[0])

                r = Call(Name(x), [f, Constant(tagof(f.closure_type))])
                r.my_extra_type = f.closure_type
                return r
            case Call(Name(x), cargs) if x == 'make_any' and isinstance(cargs[0], FunRef):
                # breakpoint()
                f = self.convert_to_closures_exp(cargs[0])
                if cargs[0].name in self.func_val_real_types:
                    closure_type = self.func_val_real_types[cargs[0].name]
                    new_tag_type = Constant(tagof(closure_type))
                else:
                    closure_type = None
                    new_tag_type = self.convert_to_closures_exp(cargs[1])
                r = Call(Name(x), [f, new_tag_type])
                print("make_any  FunRef", cargs,  closure_type)
                r.my_extra_type = closure_type  # type 需要传递
                return r
            case Call(Name(x), args):
                args = [self.convert_to_closures_exp(i) for i in args]
                # breakpoint()
                ne = Call(Name(x), args)
                if x == 'make_any':
                    ne.my_extra_type = AnyType()
                return ne
            case FunRef(name, n):
                # c = Closure(n, [FunRef(name, n)])
                # print("... name is {}".format(name))
                # breakpoint()
                if name in self.top_funs:
                    # breakpoint()
                    c = Closure(n, [FunRef(name, n)])
                else:
                    c = Name(name)
                return c
            case Call(x, args):
                # breakpoint()
                args = [self.convert_to_closures_exp(i) for i in args]

                c = self.convert_to_closures_exp(x)
                tmp = generate_name("clos")
                # breakpoint()
                 # after call the value type should be update as the call return type
                ne = Begin(
                    [Assign([Name(tmp)], c)],
                    Call(Subscript(Name(tmp), Constant(0), Load()), [Name(tmp), *args])
                )
                # breakpoint()
                # now c.my_extra_type must be tuple
                # if isinstance(c.my_extra_type, AnyType):
                #     breakpoint()
                if isinstance(c.my_extra_type, AnyType):
                    # breakpoint()
                    ne.my_extra_type = AnyType()
                else:
                    # breakpoint()
                    print("calling ", tmp, c.my_extra_type.types[0].ret_type )
                    ne.my_extra_type = c.my_extra_type.types[0].ret_type  # x's  my_extra_type is not x()'s my_extra_type
                return ne
            case Begin(stmts, exp):
                stmts = [self.convert_to_closures_stmt(i) for i in stmts]
                exp = self.convert_to_closures_exp(exp)
                ne = Begin(stmts, exp)
                ne.my_extra_type = exp.my_extra_type
                return ne
            case TagOf(value):
                value = self.convert_to_closures_exp(value)
                return TagOf(value)

            case ValueOf(value, typ):
                value = self.convert_to_closures_exp(value)
                if isinstance(value, Name) and value.id in self.func_val_real_types:
                    if isinstance(self.func_val_real_types[value.id], TupleType):
                        typ = self.func_val_real_types[value.id]

                # bool cam't change
                # print("ValueOf ", value, value.my_extra_type)
                ne = ValueOf(value, typ)
                ne.my_extra_type = typ
                return ne

            case Constant(v):
                # we need change callable to
                # match v:
                #     case TagOf(FunctionType(args_types, AnyType())):
                #         # change to ClosureType
                #         # how can I know this function free_types is what?
                #         # It is wrong
                #         closureTy = TupleType(
                #             [FunctionType(args_types, AnyType())]
                #         )
                #         return TagOf(closureTy)
                return e

            case Name(id):
                # breakpoint()
                e.my_extra_type = self.func_val_real_types[id]

                if id not in self.box_dict:
                    print("id is .... {} {} {}".format(id, self.top_funs, self.func_val_real_types))
                    # if isinstance(id, )
                    if id in self.top_funs:
                        # pass
                        funref = self.func_map[id]

                        ne = Closure(funref.arity, [funref])
                        ne.my_extra_type = self.func_val_real_types[id]
                        return ne
                    return e
                else:
                    return Subscript(Name(self.box_dict[id]), Constant(0), Load())
            case BinOp(left, op, right):
                # breakpoint()
                left = self.convert_to_closures_exp( left)
                # breakpoint()
                right = self.convert_to_closures_exp( right)
                return BinOp(left, op, right)
            case UnaryOp(op, v):
                # one by one
                v = self.convert_to_closures_exp(v)
                return UnaryOp(op, v)

            case Compare(left, [cmp], [right]):
                left = self.convert_to_closures_exp(left)
                right = self.convert_to_closures_exp(right)
                if isinstance(left, TagOf) and left.value.id in self.func_val_real_types:
                    # breakpoint()
                    if isinstance(self.func_val_real_types[left.value.id], TupleType):
                        right = Constant(tagof(self.func_val_real_types[left.value.id]))

                # right = self.convert_to_closures_exp(right)
                ne = Compare(left, [cmp], [right])
                ne.my_extra_type = BoolType()
                return ne

            case IfExp(expr_test, expr_body, expr_orelse):
                t = self.convert_to_closures_exp(expr_test)
                b = self.convert_to_closures_exp(expr_body)
                else_ = self.convert_to_closures_exp(expr_orelse)

                # at now just use the expr_body type
                ne = IfExp(t, b, else_)
                ne.my_extra_type = b.my_extra_type
                return ne
            case Subscript(value, slice, ctx):
                v = self.convert_to_closures_exp(value)
                s = self.convert_to_closures_exp(slice)
                return Subscript(v, s, ctx)
            case Tuple(exprs, ctx):
                # breakpoint()
                exprs = [self.convert_to_closures_exp(i) for i in exprs]

                ne = Tuple(exprs, ctx)
                ne.my_extra_type = TupleType([i.my_extra_type for i in exprs])
                return ne
                # return Subscript(new_value, slice, ctx)
            case Lambda(params, body):
                name = generate_name('lambda')
                n = len(params)

                free_vars = list(self.free_in_exp(params, body))
                # free_vars return the name.....
                free_named_vars = [Name(i) for i in free_vars]
                free_types = [self.name_type_dict[i] for i in free_vars]
                # breakpoint()
                lambda_parms = []
                stmts = []
                closTy = TupleType([Bottom(), *[self.name_type_dict[i] for i in free_vars]])
                fsv_name = generate_name('fvs')
                lambda_parms.append((fsv_name, closTy))
                for i in params:
                    # breakpoint()
                    lambda_parms.append((i, self.name_type_dict[i]))

                for i, v in enumerate(free_named_vars):
                    stmts.append(Assign([v], Subscript(Name(fsv_name), Constant(i+1), Load())))

                # breakpoint()
                returns = self.tmp_ann_typ.ret_type
                # May be the return was function type again and need to convertion to closure type TODO
                lambda_def = FunctionDef(name, lambda_parms, stmts + [Return(body)], None, returns, None)
                self.lambda_convert_defs.append(lambda_def)

                # The return type was
                closureTy = TupleType([FunctionType([i[1] for i in lambda_parms], returns), *free_types])
                c = Closure(n, [FunRef(name, n), *free_named_vars])  # save the free_named_vars into the cloure
                c.closure_type = closureTy
                c.my_extra_type = closureTy
                return c
            case AnnLambda(params, returns, body):
                name = generate_name('lambda')
                n = len(params)

                # params have types info
                bindings = [i[0] for i in params]
                free_vars = list(self.free_in_exp(bindings, body))
                # breakpoint()
                free_named_vars = [Name(i) for i in free_vars]
                free_types = [self.name_type_dict[i] for i in free_vars]
                lambda_parms = []
                stmts = []
                closTy = TupleType([Bottom(), *[self.name_type_dict[i] for i in free_vars]])
                fsv_name = generate_name('fvs')
                lambda_parms.append((fsv_name, closTy))
                for i in params:
                    # breakpoint()
                    # breakpoint()
                    lambda_parms.append(i)

                for i, v in enumerate(free_named_vars):
                    stmts.append(Assign([v], Subscript(Name(fsv_name), Constant(i+1), Load())))

                # breakpoint()
                # TODO may be we need just trust the Annlambda
                # returns = self.tmp_ann_typ.ret_type

                # May be the return was function type again and need to convertion to closure type TODO
                lambda_def = FunctionDef(name, lambda_parms, stmts + [Return(body)], None, returns, None)
                self.lambda_convert_defs.append(lambda_def)

                # The return type was
                # but I don't know its real free_types in
                # 好像不需要 *free_types
                closureTy = TupleType(
                    [FunctionType([i[1] for i in lambda_parms], returns)]
                )

                c = Closure(n, [FunRef(name, n), *free_named_vars])  # save the free_named_vars into the cloure
                # breakpoint()
                c.my_extra_type = closureTy
                c.closure_type = closureTy
                self.func_val_real_types[name] = closureTy

                return c
            case Uninitialized(ty):
                e.my_extra_type = ty
                return e
            case _:
                raise Exception('convert_to_closures_exp: unexpected ' + repr(e))

    def convert_to_closures_stmt(self, stmt):
        match stmt:
            case Expr(Call(x, args)):
                new_args = [self.convert_to_closures_exp(i) for i in args]
                return Expr(Call(x, new_args))
            case Expr(value):
                expr = self.convert_to_closures_exp(value)
                return Expr(expr)
            case Assign([l], value):
                # TODO l need do?
                # l = self.convert_to_closures_exp(l)

                v_expr = self.convert_to_closures_exp(value)
                # if isinstance(v_expr, Closure):
                #     breakpoint()
                # Subscript single type don't need to be check
                if not isinstance(l, Subscript):
                    self.func_val_real_types[l.id] = v_expr.my_extra_type

                return Assign(stmt.targets, v_expr)
            case If(test, body, orelse):
                test_expr = self.convert_to_closures_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.convert_to_closures_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.convert_to_closures_stmt(s))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.convert_to_closures_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.convert_to_closures_stmt(s))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.convert_to_closures_exp(expr)
                return Return(expr)
            case AnnAssign(Name(name), typ, value, simple):
                # breakpoint()
                self.tmp_ann_typ = typ
                value = self.convert_to_closures_exp(value)
                self.lambda_exp[Name(name)] = value
                return Assign([Name(name)], value)

    def find_last_stmt_return(self, stmt):
        # if it was return
        match stmt:
            case Return(exp):
                return exp
            case If(test, body, orelse):
                # breakpoint()
                return self.find_last_stmt_return(body[-1])

    def convert_to_closures(self, p):
        result = []
        type_check_Lany.TypeCheckLany().type_check(p)
        # self.name_type_dict = {}
        self.lambda_convert_defs = []
        self.lambda_exp = {}
        self.func_val_real_types = {}
        match p:
            case Module(body):
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            # detect need add a new function?
                            for i,t in args:
                                # breakpoint()
                                self.func_val_real_types[i] = t
                            stmts = [self.convert_to_closures_stmt(i) for i in stmts]
                            if x != "main":
                                tmp = generate_name('fvs')
                                args = [(tmp, Bottom())] + args
                            # breakpoint()
                            return_value = self.find_last_stmt_return(stmts[-1])


                            # if isinstance(return_value, Name) and return_value in self.lambda_exp:
                            #     # pass
                            #     returns = self.lambda_exp[stmts[-1].value].closure_type
                            # change to my_extra_type

                            # breakpoint()
                            returns = return_value.my_extra_type

                            # we keep real type in here

                            self.func_val_real_types[x] = TupleType([FunctionType([i[1] for i in args], returns)])


                            # but return still return Any?????
                            result.append(FunctionDef(x, args, stmts, dl, AnyType(), comment))
            case _:
                raise Exception('convert_to_closures: unexpected ' + repr(p))
        # breakpoint()
        result = self.lambda_convert_defs + result
        trace(result)
        r = Module(result)
        trace(r)
        # breakpoint()
        type_check_Lany.TypeCheckLany().type_check(r)
        # sys.exit()
        return r

    def limit_functions_exp(self, e, func_arg_map, args_map):
        match e:
            case Call(Name(x), args):
                args = [self.limit_functions_exp(i, func_arg_map, args_map) for i in args]
                return Call(Name(x), args)
            case Call(FunRef(name, arth), args):
                args = [self.limit_functions_exp(i, func_arg_map, args_map) for i in args]

                if name in func_arg_map:
                    first = [args[i] for i in range(5)]
                    after = Tuple([args[i] for i in range(5, len(args))], Load())
                    return Call(FunRef(name, 6), first + [after])
                else:
                    return e
            case Constant(v):
                return e
            case TagOf(v):
                return e
            case ValueOf(v, t):
                return e
            case Name(id):
                if id in args_map:
                    return args_map[id]
                else:
                    return e
            case BinOp(left, op, right):
                print(left, op, right)
                l_expr = self.limit_functions_exp(left, func_arg_map, args_map)
                r_expr = self.limit_functions_exp(right, func_arg_map, args_map)
                return_expr = BinOp(l_expr, op, r_expr)
                return return_expr
            case UnaryOp(op, v):
                # one by one
                v_expr = self.limit_functions_exp(v, func_arg_map, args_map)
                return UnaryOp(op, v_expr)

            case Compare(left, [cmp], [right]):
                left_expr = self.limit_functions_exp(left, func_arg_map, args_map)
                right_expr = self.limit_functions_exp(right, func_arg_map, args_map)
                return Compare(left_expr, [cmp], [right_expr])

            case IfExp(expr_test, expr_body, expr_orelse):
                test_expr = self.limit_functions_exp(expr_test, func_arg_map, args_map)
                body = self.limit_functions_exp(expr_body, func_arg_map, args_map)
                orelse_expr = self.limit_functions_exp(expr_orelse, func_arg_map, args_map)
                return IfExp(test_expr, body, orelse_expr)

            case Subscript(value, slice, ctx):
                value_expr = self.limit_functions_exp(value, func_arg_map, args_map)
                slice_expr = self.limit_functions_exp(slice, func_arg_map, args_map)
                return Subscript(value_expr, slice_expr, ctx)
            case Tuple(exprs, ctx):
                # breakpoint()
                return Tuple([self.limit_functions_exp(i, func_arg_map, args_map) for i in exprs], ctx)
                # return Subscript(new_value, slice, ctx)
            case Uninitialized(ty):
                return e
            case Call(Subscript(Name(f), Constant(0), Load()), args) if len(args) > 6:
                first = [args[i] for i in range(5)]
                after = Tuple([args[i] for i in range(5, len(args))], Load())
                return Call(Subscript(Name(f), Constant(0), Load()), first + [after])
            case Call(Subscript(Name(f), Constant(0), Load()), args):
                return e
            case Closure(arith, [FunRef(name, arity), *z]):
                return Closure(6 if arith > 6 else arith, [FunRef(name, 6 if arith > 6 else arity), *z])
            case FunRef(name, arith):
                return FunRef(name, 6 if arith > 6 else arith)
            case Begin(stmts, result):
                stmts = [self.limit_functions_stmt(i, func_arg_map, args_map) for i in stmts]
                result = self.limit_functions_exp(result, func_arg_map, args_map)
                return Begin(stmts, result)
            case _:
                raise Exception('limit exp: unexpected ' + repr(e))

    def limit_functions_stmt(self, stmt, func_args_map, args_map):
        match stmt:
            case Expr(Call(Name(x), [arg])):
                new_arg = self.limit_functions_exp(arg, func_args_map, args_map)
                return Expr(Call(Name(x), [new_arg]))
            case Expr(value):
                expr = self.limit_functions_exp(value, func_args_map, args_map)
                return Expr(expr)
            case Assign([lhs], value):
                v_expr = self.limit_functions_exp(value, func_args_map, args_map)
                return Assign([lhs], v_expr)
            case If(test, body, orelse):
                test_expr = self.limit_functions_exp(test, func_args_map, args_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.limit_functions_stmt(s, func_args_map, args_map))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.append(self.limit_functions_stmt(s, func_args_map, args_map))
                return If(test_expr, body_stmts, orelse_stmts)
            case While(test, body, []):
                test_expr = self.limit_functions_exp(test, func_args_map, args_map)
                body_stmts = []
                for s in body:
                    body_stmts.append(self.limit_functions_stmt(s, func_args_map, args_map))
                return While(test_expr, body_stmts, [])
            case Return(expr):
                expr = self.limit_functions_exp(expr, func_args_map, args_map)
                return Return(expr)

    def limit_functions(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        result = []
        func_args_map = {}
        match p:
            case Module(body):
                print(body)
                # breakpoint()
                for s in body:
                    match s:
                        case FunctionDef(x, args, stmts, dl, returns, comment):
                            # breakpoint()
                            # lambda 已经转化成 FunctionDef 了
                            new_args = []

                            # change returns
                            if len(args) > 6:

                                pass
                                for i in range(5):
                                    new_args.append(args[i])
                                print("... ", i)
                                # breakpoint()
                                new_args_map = {}
                                tuple_args = []
                                for i in range(5, len(args)):
                                    tuple_args.append(self.convert_type(args[i][1]))  # this is type signature
                                    new_args_map[args[i][0]] = Subscript(Name('tup'), Constant(i - 5), Load())
                                new_args.append(("tup", TupleType(tuple_args)))
                                func_args_map[x] = new_args_map

                                # return 的参数如果也是大于 6 的那么这个 return 液压好改啊

                                result.append(FunctionDef(x, new_args, stmts, dl, returns, comment))
                            else:
                                result.append(s)
            case _:
                raise Exception('reveal_functions: unexpected ' + repr(p))

        new_result = []

        for s in result:
            match s:
                case FunctionDef(fun, args, stmts, dl, returns, comment):
                    # breakpoint()
                    if fun in func_args_map:
                        # 到这个函数之后才用这个 args map
                        args_map = func_args_map[fun]
                    else:
                        args_map = {}

                    # 在这里改 return 更加合适
                    return_value = self.find_last_stmt_return(stmts[-1])
                    if isinstance(return_value, Name) and return_value in self.lambda_exp:
                        # reducet type
                        lambda_name = self.lambda_exp[stmts[-1].value].args[0].name
                        if lambda_name in func_args_map:
                            match returns:
                                # 用同样的 args 居然 覆盖了上面的
                                # 该用 targs
                                case TupleType([FunctionType(targs, y), *z]):
                                    first = [targs[i] for i in range(5)]
                                    after = [TupleType([targs[i] for i in range(5, len(targs))])]
                                    returns = TupleType([FunctionType(first + after, y), *z])
                        # breakpoint()
                    new_result.append(
                        FunctionDef(fun, args, [self.limit_functions_stmt(s, func_args_map, args_map) for s in stmts],
                                    dl, returns, comment))
                case _:
                    raise Exception('limit_functions: unexpected ' + repr(s))


        # breakpoint()
        trace("limit function {}".format(new_result))
        return Module(new_result)

    def expose_allocation_exp(self, exp) -> Tupling[expr, List[stmt]]:
        match exp:
            case Call(x, args):
                stmts = []
                new_args = []
                for arg in args:
                    new_arg, arg_stmts = self.expose_allocation_exp(arg)
                    stmts.extend(arg_stmts)
                    new_args.append(new_arg)
                # breakpoint()
                return Call(x, new_args), stmts

            case Subscript(value, slice, ctx):
                new_value, stmts = self.expose_allocation_exp(value)
                return Subscript(new_value, slice, ctx), stmts
            case Tuple(exprs):
                stmts = []

                # do expr
                tmp_exprs = []
                for expr in exprs:
                    tmp = generate_name("tmp")
                    var = Name(tmp)
                    new_expr, tmp_stmts = self.expose_allocation_exp(expr)
                    stmts.extend(tmp_stmts)
                    new_stmt = Assign([var], new_expr)
                    stmts.append(new_stmt)
                    tmp_exprs.append(var)
                # breakpoint()
                n = len(exprs)
                stmts.append(
                    If(Compare(BinOp(GlobalValue("free_ptr"), Add(), Constant(8 * (n+1))), [Lt()], [GlobalValue("fromspace_end")]),
                       [Expr(Constant(0))],
                       [Collect(8 * (n+1))])
                )
                tmp = generate_name("alloc")
                var = Name(tmp)
                stmts.append(Assign([var], Allocate(n, exp.has_type))) # may exp.has_type.types
                for i in range(len(exprs)):
                    stmts.append(Assign([Subscript(var, Constant(i), Store())], tmp_exprs[i])) # todo the Load is what
                return var, stmts
            case Closure(arity, exprs):

                # may be we can using begin
                stmts = []

                # do expr
                tmp_exprs = []
                for expr in exprs:
                    tmp = generate_name("tmp")
                    var = Name(tmp)
                    new_expr, tmp_stmts = self.expose_allocation_exp(expr)
                    stmts.extend(tmp_stmts)
                    new_stmt = Assign([var], new_expr)
                    stmts.append(new_stmt)
                    tmp_exprs.append(var)
                # breakpoint()
                n = len(exprs)
                stmts.append(
                    If(Compare(BinOp(GlobalValue("free_ptr"), Add(), Constant(8 * (n+1))), [Lt()], [GlobalValue("fromspace_end")]),
                       [Expr(Constant(0))],
                       [Collect(8 * (n+1))])
                )
                tmp = generate_name("alloc")
                var = Name(tmp)
                stmts.append(Assign([var], AllocateClosure(n, exp.has_type, arity))) # may exp.has_type.types
                for i in range(len(exprs)):
                    stmts.append(Assign([Subscript(var, Constant(i), Store())], tmp_exprs[i])) # todo the Load is what
                return var, stmts

            case BinOp(left, op, right):
                left, left_stmts = self.expose_allocation_exp(left)
                right, right_stmts = self.expose_allocation_exp(right)
                return BinOp(left, op, right), left_stmts + right_stmts

            case Uninitialized(t):
                return exp, []
            case Name(x):
                return exp, []
            case Constant(x):
                return exp, []
            case TagOf(x):
                return exp, []  # we don't have tuple in Tag
            case ValueOf(x):
                return exp, []
            case FunRef(x, n):
                return exp, []
            case Begin(body, exp):
                new_body = []
                for i in body:
                    new_body.extend(self.expose_allocation_stmt(i))
                exp, stmts = self.expose_allocation_exp(exp)
                new_body.extend(stmts)
                # we can't make exp 's stmt before begin's own stmt

                return Begin(new_body, exp), []
            case Compare(x, [op], yl):
                nx, stmts = self.expose_allocation_exp(x)
                n_yl = []
                for y in yl:
                    ny, ny_stmts = self.expose_allocation_exp(y)
                    n_yl.append(ny)
                    stmts.extend(ny_stmts)
                return Compare(nx, [op], n_yl), stmts
            case UnaryOp(op, expr):
                expr, stmts = self.expose_allocation_exp(expr)
                return UnaryOp(op, expr), stmts
            case IfExp(test, body, else_):
                test, test_stmts = self.expose_allocation_exp(test)
                body, body_stmts = self.expose_allocation_exp(body)
                if body_stmts:
                    body = Begin(body_stmts, body)
                else_, else_stmts = self.expose_allocation_exp(else_)
                if else_stmts:
                    else_ = Begin(else_stmts, else_)
                    # 没有 stmt 没有必要用 begin 包装

                # test_stmts 是可以在前面返回的
                return IfExp(test, body, else_), test_stmts
            case _:
                raise Exception('expose_allocation_exp: unexpected ' + repr(exp))


    def expose_allocation_stmt(self, s: stmt) -> List[stmt]:
        # result = []
        # breakpoint()
        match s:
            case Expr(Call(Name(x), [arg])):
                new_arg, stmts = self.expose_allocation_exp(arg)
                return stmts + [Expr(Call(Name(x), [new_arg]))]
            case Expr(value):
                expr, stmts = self.expose_allocation_exp(value)
                return stmts + [Expr(expr)]
            case Assign([lhs], value):
                v_expr , stmts = self.expose_allocation_exp(value)
                return stmts + [Assign([lhs], v_expr)]
            case If(test, body, orelse):
                test_expr, stmts = self.expose_allocation_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.extend(self.expose_allocation_stmt(s))
                orelse_stmts = []
                for s in orelse:
                    orelse_stmts.extend(self.expose_allocation_stmt(s))
                return stmts + [If(test_expr, body_stmts, orelse_stmts)]
            case While(test, body, []):
                test_expr, stmts = self.expose_allocation_exp(test)
                body_stmts = []
                for s in body:
                    body_stmts.extend(self.expose_allocation_stmt(s))
                return stmts + [While(test_expr, body_stmts, [])]
            case Return(value):
                expr, stmts = self.expose_allocation_exp(value)
                return stmts + [Return(expr)]
            case _:
                raise Exception('error in expose_allocation_stmt, unexpected ' + repr(s))
        # return result

    def expose_allocation(self, p):
        # YOUR CODE HERE
        trace(p)
        type_check_Lany.TypeCheckLany().type_check(p)
        result = []
        match p:
            case Module(body):
                # breakpoint()
                for s in body:
                    # breakpoint()
                    match s:
                        case FunctionDef(fun, args, stmts, dl, returns, comment):
                            new_stmts = []
                            for s in stmts:
                                new_stmts.extend(self.expose_allocation_stmt(s))
                            result.append(FunctionDef(fun, args, new_stmts, dl, returns, comment))
                result = Module(result)
            case _:
                raise Exception('interp: expose_allocation unexpected ' + repr(p))

        # breakpoint()
        trace(result)
        return result

    def rco_exp(self, e: expr, need_atomic: bool) -> Tupling[expr, Temporaries]:
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
            case GlobalValue(label):
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # v_tmps.append()
                    return tmp, [(tmp, e)]
                else:
                    return e, []
            case Allocate(length, ty):
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # v_tmps.append()
                    return tmp, [(tmp, e)]
                else:
                    return e, []
            case AllocateClosure(length, ty, airth):
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # v_tmps.append()
                    return tmp, [(tmp, e)]
                else:
                    return e, []
            case Constant(value):
                return e, []
            case TagOf(value):
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # v_tmps.append()
                    return tmp, [(tmp, e)]
                else:
                    return e, []
            case ValueOf(value, ty):
                # we think the value was must of tmp TODO may be it is not right
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # v_tmps.append()
                    return tmp, [(tmp, e)]
                else:
                    return e, []

            # TODO check it is right for normal exp
            # case Call(Name('input_int'), []):
            #     return e, []  # beachse match e was
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

                # TODO does this need atom?
                test_expr, test_tmps = self.rco_exp(expr_test, False)
                body, body_tmps = self.rco_exp(expr_body, False)
                orelse_expr, orelse_tmp = self.rco_exp(expr_orelse, False)

                # 如果这里不这个name
                if body_tmps:
                    body = Begin([Assign([name], expr) for name,expr in body_tmps], body)
                if orelse_tmp:
                    orelse_expr = Begin([Assign([name], expr) for name, expr in orelse_tmp], orelse_expr)
                return_expr = IfExp(test_expr, body, orelse_expr)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    test_tmps.append((tmp, return_expr))
                    return tmp, test_tmps
                else:
                    return return_expr, test_tmps
            case Subscript(value, slice, ctx):
                value_expr, value_tmps = self.rco_exp(value, True)
                slice_expr, slice_tmps = self.rco_exp(slice, True)
                return_expr = Subscript(value_expr, slice_expr, ctx)
                value_tmps.extend(slice_tmps)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    value_tmps.append((tmp, return_expr))
                    return tmp, value_tmps
                else:
                    return return_expr, value_tmps
                # return Subscript(new_value, slice, ctx)
            case FunRef(n, art):
                fun_tmp = Name(generate_name("fun"))
                new_tmps = []
                new_tmps.append((fun_tmp, FunRef(n, art)))
                return fun_tmp, new_tmps
            case Call(fr, args):
                # 	fun.0 = add(%rip)
                # 	tmp.1 = fun.0(40, 2)
                new_args = []
                fun_tmp, new_tmps = self.rco_exp(fr, True)
                for arg in args:
                    arg_expr, arg_tmps = self.rco_exp(arg, True)
                    new_args.append(arg_expr)
                    new_tmps.extend(arg_tmps)
                return_expr = Call(fun_tmp, new_args)
                if need_atomic and (not self.optimse_tail):
                    tmp = Name(generate_name("tmp"))
                    new_tmps.append((tmp, return_expr))
                    return tmp, new_tmps
                else:
                    return return_expr, new_tmps
            case Begin(body, result):
                # first body then result
                new_body = []
                for i in body:
                    new_body.extend(self.rco_stmt(i))
                new_result, tmps = self.rco_exp(result, True)  # does begin it self need atom
                for name, i in tmps:
                    new_body.append(Assign([name], i))
                return_exp = Begin(new_body, new_result)
                if need_atomic:
                    tmp = Name(generate_name("tmp"))
                    # the begin itself is not
                    return tmp, [(tmp, return_exp)]
                else:
                    return return_exp, []
            case Uninitialized(t):
                return e, []
            case _:
                raise Exception('error in rco_exp, unexpected ' + repr(e))
    
    def rco_stmt(self, s: stmt) -> List[stmt]:
        # YOUR CODE HERE
        result = []
        # breakpoint()
        self.optimse_tail = False
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
            case Collect(size):
                result.append(s)
            case Return(value):
                # the tail call need the it to be false
                # 为了调试可以先不这样
                self.optimse_tail = True
                value_expr, value_tmps = self.rco_exp(value, True)
                for name, t_expr in value_tmps:
                    result.append(Assign([name], t_expr))
                result.append(Return(value_expr))
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        return result

    def remove_complex_operands(self, p: Module) -> Module:
        # YOUR CODE HERE
        trace(p)
        type_check_Lany.TypeCheckLany().type_check(p)
        result = []
        match p:
            case Module(body):
                # breakpoint()
                for s in body:
                    # breakpoint()
                    match s:
                        case FunctionDef(fun, args, stmts, dl, returns, comment):
                            new_stmts = []
                            for s in stmts:
                                new_stmts.extend(self.rco_stmt(s))
                            result.append(FunctionDef(fun, args, new_stmts, dl, returns, comment))
                result = Module(result)
            case _:
                raise Exception('interp: unexpected ' + repr(p))

        # breakpoint()
        type_check_Lany.TypeCheckLany().type_check(p)
        trace(result)
        return result


    def explicate_assign(self, rhs: expr, lhs: Variable, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                # breakpoint()
                # if lhs == Name("tmp.49"):
                #     breakpoint()
                goto_cont = create_block(cont, basic_blocks)
                body_list = self.explicate_assign(body, lhs, [goto_cont], basic_blocks)
                orelse_list = self.explicate_assign(orelse, lhs, [goto_cont], basic_blocks)
                return self.explicate_pred(test, body_list, orelse_list, basic_blocks)

            case Begin(body, result):
                # return self.explicate_assign(rhs, lhs, cont, basic_blocks)

                # new_body = [Assign([lhs], result)] + cont
                new_body = self.explicate_assign(result, lhs, cont, basic_blocks)

                for s in reversed(body):
                    # the new_body was after s we need do the new_body
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body
            case _:

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
                # print("......", e)
                return [] + cont

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Compare(left, [op], [right]):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                # breakpoint()
                # print("xxxxxxxxxx")
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

    def explicate_tail(self, exp, basic_blocks) ->  List[stmt]:
        match exp:
            case Call(Name('make_any'), args):
                return [Return(exp)]
            case Call(fun, args):
                # breakpoint()
                return [Return(TailCall(fun, args))]
            case Begin(body, result):
                the_result_stmts = self.explicate_tail(result, basic_blocks)
                for s in reversed(body):
                    the_result_stmts = self.explicate_stmt(s, the_result_stmts, basic_blocks)
                return the_result_stmts
            case IfExp(test, body, orelse):
                # TODO
                # Return
                # goto_thn = create_block(thn, basic_blocks)
                # goto_els = create_block(els, basic_blocks)
                body = self.explicate_tail(body, basic_blocks)
                orelse = self.explicate_tail(orelse, basic_blocks)
                goto_thn_out = create_block(body, basic_blocks)
                goto_els_out = create_block(orelse, basic_blocks)
                return [If(test, [goto_thn_out], [goto_els_out])]
            case _:
                # breakpoint()
                return [Return(exp)]

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
            case Collect(size):
                return [s] + cont
            case Return(value):
                # return always the last
                return self.explicate_tail(value, basic_blocks)
            # case Expr(Call(Name('print'), [arg])):
            #     return [s] + cont

    def explicate_control(self, p):
        result = []

        match p:
            case Module(body):
                for s in body:
                    # breakpoint()
                    match s:
                        case FunctionDef(fun, args, stmts, dl, returns, comment):

                            basic_blocks = {}
                            conclusion = []
                            conclusion.extend([
                                #Return(Constant(0)),
                            ])
                            basic_blocks[label_name("{}conclusion".format(fun))] = conclusion

                            # blocks[self.sort_cfg[-1]][-1] = Jump(label_name("conclusion"))
                            new_body = [Goto(label_name("{}conclusion".format(fun)))]
                            # 也许这里是一个 newblock conclude = block(Return(Constant(0))])
                            # create_block 是 goto 那个 bloc
                            # conclude 这里是从那里 goto 到这里

                            for s in reversed(stmts):
                                # the new_body was after s we need do the new_body
                                new_body = self.explicate_stmt(s, new_body, basic_blocks)
                            basic_blocks[label_name('{}start'.format(fun))] = new_body
                            result.append(FunctionDef(fun, args, basic_blocks, dl, returns, comment))

        # f = interp_Cif.InterpCif().interp
        # breakpoint()
        result = CProgramDefs(result)
        return result

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        match e:
            case Name(name):
                return Variable(name)
            case GlobalValue(name):
                return x86_ast.Global(name)
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Constant(value):
                return Immediate(value)
            case Uninitialized(ty):
                return Immediate(0)
            # case FunRef(name, arith):
            #     # breakpoint()
            #     return Instr('leaq', [x86_ast.Global(name),])
            # case x if isinstance(x, int):
            #     return Immediate(x)
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
                    JumpIf(op_dict[str(op)], then_label),
                    Jump(else_label)
                    # Instr('jmp', [else_label])
                ]
            case Name(id):
                x = self.select_arg(expr)
                y = Immediate(1)
                # the result == 1 ?
                return [
                    Instr('cmpq', [y, x]),
                    JumpIf(op_dict["=="], then_label),
                    Jump(else_label)
                ]
            case _:
                breakpoint()
                raise Exception("no match {} ".format(expr))

    def select_stmt(self, s: stmt) -> List[instr]:
        # YOUR CODE HERE
        result = []
        match s:
            case Assign([Subscript(tu, slice, ctx)], Call(Name('make_any'), [value, Constant(tag)])):
                tu = self.select_arg(tu)
                slice = self.select_arg(slice)
                result.append(Instr('movq', [tu, Reg('r11')]))
                # Deref('r11', 8 * (slice.value + 1)) is the left
                # result.append(Instr('movq', [value, Deref('r11', 8 * (slice.value + 1))]))

                value = self.select_arg(value)
                if tag in (1, 4):
                    result.append(Instr('movq', [value, Deref('r11', 8 * (slice.value + 1))]))
                    result.append(Instr('salq', [Immediate(3), Deref('r11', 8 * (slice.value + 1))]))
                    result.append(Instr('orq', [Immediate(tag), Deref('r11', 8 * (slice.value + 1))]))
                else:
                    result.append(Instr('movq', [value, Deref('r11', 8 * (slice.value + 1))]))
                    result.append(Instr('orq', [Immediate(tag), Deref('r11', 8 * (slice.value + 1))]))

            case Assign([lhs], Call(Name('any_len'), [value])):
                left = self.select_arg(lhs)
                value = self.select_arg(value)
                result.append(Instr('movq', [Immediate(-8), Reg("r11")]))
                result.append(Instr('andq', [value, Reg("r11")]))
                result.append(Instr('movq', [Deref('r11', 0), Reg('r11')]))
                result.append(Instr('andq', [Immediate(126), Reg("r11")]))
                result.append(Instr('sarq', [Immediate(1), Reg("r11")]))
                result.append(Instr('movq', [ Reg("r11"), left]))
            case Assign([lhs], Call(Name('any_tuple_load_unsafe'), [e1, e2])):
                left = self.select_arg(lhs)
                e1 = self.select_arg(e1)
                e2 = self.select_arg(e2)
                result.append(Instr('movq', [Immediate(-8), Reg("r11")]))
                result.append(Instr('andq', [e1, Reg("r11")]))
                result.append(Instr('movq', [e2, Reg('rax')]))
                result.append(Instr('andq', [Immediate(1), Reg("rax")]))
                result.append(Instr('imulq', [Immediate(8), Reg("r11")]))
                result.append(Instr('movq', [ Deref("r11", 0), left]))
            case Assign([lhs], Call(Name('make_any'), [value, Constant(tag)])):

                left = self.select_arg(lhs)
                value = self.select_arg(value)
                if tag in (1, 4):
                    result.append(Instr('movq', [value, left]))
                    result.append(Instr('salq', [Immediate(3), left]))
                    result.append(Instr('orq', [Immediate(tag), left]))
                else:
                    result.append(Instr('movq', [value, left]))
                    result.append(Instr('orq', [Immediate(tag), left]))
            case Assign([lhs], TagOf(e)):
                left = self.select_arg(lhs)
                value = self.select_arg(e)
                result.append(Instr('movq', [value, left]))
                result.append(Instr('andq', [Immediate(7), left]))
            case Assign([lhs], ValueOf(e, ty)):
                left = self.select_arg(lhs)
                value = self.select_arg(e)
                # how should I now this is BoolType
                if isinstance(ty, IntType) or isinstance(ty, BoolType):
                    result.append(Instr('movq', [value, left]))
                    result.append(Instr('sarq', [Immediate(3), left]))
                else:
                    result.append(Instr('movq', [Immediate(-8), left]))
                    result.append(Instr('andq', [value, left]))

            case Expr(Call(Name('print'), [arg])):
                arg = self.select_arg(arg)
                # need print can be any... so need valueOf
                # at now we thint it is int
                # TODO how to make print can pass type check
                result.append(Instr('sarq', [Immediate(3), arg]))

                result.append(Instr('movq', [arg, Reg("rdi")]))
                result.append(Callq(label_name("print_int"), 1))
            case Assign([lhs], Call(Name('input_int'), [])):
                lhs = self.select_arg(lhs)
                result.append(Callq(label_name("read_int"), 0))
                result.append(Instr('movq', [Reg('rax'), lhs]))
            case Assign([lhs], Call(Name('exit'), [])):
                # lhs = self.select_arg(lhs)
                result.append(Callq(label_name("exit"), 0))
            case Assign([lhs], Call(Name('arity'), [arg])):
                lhs = self.select_arg(lhs)
                arg = self.select_arg(arg)
                result.append(Instr('movq', [arg, Reg("r11")]))
                result.append(Instr('movq', [Deref('r11', 0), lhs]))
                result.append(Instr('sarq', [Immediate(57), lhs]))
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
                    # breakpoint()
                    result.append(Instr('movq', [left_arg, lhs]))
                    result.append(Instr('subq', [right_arg, lhs]))
            case Assign([lhs], FunRef(name, arith)):
                # breakpoint()
                lhs = self.select_arg(lhs)
                # breakpoint()
                result.append(Instr('leaq', [x86_ast.Global("{}".format(name)), lhs]))
            case Assign([lhs], UnaryOp(USub(), v)):
                arg = self.select_arg(v)
                lhs = self.select_arg(lhs)
                if arg == lhs:
                    result.append(Instr('negq', [lhs]))
                else:
                    result.append(Instr('movq', [arg, lhs]))
                    result.append(Instr('negq', [lhs]))
            # TODO add a call Name('arith')
            case Assign([Subscript(tu, slice, ctx)], value):
                tu = self.select_arg(tu)
                slice = self.select_arg(slice)
                result.append(Instr('movq', [tu, Reg('r11')]))
                value = self.select_arg(value)
                result.append(Instr('movq', [value, Deref('r11', 8 * (slice.value + 1))]))

            case Assign([lhs], Call(fun, args)):
                # breakpoint()
                lhs = self.select_arg(lhs)
                for i, arg in enumerate(args):
                    arg = self.select_arg(arg)
                    result.append(Instr('movq', [arg, arg_regs[i]]))
                # here cost my 1hour to findoutout
                fun = self.select_arg(fun)
                result.append(IndirectCallq(fun, len(args)))

                result.append(Instr('movq', [Reg('rax'), lhs]))
            case Return(TailCall(fun, args)):
                # breakpoint()
                # lhs = self.select_arg(lhs)
                fun = self.select_arg(fun)
                for i, arg in enumerate(args):
                    arg = self.select_arg(arg)
                    result.append(Instr('movq', [arg, arg_regs[i]]))
                result.append(TailJump(fun, len(args)))
                # result.append(Instr('movq', [Reg('rax'), lhs]))
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
            case Assign([lhs], Call(Name('len'), [arg])):
                arg = self.select_arg(arg)
                result.append(Instr('movq', [arg, Reg('r11')]))
                result.append(Instr('movq', [Deref('r11', 0), Reg('r11')]))
                result.append(Instr('andq', [Immediate(126), Reg('r11')]))
                result.append(Instr('sarq', [Immediate(1), Reg('r11')]))
                result.append(Instr('sarq', [Reg('r11'), lhs]))

            case Assign([lhs], Subscript(value, slice, ctx)):
                lhs = self.select_arg(lhs)
                value = self.select_arg(value)
                slice = self.select_arg(slice)  # slice must be int 这里没有必要
                result.append(Instr('movq', [value, Reg('r11')]))
                result.append(Instr('movq', [Deref('r11', 8 * (slice.value + 1)), lhs]))

            case Assign([lhs], Allocate(size, ty)):
                lhs = self.select_arg(lhs)

                # size = self.select_arg(size)
                tag = calculate_tag(size, ty)
                result.append(Instr("movq", [x86_ast.Global("free_ptr"), Reg('r11')]))
                result.append(Instr("addq", [Immediate(8 * (size + 1)),  x86_ast.Global("free_ptr")]))
                result.append(Instr("movq", [Immediate(tag), Deref('r11', 0)]))
                result.append(Instr('movq', [Reg('r11'), lhs]))
            case Assign([lhs], AllocateClosure(size, ty, arith)):
                lhs = self.select_arg(lhs)

                # size = self.select_arg(size)
                tag = calculate_tag(size, ty, arith=arith)
                result.append(Instr("movq", [x86_ast.Global("free_ptr"), Reg('r11')]))
                result.append(Instr("addq", [Immediate(8 * (size + 1)),  x86_ast.Global("free_ptr")]))
                result.append(Instr("movq", [Immediate(tag), Deref('r11', 0)]))
                result.append(Instr('movq', [Reg('r11'), lhs]))
            case Assign([lhs], value):
                lhs = self.select_arg(lhs)
                arg = self.select_arg(value)
                result.append(Instr('movq', [arg, lhs]))
            # case Return(Constant(value)):
            #     result.append(Instr('movq', [self.select_arg(Constant(value)), Reg('rax')]))
            #     result.append(Instr('retq', []))
            case Goto(label):
                result.append(Jump(label))

            case If(expr, [Goto(then_label)], [Goto(else_label)]):
                # expr can be valueof
                if_ = self.select_compare(expr, then_label, else_label)
                result.extend(if_)

            case Collect(size):
                # size = self.select_arg(size)
                result.append(Instr('movq', [Reg('r15'), Reg('rdi')]))
                result.append(Instr('movq', [Immediate(size), Reg('rsi')]))
                result.append(Callq(label_name("collect"), 2))
            case Return(Call(Name('make_any'), [value, Constant(tag)])):

                value = self.select_arg(value)
                if tag in (1, 4):
                    result.append(Instr('movq', [value, Reg('rax')]))
                    result.append(Instr('salq', [Immediate(3), Reg('rax')]))
                    result.append(Instr('orq', [Immediate(tag), Reg('rax')]))
                else:
                    result.append(Instr('movq', [value, Reg('rax')]))
                    result.append(Instr('orq', [Immediate(tag), Reg('rax')]))
                result.append(Jump(self.tmp_concluation))
            case Return(value):
                value = self.select_arg(value)
                result.append(Instr('movq', [value, Reg('rax')]))
                result.append(Jump(self.tmp_concluation))
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))
        return result
        pass        

    def select_instructions(self, p: Module) -> X86Program:
        # YOUR CODE HERE
        type_check_Clambda.TypeCheckClambda().type_check(p)
        # breakpoint()
        # arg_regs
        result = []
        match p:
            case CProgramDefs(cdefs):
                for cdef in cdefs:
                    match cdef:
                        case FunctionDef(fun, args, basic_blocks, dl, returns, comment):
                            blocks = {}
                            args_start = []
                            self.tmp_concluation = label_name("{}conclusion".format(fun))
                            for i, arg in enumerate(args):
                                args_start.append(Instr('movq', [arg_regs[i], Variable(arg[0])]))

                            for label, body in basic_blocks.items():
                                instr_body = []
                                for s in body:
                                    instr_body.extend(self.select_stmt(s))
                                blocks[label] = instr_body

                            blocks[label_name('{}start'.format(fun))] = args_start + blocks[label_name('{}start'.format(fun))]
                            # for only test
                            blocks[label_name('{}'.format(fun))] = [Jump(label_name('{}start'.format(fun)))]

                            ndef = FunctionDef(fun, [], blocks, dl, returns, comment)

                            ndef.var_types = cdef.var_types
                            result.append(ndef)

                        case _:
                            raise Exception('interp: unexpected ' + repr(p))

        x86 = X86ProgramDefs(result)
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
            case Instr(cmpq, [s, Variable(t)]):
                return {i.args[1]}
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

    def free_var(self, t):
        match(t):
            case Variable(i):
                return t
            case Reg(r):
                return t
            case Deref(r, offset):
                return Reg(r)
            case TailJump(func, n):
                return arg_regs[:n]
            case IndirectCallq(func, n):
                return arg_regs[:n]
            case _:
                return set()

    def write_var(self, i) -> Set[location]:
        match (i):
            case Instr("movq", [s, t]):
                if r := self.free_var(t):
                    return set([r])
                else:
                    return set()
            case Instr("subq", [s, t]):
                if r := self.free_var(t):
                    return set([r])
                else:
                    return set()
            case Instr("addq", [s, t]):
                # breakpoint()
                if r := self.free_var(t):
                    return set([r])
                else:
                    return set()
            case Callq(func, num_args):
                return set(caller_saved_regs)
            case IndirectCallq(func, num_args):
                return set(caller_saved_regs)
            case Instr('leaq', [s, t]):
                return set([self.free_var(t)])
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


    def transfer(self,label, live_after_block):
        ss = self.blocks[label]
        after_instr_set = live_after_block  # the set after the block
        live_before_block = set()
        if not ss:
            return set()
        self.live_after[ss[-1]] = after_instr_set
        s = ss[-1]
        match s:
            # jump 到别处 通过的是 input 来传岛的
            case Jump(label):
                before_instr_set = live_after_block
            case JumpIf(cc, label):
                tmp = (self.live_after[s] - self.write_var(s)).union(self.read_var(s))
                before_instr_set = tmp.union(live_after_block)
            case _:
                before_instr_set = (self.live_after[s] - self.write_var(s)).union(self.read_var(s))

        pre_instr = ss[-1]
        self.live_before[pre_instr] = before_instr_set
        live_before_block = live_before_block.union(before_instr_set)

        for s in list(reversed(ss))[1:]:
            self.live_after[s] = self.live_before[pre_instr]
            match s:
                # jump 到别处 通过的是 input 来传岛的
                case Jump(label):
                    before_instr_set = live_after_block
                case JumpIf(cc, label):
                    tmp = (self.live_after[s] - self.write_var(s)).union(self.read_var(s))
                    before_instr_set = tmp.union(live_after_block)
                case _:
                    before_instr_set = (self.live_after[s] - self.write_var(s)).union(self.read_var(s))
            # print("s" , s, before_instr_set)
            self.live_before[s] = before_instr_set
            live_before_block = live_before_block.union(before_instr_set)
            pre_instr = s
            # self.live_after[s] = pre_instr_set.union(self.live_after.get(s, set()))

        # pre_instr_set = (pre_instr_set - self.write_var(pre_instr)).union(self.read_var(pre_instr))
        # print("after_set ", pre_instr_set)
        # live_before_block = live_before_block.union(pre_instr_set)
        return live_before_block


    def analyze_dataflow(self, G, transfer, bottom, join):
        trans_G = transpose(G)
        mapping = dict((v, bottom) for v in G.vertices())
        worklist = deque(G.vertices())
        debug = {}
        while worklist:
            # print(worklist)
            node = worklist.pop()
            inputs = [mapping[v] for v in trans_G.adjacent(node)]
            input = reduce(join, inputs, bottom)
            output = transfer(node, input)
            # print("node", node, "input", input, "output", output)
            if output != mapping[node]:
                worklist.extend(G.adjacent(node))
                mapping[node] = output
            else:
                debug[node] = output
        return debug

    def build_interference(self, blocks) -> UndirectedAdjList:
        cfg = UndirectedAdjList()
        for label, body in blocks.items():
            for i in body:
                if isinstance(i, Jump) or isinstance(i, JumpIf):
                    # breakpoint()
                    cfg.add_edge(label, i.label)

        t_cfg = transpose(cfg)
        interference_graph = UndirectedAdjList()
        # self.sort_cfg = topological_sort(cfg)
        live_before_block = {}
        self.live_after = {}
        self.live_before = {}
        self.live_before_block = {}
        self.blocks = blocks
        debug = self.analyze_dataflow(cfg, self.transfer, set(), lambda x,y: x|y)
        # breakpoint()
        # for label in reversed(self.sort_cfg):
        #     ss = blocks[label]
        #     tmp = self.uncover_live(ss, live_before_block)
        #     # live update bind instr with
        #     # flow 分析解决的是 block 的分析问题。
        #     # 在解决 block 的
        #     live_before_block[label] = tmp[ss[0]]
        #     live_after.update(tmp)

        # print("live_after ", self.live_after)
        for label, ss in blocks.items():
            for s in ss:
                match (s):
                    case Instr("movq", [si, d]):
                        # si = s.args[0]
                        d = self.free_var(d)
                        for v in self.live_after[s]:
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
                            for v in self.live_after[s]:
                                if v != d:
                                    interference_graph.add_edge(d, v)
        return interference_graph

    #def color_graph(self, ss: List[instr], k=100) -> Dict[location, int]:
    def color_graph(self, blocks, k=100) -> Dict[location, int]:
        # first make it k big enough
        valid_colors = list(range(0, k))  # number of colar
        # Rdi 的保存问题
        # arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]
        color_map = {
            Reg('rax'): -1, Reg('rsp'): -2, Reg('rdi'): -3, ByteReg('bl'): -4, Reg('r11'): -5,
            Reg('r15'): -6, Reg('rsi'): -7 ,# rsi 其实可以用来做其他事情。 但如果分配 rsi 9  rsi 的 color
            # 算法 color 9 和 可以分配出去reg 的color 0 1 3 矛盾
            Reg('rdx'): -8,  Reg('rcx'): -9,  Reg('r8'): -10,  Reg('r9'): -11
        }
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
            # print("handing", u)

            adj_colors = {color_map[v] for v in interference_graph.adjacent(u) if v in color_map}
            # print(u, adj_colors)
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
        # exit()
        # breakpoint()
        # ? RDI


        match(p):
            case X86ProgramDefs(defs):

                # breakpoint()
                for cdef in defs:
                    cdef.color_regs = [Reg("rbx"), Reg("rcx"), Reg("rdx"), Reg("rsi"),
                                       Reg("rdi"), Reg("r8"), Reg("r9"), Reg("r10")]
                    cdef.color_regs = [Reg("rbx"), Reg("rcx")]
                    cdef.color_regs = [Reg("rbx")]
                    # rcx as tmp
                    cdef.color_regs = [Reg("rbx"), Reg("r10")]

                    cdef.alloc_callee_saved_regs = list(set(cdef.color_regs).intersection(callee_saved_regs))
                    cdef.C = len(cdef.alloc_callee_saved_regs)
                    # used_regs = 1
                    color_regs_map = {i: reg for i, reg in enumerate(cdef.color_regs)}
                    color_regs_map[-1] = Reg('rax')
                    color_regs_map[-2] = Reg('rsp')
                    color_regs_map[-3] = Reg('rdi')
                    color_regs_map[-4] = ByteReg("bl")
                    color_regs_map[-5] = Reg('r11')
                    color_regs_map[-6] = Reg('r15')
                    color_regs_map[-7] = Reg('rsi')

                    color_regs_map[-8] = Reg('rdx')
                    color_regs_map[-9] = Reg('rcx')
                    color_regs_map[-10] = Reg('r8')
                    color_regs_map[-11] = Reg('r9')
                    # arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]

                    cdef.real_color_map = {}
                    blocks = cdef.body

                    new_blocks = {}
                    color_map = self.color_graph(blocks)

                    # print("color_map", color_map)
                    so_far_rbp = 0
                    so_far_r15 = 0
                    cdef.rbp_spill = set()
                    cdef.r15_spill = set()
                    for var, color in sorted(color_map.items(), key=lambda i: i[1]):
                        # 相同的 color 但 type 不一样
                        if color in cdef.real_color_map:
                            continue
                        if color in color_regs_map:
                            cdef.real_color_map[color] = color_regs_map[color]
                        else:
                            # Yes
                            # breakpoint()
                            if isinstance(cdef.var_types.get(str(var)), TupleType):
                                # breakpoint()
                                # r15 is up r15 was saveid in heap
                                cdef.real_color_map[color] = Deref("r15", 8*(so_far_r15))
                                so_far_r15 += 1
                                cdef.r15_spill.add(color)
                            else:
                                cdef.real_color_map[color] = Deref("rbp", -8*(so_far_rbp + cdef.C + 1))
                                so_far_rbp += 1
                                cdef.rbp_spill.add(color)

                    cdef.S = len(cdef.rbp_spill)
                    if cdef.r15_spill.intersection(cdef.rbp_spill):
                        # print("r15 and rbp have somecolor", )
                        sys.exit(-1)

                    # print("real_color_map", cdef.real_color_map)

                    for label, ss in blocks.items():
                        ss = blocks[label]
                        result = []
                        for s in ss:
                            match(s):
                                case Instr(op, [source, target]):
                                    # breakpoint()
                                    if (color := color_map.get(source)) is not None:
                                        source = cdef.real_color_map[color]
                                    if (color := color_map.get(target)) is not None:
                                        target = cdef.real_color_map[color]
                                    result.append(Instr(op, [source, target]))
                                case Instr(op, [source]):
                                    if (color := color_map.get(source)) is not None:
                                        source = cdef.real_color_map[color]
                                    result.append(Instr(op, [source]))
                                case Callq(fun, args):
                                    if (color := color_map.get(fun)) is not None:
                                        fun = cdef.real_color_map[color]
                                    # for i in range(len(args)):
                                    #     if (color := color_map.get(args[i])) is not None:
                                    #         args[i] = cdef.real_color_map[color]

                                    result.append(Callq(fun, args))
                                case IndirectCallq(fun, args):
                                    if (color := color_map.get(fun)) is not None:
                                        fun = cdef.real_color_map[color]
                                    # for i in range(len(args)):
                                    #     if (color := color_map.get(args[i])) is not None:
                                    #         args[i] = cdef.real_color_map[color]

                                    result.append(IndirectCallq(fun, args))
                                case TailJump(fun, args):
                                    if (color := color_map.get(fun)) is not None:
                                        fun = cdef.real_color_map[color]
                                    # for i in range(len(args)):
                                    #     if (color := color_map.get(args[i])) is not None:
                                    #         args[i] = cdef.real_color_map[color]

                                    result.append(TailJump(fun, args))
                                case _:
                                    result.append(s)
                        new_blocks[label] = result
                        cdef.body = new_blocks
                        cdef.rsp_sub = align(8 * cdef.S + 8 * cdef.C, 16) - 8 * cdef.C

        # 执行需要提前把这些 save 好
        match(p):
            case X86ProgramDefs(defs):
                # breakpoint()
                for cdef in defs:

                    self.cdef = cdef
                    cdef.len_spill_r15 = len(cdef.r15_spill)
                    cdef.extra_saved_regs = list(set(cdef.alloc_callee_saved_regs) - {Reg("rbp")})


                    for label, stmts in cdef.body.items():
                        result = self.patch_instrs(stmts)
                        cdef.body[label] = result


                    start = []
                    start.extend([
                        Instr("pushq", [Reg("rbp")]),
                        Instr("movq", [Reg("rsp"), Reg("rbp")]),

                    ])
                    # save
                    for reg in cdef.extra_saved_regs:
                        start.append(Instr("pushq", [reg]))
                    start.extend([Instr("subq", [Immediate(cdef.rsp_sub), Reg("rsp")])])
                    if cdef.name == 'main':
                        start.extend([
                            Instr("movq", [Immediate(65536), Reg("rdi")]),
                            Instr("movq", [Immediate(65536), Reg("rsi")]),
                            Callq(label_name("initialize"), 2),
                            Instr("movq", [x86_ast.Global("rootstack_begin"), Reg("r15")]),
                        ])

                    for i in range(cdef.len_spill_r15):
                        start.append(Instr("movq", [Immediate(0), Deref("r15", 8 * i)]))
                    start.append(Instr('addq', [Immediate(8 * cdef.len_spill_r15), Reg('r15')]))
                    start.append(Jump(label_name("{}start".format(cdef.name))))

                    cdef.body[label_name('{}'.format(cdef.name))] = start
                    # for label , body in blocks.items():
                    #     pass
                    conclusion = []
                    conclusion.extend([
                        Instr("subq", [Immediate(8 * cdef.len_spill_r15), Reg("r15")]),
                        Instr("addq", [Immediate(cdef.rsp_sub), Reg("rsp")]),
                    ])
                    for reg in cdef.extra_saved_regs[::-1]:
                        conclusion.append(Instr("popq", [reg]))
                    conclusion.append(Instr("popq", [Reg('rbp')]))  # seem no need pop
                    conclusion.append(Instr("retq", []))
                    # just replace
                    cdef.body[label_name('{}conclusion'.format(cdef.name))] = conclusion + \
                        cdef.body[label_name('{}conclusion'.format(cdef.name))]
                    # for rbp save
                    # call itelf need be update


        return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match(i):
            case Instr(instr, [x, y]) if x == y:
                return []
            case Instr(instr, [Deref(label_x, x), Deref(label_y, y)]):
                return [
                    Instr("movq", [Deref(label_x, x), Reg("rax")]),
                    Instr(instr, [Reg("rax"), Deref(label_y, y)])
                ]
            case TailJump(func, arg):
                conclusion = []
                conclusion.extend([
                    Instr("subq", [Immediate(8 * self.cdef.len_spill_r15), Reg("r15")]),
                    Instr("addq", [Immediate(self.cdef.rsp_sub), Reg("rsp")]),
                ])
                for reg in self.cdef.extra_saved_regs[::-1]:
                    conclusion.append(Instr("popq", [reg]))
                conclusion.append(Instr("popq", [Reg('rbp')]))  # seem no need pop

                # func may be need rbp and rbp was pop
                return [Instr("movq", [func, Reg("rax")])]  + conclusion + [
                    # Instr('jmp', [Reg("rax")])
                    TailJump(Reg('rax'), arg)
                ]
                # breakpoint()
            case Instr('leaq', [x, Deref(label_y, y)]):
                return [
                    Instr("leaq", [x, Reg("rax")]),
                    Instr("movq", [Reg("rax"), Deref(label_y, y)]),

                ]
            case Instr(instr, [x86_ast.Global(x), Deref(label_y, y)]):
                return [
                    Instr("movq", [x86_ast.Global(x), Reg("rax")]),
                    Instr("movq", [Reg("rax"), Deref(label_y, y)])
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
            case Instr('movq', [Immediate(n), Deref(x, y)]) if n > 4294967296:
                return [
                    Instr("movq", [Immediate(n), Reg("rax")]),
                    Instr("movq", [Reg("rax"), Deref(x, y)])
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
        return p


    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        result = {}
        match (p):
            case X86ProgramDefs(defs):
                # breakpoint()
                for cdef in defs:
                    result.update(cdef.body)
        return X86Program(result)