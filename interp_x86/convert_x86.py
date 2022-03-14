# Convert from the x86 AST classes defined in utils.py into the parse
# tree format used by the interpreter.

from lark import Tree
from ast import Name, Constant
from x86_ast import *
from utils import label_name, GlobalValue, trace

def convert_int(value):
    if value >= 0:
        return Tree('int_a', [Tree('int_a', [value])])
    else:
        return Tree('neg_a', [Tree('int_a', [- value])])

def convert_arg(arg):
    match arg:
        case Reg(id):
            return Tree('reg_a', [id])
        case Variable(id):
            return Tree('var_a', [id])
        case Immediate(value):
            return convert_int(value)
        case Deref(reg, offset):
            return Tree('mem_a', [convert_int(offset), reg])
        case ByteReg(id):
            return Tree('reg_a', [id])
        case Global(id):
            return Tree('global_val_a', [id, 'rip'])
        case x if isinstance(x, str):
            return x
        case _:
            raise Exception('convert_arg: unhandled ' + repr(arg))

def convert_instr(instr):
    match instr:
        case Instr(instr, args):
            # trace("convert.... {} {}".format( instr, args))
            return Tree(instr, [convert_arg(arg) for arg in args])
        case Callq(func, args):
            return Tree('callq', [convert_arg(func)])
        case IndirectCallq(func, args):
            return Tree('indirect_callq', [convert_arg(func)])
        case Jump(label):
            return Tree('jmp', [label])
        case JumpIf(cc, label):
            return Tree('j' + cc, [label])
        case _:
            raise Exception('error in convert_instr, unhandled ' + repr(instr))

def convert_program(p):
    if isinstance(p, X86Program):
        if isinstance(p.body, list):
            main_instrs = [convert_instr(instr) for instr in p.body]
            main_block = Tree('block', [label_name('main')] + main_instrs)
            return Tree('prog', [main_block])
        elif isinstance(p.body, dict):
            blocks = []
            for (l, ss) in p.body.items():
                blocks.append(Tree('block',
                                   [l] + [convert_instr(instr) for instr in ss]))
            return Tree('prog', blocks)
    elif isinstance(p, X86ProgramDefs):
        blocks = []
        for cdef in p.defs:
            for (l, ss) in cdef.body.items():
                blocks.append(Tree('block',
                                   [l] + [convert_instr(instr) for instr in ss]))
        # breakpoint()
        return Tree('prog', blocks)
