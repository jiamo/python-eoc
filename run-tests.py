import os
import sys
import compiler
import interp_Pvar
import interp_Lvar
import type_check_Pvar
import type_check_Lvar
from interp_x86.eval_x86 import interp_x86
from utils import run_tests, run_one_test


compiler = compiler.Compiler()
type_check_dict = {
    "var": type_check_Lvar.TypeCheckLvar().type_check
}
interp_dict = {
    "var": interp_Lvar.InterpLvar().interp,
    "remove_complex_operands": interp_Lvar.InterpLvar().interp,
    "select_instructions": interp_x86,
    "assign_homes": interp_x86,
    "patch_instructions": interp_x86,
    "prelude_and_conclusion": interp_x86,
    "allocate_registers": interp_x86,
}

if len(sys.argv) == 2:
    one_test_file = sys.argv[1]
    run_one_test(one_test_file, 'var',
                 compiler, 'var',
                 #type_check_Pvar.TypeCheckPvar().type_check_P,
                 type_check_dict,
                 # interp_Pvar.InterpPvar().interp_P,
                 interp_dict,
                 )
else:
    run_tests('var', compiler, 'var',
              # type_check_Pvar.TypeCheckPvar().type_check_P,
              type_check_dict,
              # interp_Pvar.InterpPvar().interp_P,
              interp_dict,
              )

