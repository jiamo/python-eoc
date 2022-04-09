import os
import sys
import compiler
import interp_Pvar
import interp_Lvar
import interp_Lif
import interp_Lwhile
import interp_Ldyn
import interp_Lany
import interp_Ltup
import interp_Lfun
import interp_Llambda
import type_check_Pvar
import type_check_Lvar
import type_check_Lfun
import type_check_Clambda
import interp_Cif
import interp_Ctup
import interp_Cfun
import interp_Clambda
import interp_Cany

import type_check_Lif

from interp_x86.eval_x86 import interp_x86
from utils import run_tests, run_one_test


compiler = compiler.Compiler()
type_check_dict = {
    "var": type_check_Lvar.TypeCheckLvar().type_check,
    "cond": type_check_Lif.TypeCheckLvar().type_check,
}
interp_dict = {
    # "var": interp_Lvar.InterpLvar().interp,
    # "cond": interp_Lif.InterpLif().interp,
    # "while": interp_Lwhile.InterpLwhile().interp,
    # "tuple": interp_Ltup.InterpLtup().interp,
    # "fun": interp_Lfun.InterpLfun().interp,
    # "lambda": interp_Llambda.InterpLlambda().interp,
    "dyn":  interp_Ldyn.InterpLdyn().interp,
    "shrink": interp_Ldyn.InterpLdyn().interp,
    "uniquify": interp_Ldyn.InterpLdyn().interp,
    "reveal_functions": interp_Ldyn.InterpLdyn().interp,
    "cast_insert": interp_Lany.InterpLany().interp,
    "reveal_casts": interp_Lany.InterpLany().interp,
    "convert_assignments": interp_Lany.InterpLany().interp,
    "convert_to_closures": interp_Lany.InterpLany().interp,
    "limit_functions": interp_Lany.InterpLany().interp,
    "expose_allocation": interp_Lany.InterpLany().interp,
    "remove_complex_operands": interp_Lany.InterpLany().interp,
    "explicate_control": interp_Cany.InterpCany().interp,
    "select_instructions": interp_x86,
    "assign_homes": interp_x86,
    "patch_instructions": interp_x86,
    "prelude_and_conclusion": interp_x86,
    "allocate_registers": interp_x86,
}

if len(sys.argv) == 2:
    one_test_file = sys.argv[1]
    run_one_test(one_test_file, 'dyn',
                 compiler, 'dyn',
                 #type_check_Pvar.TypeCheckPvar().type_check_P,
                 type_check_dict,
                 # interp_Pvar.InterpPvar().interp_P,
                 interp_dict,
                 )
else:
    run_tests('cond', compiler, 'cond',
              # type_check_Pvar.TypeCheckPvar().type_check_P,
              type_check_dict,
              # interp_Pvar.InterpPvar().interp_P,
              interp_dict,
              )

