import os
import sys
import compiler
import interp_Pvar
import type_check_Pvar
from utils import run_tests, run_one_test


compiler = compiler.Compiler()
type_check_dict = {
    "var": type_check_Pvar
}
interp_dict = {
    "var": interp_Pvar
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

