#python-student-support-code

Support code for students (Python version).

The `runtime.c` file needs to be compiled by doing the following
```
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named `runtime.o`. The -g flag is to tell the
compiler to produce debug information that you may need to use
the gdb (or lldb) debugger.

## https://github.com/IUCompilerCourse/IU-Fall-2021


## example one chapter for one chapter

    python run-tests-dyn.py tests/dyn/add.py
    python run-tests-lambda.py tests/lambda/add.py
    python run-tests-lambda.py tests/lambda/add1.py
    python run-tests-lambda.py tests/lambda/add2.py

##  example the higher chapter should work on low test
    python run-tests-lambda.py tests/func/add.py