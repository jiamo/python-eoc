#!/usr/bin/env bash

python run-tests-dyn.py tests/dyn/add.py

python run-tests-dyn.py tests/dyn/add1.py
python run-tests-dyn.py tests/dyn/add2.py
python run-tests-dyn.py tests/dyn/add4.py

python run-tests-lambda.py tests/lambda/add.py
python run-tests-lambda.py tests/lambda/add1.py
python run-tests-lambda.py tests/lambda/add2.py
python run-tests-lambda.py tests/lambda/add4.py