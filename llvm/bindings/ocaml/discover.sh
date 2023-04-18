#!/bin/sh

set -e
set -x

echo "($($LLVM_CONFIG $@))" > "c_library_flags.sexp"
