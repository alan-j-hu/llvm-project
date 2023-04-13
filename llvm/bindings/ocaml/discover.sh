#!/bin/sh

set -e
set -x

echo "($($LLVM_CONFIG --libs $1))" > "c_library_flags.sexp"
