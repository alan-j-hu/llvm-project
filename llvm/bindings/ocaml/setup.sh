#!/bin/sh

set -e
set -x

if test ! "$(dirname $0)" -ef '.'; then
    echo "The script must be executed from its current directory."
    exit 1
fi

if test "$#" -ne 1; then
    echo "Usage: $0 <llvm-config>"
    exit 1
fi

llvm_config() {
    "$llvm_config" $@
}

llvm_config=$1

base_cflags=$(llvm_config --cflags)
ldflags="$(llvm_config --ldflags) -lstdc++"
llvm_targets=$(llvm_config --targets-built)

echo "(" > c_flags.sexp
echo $base_cflags >> c_flags.sexp
echo ")" >> c_flags.sexp

create_library() {
    dir=$1
    components=$2

    echo "(" > $dir/c_library_flags.sexp
    echo $(llvm_config --link-shared --libs $components --ldflags) \
         > $dir/c_library_flags.sexp
    echo ")" >> $dir/c_library_flags.sexp
}

create_library "analysis" "Analysis"
create_library "bitreader" "BitReader"

create_target() {
    target=$1
    dest=generated/$target

    cflags="$base_cflags \"-DTARGET=$target\""

    mkdir -p $dest
    echo "(" > $dest/c_flags.sexp
    echo $cflags >> $dest/c_flags.sexp
    echo ")" >> $dest/c_flags.sexp
    sed s/@TARGET@/$target/g backends/dune.in > $dest/dune
    sed s/@TARGET@/$target/g backends/llvm_backend.ml.in \
        > $dest/llvm_$target.ml
    sed s/@TARGET@/$target/g backends/llvm_backend.mli.in \
        > $dest/llvm_$target.mli
    sed s/@TARGET@/$target/g backends/backend_ocaml.c > $dest/${target}_ocaml.c
}

for target in $llvm_targets; do
    touch "llvm_${target}.opam"
    create_target "$target"
done
