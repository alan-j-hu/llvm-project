#!/bin/sh

set -e
set -x

if test "$(dirname $0)" != '.'; then
    echo "The script must be executed from its current directory."
    exit 1
fi

if test "$#" -ne 1; then
    echo "Usage: $0 <llvm-config>"
    exit 1
fi

llvm_config=$1
default_mode=
support_static_mode=false
support_shared_mode=false

llvm_config() {
    "$llvm_config" $@
}

llvm_version=$(llvm_config --version | cut -d. -f1)
expected_version=$(cat VERSION | cut -d. -f1)
if test "$llvm_version" != "$expected_version"; then
  echo "LLVM version does not match. Expected '$expected_version' but got '$llvm_version'"
  exit 1
fi

if llvm_config --link-static --libs; then
    default_mode=static
    support_static_mode=true
fi

if llvm_config --link-shared --libs; then
    default_mode=shared
    support_shared_mode=true
fi

if test -z "$default_mode"; then
    echo "Something is wrong with the llvm-config command provided."
    exit 1
fi

base_cflags=$(llvm_config --cflags)
ldflags="$(llvm_config --ldflags) -lstdc++"
llvm_targets=$(llvm_config --targets-built)

echo "
(env
 (_ (env-vars
     (LLVM_CONFIG $llvm_config)
     (LLVM_SHARED_AVAILABLE $support_shared_mode)
     (LLVM_STATIC_AVAILABLE $support_static_mode))
    (binaries (discover.sh as discover.sh))
    (c_flags $base_cflags)))
" > "dune"
