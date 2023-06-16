/*===-- target_ocaml.h - LLVM OCaml Glue ------------------------*- C++ -*-===*\
|*                                                                            *|
|* Part of the LLVM Project, under the Apache License v2.0 with LLVM          *|
|* Exceptions.                                                                *|
|* See https://llvm.org/LICENSE.txt for license information.                  *|
|* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception                    *|
|*                                                                            *|
|*===----------------------------------------------------------------------===*|
|*                                                                            *|
|* This file glues LLVM's OCaml interface to its C interface. These functions *|
|* are by and large transparent wrappers to the corresponding C functions.    *|
|*                                                                            *|
|* Note that these functions intentionally take liberties with the CAMLparamX *|
|* macros, since most of the parameters are not GC heap objects.              *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/

#include "error_ocaml.h"
#include <caml/memory.h>

value error_to_result(LLVMErrorRef Err) {
  if (Err == LLVMErrorSuccess) {
    value result = caml_alloc(1, 0);
    Store_field(result, 0, Val_unit);
    return result;
  } else {
    value result = caml_alloc(1, 1);
    Store_field(result, 0, to_val(Err));
    return result;
  }
}

value llvm_create_string_error(value ErrMsg) {
  LLVMErrorRef Err = LLVMCreateStringError(String_val(ErrMsg));
  return to_val(Err);
}

value llvm_get_error_message(value Err) {
  char *str = LLVMGetErrorMessage(Error_val(Err));
  value v = caml_copy_string(str);
  LLVMDisposeErrorMessage(str);
  return v;
}
