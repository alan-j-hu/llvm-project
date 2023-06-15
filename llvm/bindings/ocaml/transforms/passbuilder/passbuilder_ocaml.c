/*===-- passbuilder_ocaml.c - LLVM OCaml Glue -------------------*- C++ -*-===*\
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

#include "llvm_ocaml.h"
#include "target_ocaml.h"
#include "llvm-c/Transforms/PassBuilder.h"
#include <caml/memory.h>

#define PassBuilderOptions_val(v) ((LLVMPassBuilderOptionsRef)from_val(v))

value llvm_create_passbuilder_options(value Unit) {
  LLVMPassBuilderOptionsRef PBO = LLVMCreatePassBuilderOptions();
  return to_val(PBO);
}

value llvm_dispose_passbuilder_options(value PBO) {
  LLVMDisposePassBuilderOptions(PassBuilderOptions_val(PBO));
  return Val_unit;
}

value llvm_run_passes(value M, value Passes, value TM, value Options) {
  CAMLparam1(TM);
  LLVMErrorRef E =
      LLVMRunPasses(Module_val(M), String_val(Passes), TargetMachine_val(TM),
                    PassBuilderOptions_val(Options));
  if (E == NULL) {
    value ok = caml_alloc(1, 0);
    Store_field(ok, 0, Val_unit);
    return ok;
  } else {
    value error = caml_alloc(1, 1);
    Store_field(error, 0, to_val(E));
    return error;
  }
}
