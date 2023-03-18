/*===-- vectorize_ocaml.c - LLVM OCaml Glue ---------------------*- C++ -*-===*\
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

#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "llvm_ocaml.h"
#include "llvm-c/Transforms/Vectorize.h"

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_vectorize(value PM) {
  LLVMAddLoopVectorizePass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_slp_vectorize(value PM) {
  LLVMAddSLPVectorizePass(PassManager_val(PM));
  return Val_unit;
}
