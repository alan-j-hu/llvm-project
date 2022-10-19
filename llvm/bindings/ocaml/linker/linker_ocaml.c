/*===-- linker_ocaml.c - LLVM OCaml Glue ------------------------*- C++ -*-===*\
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

#include "llvm-c/Core.h"
#include "llvm-c/Linker.h"
#include "caml/alloc.h"
#include "caml/memory.h"
#include "caml/fail.h"
#include "caml/callback.h"
#include "llvm_ocaml.h"

void llvm_raise(value Prototype, char *Message);

/* llmodule -> llmodule -> unit */
value llvm_link_modules(value Dst, value Src) {
  CAMLparam2(Dst, Src);
  if (LLVMLinkModules2(Module_val(Dst), Module_val(Src)))
    llvm_raise(*caml_named_value("Llvm_linker.Error"),
               LLVMCreateMessage("Linking failed"));

  CAMLreturn(Val_unit);
}
