/*===-- ipo_ocaml.c - LLVM OCaml Glue ---------------------------*- C++ -*-===*\
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
#include "llvm-c/Transforms/IPO.h"

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_constant_merge(value PM) {
  LLVMAddConstantMergePass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_merge_functions(value PM) {
  LLVMAddMergeFunctionsPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_dead_arg_elimination(value PM) {
  LLVMAddDeadArgEliminationPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_function_attrs(value PM) {
  LLVMAddFunctionAttrsPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_function_inlining(value PM) {
  LLVMAddFunctionInliningPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_always_inliner(value PM) {
  LLVMAddAlwaysInlinerPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_global_dce(value PM) {
  LLVMAddGlobalDCEPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_global_optimizer(value PM) {
  LLVMAddGlobalOptimizerPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_prune_eh(value PM) {
  LLVMAddPruneEHPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_ipsccp(value PM) {
  LLVMAddIPSCCPPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> all_but_main:bool -> unit */
value llvm_add_internalize(value PM, value AllButMain) {
  LLVMAddInternalizePass(PassManager_val(PM), Bool_val(AllButMain));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_strip_dead_prototypes(value PM) {
  LLVMAddStripDeadPrototypesPass(PassManager_val(PM));
  return Val_unit;
}

/* [`Module] Llvm.PassManager.t -> unit */
value llvm_add_strip_symbols(value PM) {
  LLVMAddStripSymbolsPass(PassManager_val(PM));
  return Val_unit;
}
