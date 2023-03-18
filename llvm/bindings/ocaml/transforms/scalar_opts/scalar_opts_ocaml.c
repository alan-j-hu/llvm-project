/*===-- scalar_opts_ocaml.c - LLVM OCaml Glue -------------------*- C++ -*-===*\
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
#include "llvm-c/Transforms/Scalar.h"
#include "llvm-c/Transforms/Utils.h"

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_aggressive_dce(value PM) {
  LLVMAddAggressiveDCEPass(PassManager_val(PM));
  return Val_unit;
}

value llvm_add_dce(value PM) {
  LLVMAddDCEPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_alignment_from_assumptions(value PM) {
  LLVMAddAlignmentFromAssumptionsPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_cfg_simplification(value PM) {
  LLVMAddCFGSimplificationPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_dead_store_elimination(value PM) {
  LLVMAddDeadStoreEliminationPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_scalarizer(value PM) {
  LLVMAddScalarizerPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_merged_load_store_motion(value PM) {
  LLVMAddMergedLoadStoreMotionPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_gvn(value PM) {
  LLVMAddGVNPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_ind_var_simplify(value PM) {
  LLVMAddIndVarSimplifyPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_instruction_combining(value PM) {
  LLVMAddInstructionCombiningPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_jump_threading(value PM) {
  LLVMAddJumpThreadingPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_licm(value PM) {
  LLVMAddLICMPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_deletion(value PM) {
  LLVMAddLoopDeletionPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_idiom(value PM) {
  LLVMAddLoopIdiomPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_rotate(value PM) {
  LLVMAddLoopRotatePass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_reroll(value PM) {
  LLVMAddLoopRerollPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_loop_unroll(value PM) {
  LLVMAddLoopUnrollPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_memcpy_opt(value PM) {
  LLVMAddMemCpyOptPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_partially_inline_lib_calls(value PM) {
  LLVMAddPartiallyInlineLibCallsPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_lower_atomic(value PM) {
  LLVMAddLowerAtomicPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_lower_switch(value PM) {
  LLVMAddLowerSwitchPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_promote_memory_to_register(value PM) {
  LLVMAddPromoteMemoryToRegisterPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_reassociation(value PM) {
  LLVMAddReassociatePass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_sccp(value PM) {
  LLVMAddSCCPPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_scalar_repl_aggregates(value PM) {
  LLVMAddScalarReplAggregatesPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_scalar_repl_aggregates_ssa(value PM) {
  LLVMAddScalarReplAggregatesPassSSA(PassManager_val(PM));
  return Val_unit;
}

/* int -> [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_scalar_repl_aggregates_with_threshold(value threshold,
                                                     value PM) {
  LLVMAddScalarReplAggregatesPassWithThreshold(PassManager_val(PM),
                                               Int_val(threshold));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_simplify_lib_calls(value PM) {
  LLVMAddSimplifyLibCallsPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_tail_call_elimination(value PM) {
  LLVMAddTailCallEliminationPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_demote_memory_to_register(value PM) {
  LLVMAddDemoteMemoryToRegisterPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_verifier(value PM) {
  LLVMAddVerifierPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_correlated_value_propagation(value PM) {
  LLVMAddCorrelatedValuePropagationPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_early_cse(value PM) {
  LLVMAddEarlyCSEPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_lower_expect_intrinsic(value PM) {
  LLVMAddLowerExpectIntrinsicPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_lower_constant_intrinsics(value PM) {
  LLVMAddLowerConstantIntrinsicsPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_type_based_alias_analysis(value PM) {
  LLVMAddTypeBasedAliasAnalysisPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_scoped_no_alias_aa(value PM) {
  LLVMAddScopedNoAliasAAPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_basic_alias_analysis(value PM) {
  LLVMAddBasicAliasAnalysisPass(PassManager_val(PM));
  return Val_unit;
}

/* [<Llvm.PassManager.any] Llvm.PassManager.t -> unit */
value llvm_add_unify_function_exit_nodes(value PM) {
  LLVMAddUnifyFunctionExitNodesPass(PassManager_val(PM));
  return Val_unit;
}
