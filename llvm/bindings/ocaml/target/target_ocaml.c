/*===-- target_ocaml.c - LLVM OCaml Glue ------------------------*- C++ -*-===*\
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
#include "llvm-c/Target.h"
#include "llvm-c/TargetMachine.h"
#include "caml/alloc.h"
#include "caml/fail.h"
#include "caml/memory.h"
#include "caml/custom.h"
#include "caml/callback.h"
#include "llvm_ocaml.h"

void llvm_raise(value Prototype, char *Message);
value llvm_string_of_message(char *Message);

/*===---- Data Layout -----------------------------------------------------===*/

#define DataLayout_val(v) (*(LLVMTargetDataRef *)(Data_custom_val(v)))

static void llvm_finalize_data_layout(value DataLayout) {
  LLVMDisposeTargetData(DataLayout_val(DataLayout));
}

static struct custom_operations llvm_data_layout_ops = {
    (char *)"Llvm_target.DataLayout.t",
    llvm_finalize_data_layout,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default};

value llvm_alloc_data_layout(LLVMTargetDataRef DataLayout) {
  value V =
      alloc_custom(&llvm_data_layout_ops, sizeof(LLVMTargetDataRef), 0, 1);
  DataLayout_val(V) = DataLayout;
  return V;
}

/* string -> DataLayout.t */
value llvm_datalayout_of_string(value StringRep) {
  CAMLparam1(StringRep);
  CAMLreturn(
    llvm_alloc_data_layout(LLVMCreateTargetData(String_val(StringRep))));
}

/* DataLayout.t -> string */
value llvm_datalayout_as_string(value TD) {
  CAMLparam1(TD);
  char *StringRep = LLVMCopyStringRepOfTargetData(DataLayout_val(TD));
  value Copy = copy_string(StringRep);
  LLVMDisposeMessage(StringRep);
  CAMLreturn(Copy);
}

/* DataLayout.t -> Endian.t */
value llvm_datalayout_byte_order(value DL) {
  CAMLparam1(DL);
  CAMLreturn(Val_int(LLVMByteOrder(DataLayout_val(DL))));
}

/* DataLayout.t -> int */
value llvm_datalayout_pointer_size(value DL) {
  CAMLparam1(DL);
  CAMLreturn(Val_int(LLVMPointerSize(DataLayout_val(DL))));
}

/* Llvm.llcontext -> DataLayout.t -> Llvm.lltype */
value llvm_datalayout_intptr_type(value C, value DL) {
  CAMLparam2(C, DL);
  LLVMTypeRef Type =
    LLVMIntPtrTypeInContext(Context_val(C), DataLayout_val(DL));
  CAMLreturn(to_val(Type));
}

/* int -> DataLayout.t -> int */
value llvm_datalayout_qualified_pointer_size(value AS, value DL) {
  CAMLparam2(AS, DL);
  CAMLreturn(Val_int(LLVMPointerSizeForAS(DataLayout_val(DL), Int_val(AS))));
}

/* Llvm.llcontext -> int -> DataLayout.t -> Llvm.lltype */
value llvm_datalayout_qualified_intptr_type(value C, value AS, value DL) {
  CAMLparam3(C, AS, BL);
  LLVMTypeRef Type = LLVMIntPtrTypeForASInContext(
    Context_val(C), DataLayout_val(DL), Int_val(AS));
  CAMLreturn(to_val(Type));
}

/* Llvm.lltype -> DataLayout.t -> Int64.t */
value llvm_datalayout_size_in_bits(value Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(
    caml_copy_int64(LLVMSizeOfTypeInBits(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.lltype -> DataLayout.t -> Int64.t */
value llvm_datalayout_store_size(LLVMTypeRef Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(
    caml_copy_int64(LLVMStoreSizeOfType(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.lltype -> DataLayout.t -> Int64.t */
value llvm_datalayout_abi_size(value Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(
    caml_copy_int64(LLVMABISizeOfType(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.lltype -> DataLayout.t -> int */
value llvm_datalayout_abi_align(value Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(Val_int(LLVMABIAlignmentOfType(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.lltype -> DataLayout.t -> int */
value llvm_datalayout_stack_align(value Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(
    Val_int(LLVMCallFrameAlignmentOfType(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.lltype -> DataLayout.t -> int */
value llvm_datalayout_preferred_align(value Ty, value DL) {
  CAMLparam2(Ty, DL);
  CAMLreturn(
    Val_int(LLVMPreferredAlignmentOfType(DataLayout_val(DL), Type_val(Ty))));
}

/* Llvm.llvalue -> DataLayout.t -> int */
value llvm_datalayout_preferred_align_of_global(value GlobalVar, value DL) {
  CAMLparam2(GlobalVar, DL);
  CAMLreturn(
    Val_int(LLVMPreferredAlignmentOfGlobal(DataLayout_val(DL),
                                           Value_val(GlobalVar))));
}

/* Llvm.lltype -> Int64.t -> DataLayout.t -> int */
value llvm_datalayout_element_at_offset(value Ty, value Offset, value DL) {
  CAMLparam3(Ty, Offset, DL);
  CAMLreturn(Val_int(
    LLVMElementAtOffset(DataLayout_val(DL), Type_val(Ty), Int64_val(Offset))));
}

/* Llvm.lltype -> int -> DataLayout.t -> Int64.t */
value llvm_datalayout_offset_of_element(value Ty, value Index, value DL) {
  CAMLparam3(Ty, Index, DL);
  CAMLreturn(caml_copy_int64(
      LLVMOffsetOfElement(DataLayout_val(DL), Type_val(Ty), Int_val(Index))));
}

/*===---- Target ----------------------------------------------------------===*/

#define Target_val(v) ((LLVMTargetRef) from_val(v))

/* unit -> string */
value llvm_target_default_triple(value Unit) {
  CAMLparam1(Unit);
  char *TripleCStr = LLVMGetDefaultTargetTriple();
  value TripleStr = caml_copy_string(TripleCStr);
  LLVMDisposeMessage(TripleCStr);
  CAMLreturn(TripleStr);
}

/* unit -> Target.t option */
value llvm_target_first(value Unit) {
  CAMLparam1(Unit);
  CAMLreturn(ptr_to_option(LLVMGetFirstTarget()));
}

/* Target.t -> Target.t option */
value llvm_target_succ(value Target) {
  CAMLparam1(Target);
  CAMLreturn(ptr_to_option(LLVMGetNextTarget(Target_val(Target))));
}

/* string -> Target.t option */
value llvm_target_by_name(value Name) {
  CAMLparam1(Name);
  CAMLreturn(ptr_to_option(LLVMGetTargetFromName(String_val(Name))));
}

/* string -> Target.t */
value llvm_target_by_triple(value Triple) {
  CAMLparam1(Triple);
  LLVMTargetRef T;
  char *Error;

  if (LLVMGetTargetFromTriple(String_val(Triple), &T, &Error))
    llvm_raise(*caml_named_value("Llvm_target.Error"), Error);

  CAMLreturn(to_val(T));
}

/* Target.t -> string */
value llvm_target_name(value Target) {
  CAMLparam1(Target);
  CAMLreturn(caml_copy_string(LLVMGetTargetName(Target_val(Target))));
}

/* Target.t -> string */
value llvm_target_description(value Target) {
  CAMLparam1(Target);
  CAMLreturn(caml_copy_string(LLVMGetTargetDescription(Target_val(Target))));
}

/* Target.t -> bool */
value llvm_target_has_jit(value Target) {
  CAMLparam1(Target);
  CAMLreturn(Val_bool(LLVMTargetHasJIT(Target_val(Target))));
}

/* Target.t -> bool */
value llvm_target_has_target_machine(value Target) {
  CAMLparam1(Target);
  CAMLreturn(Val_bool(LLVMTargetHasTargetMachine(Target_val(Target))));
}

/* Target.t -> bool */
value llvm_target_has_asm_backend(value Target) {
  CAMLparam1(Target);
  CAMLreturn(Val_bool(LLVMTargetHasAsmBackend(Target_val(Target))));
}

/*===---- Target Machine --------------------------------------------------===*/

#define TargetMachine_val(v) (*(LLVMTargetMachineRef *)(Data_custom_val(v)))

static void llvm_finalize_target_machine(value Machine) {
  LLVMDisposeTargetMachine(TargetMachine_val(Machine));
}

static struct custom_operations llvm_target_machine_ops = {
    (char *)"Llvm_target.TargetMachine.t",
    llvm_finalize_target_machine,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default};

static value llvm_alloc_targetmachine(LLVMTargetMachineRef Machine) {
  value V = alloc_custom(&llvm_target_machine_ops, sizeof(LLVMTargetMachineRef),
                         0, 1);
  TargetMachine_val(V) = Machine;
  return V;
}

/* triple:string -> ?cpu:string -> ?features:string
   ?level:CodeGenOptLevel.t -> ?reloc_mode:RelocMode.t
   ?code_model:CodeModel.t -> Target.t -> TargetMachine.t */
value llvm_create_targetmachine_native(value Triple, value CPU, value Features,
                                       value OptLevel, value RelocMode,
                                       value CodeModel, value Target) {
  CAMLparam5(Triple, CPU, Features, OptLevel, RelocMode);
  CAMLxparam2(CodeModel, Target);
  LLVMTargetMachineRef Machine;
  const char *CPUStr = "", *FeaturesStr = "";
  LLVMCodeGenOptLevel OptLevelEnum = LLVMCodeGenLevelDefault;
  LLVMRelocMode RelocModeEnum = LLVMRelocDefault;
  LLVMCodeModel CodeModelEnum = LLVMCodeModelDefault;

  if (CPU != Val_int(0))
    CPUStr = String_val(Field(CPU, 0));
  if (Features != Val_int(0))
    FeaturesStr = String_val(Field(Features, 0));
  if (OptLevel != Val_int(0))
    OptLevelEnum = Int_val(Field(OptLevel, 0));
  if (RelocMode != Val_int(0))
    RelocModeEnum = Int_val(Field(RelocMode, 0));
  if (CodeModel != Val_int(0))
    CodeModelEnum = Int_val(Field(CodeModel, 0));

  Machine =
      LLVMCreateTargetMachine(Target_val(Target), String_val(Triple), CPUStr,
                              FeaturesStr, OptLevelEnum, RelocModeEnum,
                              CodeModelEnum);

  CAMLreturn(llvm_alloc_targetmachine(Machine));
}

value llvm_create_targetmachine_bytecode(value *argv, int argn) {
  return llvm_create_targetmachine_native(argv[0], argv[1], argv[2], argv[3],
                                          argv[4], argv[5], argv[6]);
}

/* TargetMachine.t -> Target.t */
value llvm_targetmachine_target(value Machine) {
  CAMLparam1(Machine);
  CAMLreturn(to_val(LLVMGetTargetMachineTarget(TargetMachine_val(Machine))));
}

/* TargetMachine.t -> string */
value llvm_targetmachine_triple(value Machine) {
  CAMLparam1(Machine);
  CAMLreturn(llvm_string_of_message(
      LLVMGetTargetMachineTriple(TargetMachine_val(Machine))));
}

/* TargetMachine.t -> string */
value llvm_targetmachine_cpu(value Machine) {
  CAMLparam1(Machine);
  CAMLreturn(llvm_string_of_message(
      LLVMGetTargetMachineCPU(TargetMachine_val(Machine))));
}

/* TargetMachine.t -> string */
value llvm_targetmachine_features(value Machine) {
  CAMLparam1(Machine);
  CAMLreturn(llvm_string_of_message(
      LLVMGetTargetMachineFeatureString(TargetMachine_val(Machine))));
}

/* TargetMachine.t -> DataLayout.t */
value llvm_targetmachine_data_layout(value Machine) {
  CAMLparam1(Machine);
  CAMLreturn(llvm_alloc_data_layout(
      LLVMCreateTargetDataLayout(TargetMachine_val(Machine))));
}

/* bool -> TargetMachine.t -> unit */
value llvm_targetmachine_set_verbose_asm(value Verb, value Machine) {
  CAMLparam2(Verb, Machine);
  LLVMSetTargetMachineAsmVerbosity(TargetMachine_val(Machine), Bool_val(Verb));
  CAMLreturn(Val_unit);
}

/* Llvm.llmodule -> CodeGenFileType.t -> string -> TargetMachine.t -> unit */
value llvm_targetmachine_emit_to_file(value Module, value FileType,
                                      value FileName, value Machine) {
  CAMLparam5(Module, FileType, FileName, Machine);
  char *ErrorMessage;

  if (LLVMTargetMachineEmitToFile(TargetMachine_val(Machine),
                                  Module_val(Module),
                                  (char *)String_val(FileName),
                                  Int_val(FileType), &ErrorMessage)) {
    llvm_raise(*caml_named_value("Llvm_target.Error"), ErrorMessage);
  }

  CAMLreturn(Val_unit);
}

/* Llvm.llmodule -> CodeGenFileType.t -> TargetMachine.t ->
   Llvm.llmemorybuffer */
value
llvm_targetmachine_emit_to_memory_buffer(value Module, value FileType,
                                         value Machine) {
  CAMLparam3(Module, FileType, Machine);
  char *ErrorMessage;
  LLVMMemoryBufferRef Buffer;

  if (LLVMTargetMachineEmitToMemoryBuffer(TargetMachine_val(Machine),
                                          Module_val(Module),
                                          Int_val(FileType), &ErrorMessage,
                                          &Buffer)) {
    llvm_raise(*caml_named_value("Llvm_target.Error"), ErrorMessage);
  }

  CAMLreturn(to_val(Buffer));
}

/* TargetMachine.t -> Llvm.PassManager.t -> unit */
value llvm_targetmachine_add_analysis_passes(value PM, value Machine) {
  CAMLparam1(PM, Machine);
  LLVMAddAnalysisPasses(TargetMachine_val(Machine), PassManager_val(PM));
  CAMLreturn(Val_unit);
}
