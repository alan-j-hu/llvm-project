/*===-- llvm_ocaml.c - LLVM OCaml Glue --------------------------*- C++ -*-===*\
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

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "llvm-c/Core.h"
#include "llvm-c/Support.h"
#include "llvm/Config/llvm-config.h"
#include "caml/memory.h"
#include "caml/fail.h"
#include "caml/callback.h"
#include "llvm_ocaml.h"

#if OCAML_VERSION < 41200
value caml_alloc_some(value v) {
  CAMLparam1(v);
  value Some = caml_alloc_small(1, 0);
  Field(Some, 0) = v;
  CAMLreturn(Some);
}
#endif

value caml_alloc_tuple_uninit(mlsize_t wosize) {
  if (wosize <= Max_young_wosize) {
    return caml_alloc_small(wosize, 0);
  } else {
    return caml_alloc_shr(wosize, 0);
  }
}

value llvm_string_of_message(char *Message) {
  value String = caml_copy_string(Message);
  LLVMDisposeMessage(Message);

  return String;
}

value ptr_to_option(void *Ptr) {
  if (!Ptr)
    return Val_none;
  value v = caml_alloc(1, Abstract_tag);
  *((void**) Data_abstract_val(v)) = Ptr;
  return caml_alloc_some(v);
}

value cstr_to_string(const char *Str, mlsize_t Len) {
  if (!Str)
    return caml_alloc_string(0);
  value String = caml_alloc_string(Len);
  memcpy((char *)String_val(String), Str, Len);
  return String;
}

value cstr_to_string_option(const char *CStr, mlsize_t Len) {
  if (!CStr)
    return Val_none;
  value String = caml_alloc_string(Len);
  memcpy((char *)String_val(String), CStr, Len);
  return caml_alloc_some(String);
}

void llvm_raise(value Prototype, char *Message) {
  caml_raise_with_arg(Prototype, llvm_string_of_message(Message));
}

static value llvm_fatal_error_handler;

static void llvm_fatal_error_trampoline(const char *Reason) {
  caml_callback(llvm_fatal_error_handler, caml_copy_string(Reason));
}

value llvm_install_fatal_error_handler(value Handler) {
  LLVMInstallFatalErrorHandler(llvm_fatal_error_trampoline);
  llvm_fatal_error_handler = Handler;
  caml_register_global_root(&llvm_fatal_error_handler);
  return Val_unit;
}

value llvm_reset_fatal_error_handler(value Unit) {
  caml_remove_global_root(&llvm_fatal_error_handler);
  LLVMResetFatalErrorHandler();
  return Val_unit;
}

value llvm_enable_pretty_stacktrace(value Unit) {
  LLVMEnablePrettyStackTrace();
  return Val_unit;
}

value llvm_parse_command_line_options(value Overview, value Args) {
  const char *COverview;
  if (Overview == Val_int(0)) {
    COverview = NULL;
  } else {
    COverview = String_val(Field(Overview, 0));
  }
  LLVMParseCommandLineOptions(Wosize_val(Args),
                              (const char *const *)Op_val(Args), COverview);
  return Val_unit;
}

static value alloc_variant(int tag, void *Value) {
  value Iter = caml_alloc_small(1, tag);
  Field(Iter, 0) = Val_op(Value);
  return Iter;
}

/* Macro to convert the C first/next/last/prev idiom to the Ocaml llpos/
   llrev_pos idiom. */
#define DEFINE_ITERATORS(camlname, cname, pty, cty, pfun) \
  /* llmodule -> ('a, 'b) llpos */                        \
  value llvm_##camlname##_begin(pty Mom) {       \
    cty First = LLVMGetFirst##cname(Mom);                 \
    if (First)                                            \
      return alloc_variant(1, First);                     \
    return alloc_variant(0, Mom);                         \
  }                                                       \
                                                          \
  /* llvalue -> ('a, 'b) llpos */                         \
  value llvm_##camlname##_succ(cty Kid) {        \
    cty Next = LLVMGetNext##cname(Kid);                   \
    if (Next)                                             \
      return alloc_variant(1, Next);                      \
    return alloc_variant(0, pfun(Kid));                   \
  }                                                       \
                                                          \
  /* llmodule -> ('a, 'b) llrev_pos */                    \
  value llvm_##camlname##_end(pty Mom) {         \
    cty Last = LLVMGetLast##cname(Mom);                   \
    if (Last)                                             \
      return alloc_variant(1, Last);                      \
    return alloc_variant(0, Mom);                         \
  }                                                       \
                                                          \
  /* llvalue -> ('a, 'b) llrev_pos */                     \
  value llvm_##camlname##_pred(cty Kid) {        \
    cty Prev = LLVMGetPrevious##cname(Kid);               \
    if (Prev)                                             \
      return alloc_variant(1, Prev);                      \
    return alloc_variant(0, pfun(Kid));                   \
  }

/*===-- Context error handling --------------------------------------------===*/

void llvm_diagnostic_handler_trampoline(value DI, void *DiagnosticContext) {
  caml_callback(*((value *)DiagnosticContext), DI);
}

/* Diagnostic.t -> string */
value llvm_get_diagnostic_description(value Diagnostic) {
  return llvm_string_of_message(
      LLVMGetDiagInfoDescription(LLVMDiagnosticInfo_val(Diagnostic)));
}

/* Diagnostic.t -> DiagnosticSeverity.t */
value llvm_get_diagnostic_severity(value Diagnostic) {
  return Val_int(LLVMGetDiagInfoSeverity(LLVMDiagnosticInfo_val(Diagnostic)));
}

static void llvm_remove_diagnostic_handler(value C) {
  CAMLparam1(C);
  LLVMContextRef context = LLVMContext_val(C);
  if (LLVMContextGetDiagnosticHandler(context) ==
      llvm_diagnostic_handler_trampoline) {
    value *Handler = (value *)LLVMContextGetDiagnosticContext(context);
    remove_global_root(Handler);
    free(Handler);
  }
}

/* llcontext -> (Diagnostic.t -> unit) option -> unit */
value llvm_set_diagnostic_handler(value C, value Handler) {
  CAMLparam2(C, Handler);
  LLVMContextRef context = LLVMContext_val(C);
  llvm_remove_diagnostic_handler(context);
  if (Handler == Val_none) {
    LLVMContextSetDiagnosticHandler(context, NULL, NULL);
  } else {
    value *DiagnosticContext = caml_alloc(1, Abstract_tag);
    if (DiagnosticContext == NULL)
      caml_raise_out_of_memory();
    *DiagnosticContext = Field(Handler, 0);
    caml_register_global_root(DiagnosticContext);
    LLVMContextSetDiagnosticHandler(context, llvm_diagnostic_handler_trampoline,
                                    DiagnosticContext);
  }
  CAMLreturn (Val_unit);
}

/*===-- Contexts ----------------------------------------------------------===*/

/* unit -> llcontext */
value llvm_create_context(value Unit) {
  CAMLparam1(Unit);
  CAMLlocal1(context_val);
  context_val = caml_alloc(1, Abstract_tag);
  LLVMContext_val(context_val) = LLVMContextCreate();
  CAMLreturn(context_val);
}

/* llcontext -> unit */
value llvm_dispose_context(value C) {
  CAMLparam1(C);
  llvm_remove_diagnostic_handler(LLVMContext_val(C));
  LLVMContextDispose(LLVMContext_val(C));
  CAMLreturn(Val_unit);
}

/* unit -> llcontext */
value llvm_global_context(value Unit) {
  CAMLparam1(Unit);
  CAMLlocal1(context_val);
  context_val = caml_alloc(1, Abstract_tag);
  LLVMContext_val(context_val) = LLVMGetGlobalContext();
  CAMLreturn(context_val);
}

/* llcontext -> string -> int */
value llvm_mdkind_id(value C, value Name) {
  CAMLparam2(C, Name);
  unsigned MDKindID =
      LLVMGetMDKindIDInContext(LLVMContext_val(C), String_val(Name),
                               caml_string_length(Name));
  CAMLreturn(Val_int(MDKindID));
}

/*===-- Attributes --------------------------------------------------------===*/

/* string -> llattrkind */
value llvm_enum_attr_kind(value Name) {
  CAMLparam1(Name);
  unsigned Kind = LLVMGetEnumAttributeKindForName(String_val(Name),
                                                  caml_string_length(Name));
  if (Kind == 0)
    caml_raise_with_arg(*caml_named_value("Llvm.UnknownAttribute"), Name);
  CAMLreturn(Val_int(Kind));
}

/* llcontext -> int -> int64 -> llattribute */
value llvm_create_enum_attr_by_kind(value C, value Kind, value Value) {
  CAMLparam3(C, Kind, Value);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMAttribute_val(Ret) =
    LLVMCreateEnumAttribute(LLVMContext_val(C), Int_val(Kind),
                            Int64_val(Value));
  CAMLreturn(Ret);
}

/* llattribute -> bool */
value llvm_is_enum_attr(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMIsEnumAttribute(LLVMAttribute_val(A))));
}

/* llattribute -> llattrkind */
value llvm_get_enum_attr_kind(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMGetEnumAttributeKind(LLVMAttribute_val(A))));
}

/* llattribute -> int64 */
value llvm_get_enum_attr_value(value A) {
  CAMLparam1(A);
  CAMLreturn(caml_copy_int64(LLVMGetEnumAttributeValue(LLVMAttribute_val(A))));
}

/* llcontext -> kind:string -> name:string -> llattribute */
value llvm_create_string_attr(value C, value Kind, value Value) {
  CAMLparam3(C, Kind, Value);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMAttribute_val(Ret) = LLVMCreateStringAttribute(
    LLVMContext_val(C), String_val(Kind),
    caml_string_length(Kind), String_val(Value),
    caml_string_length(Value));
  CAMLreturn(Ret);
}

/* llattribute -> bool */
value llvm_is_string_attr(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMIsStringAttribute(LLVMAttribute_val(A))));
}

/* llattribute -> string */
value llvm_get_string_attr_kind(value A) {
  CAMLparam1(A);
  unsigned Length;
  const char *String =
    LLVMGetStringAttributeKind(LLVMAttribute_val(A), &Length);
  CAMLreturn(cstr_to_string(String, Length));
}

/* llattribute -> string */
value llvm_get_string_attr_value(value A) {
  CAMLparam1(A);
  unsigned Length;
  const char *String =
    LLVMGetStringAttributeValue(LLVMAttribute_val(A), &Length);
  CAMLreturn(cstr_to_string(String, Length));
}

/*===-- Modules -----------------------------------------------------------===*/

/* llcontext -> string -> llmodule */
value llvm_create_module(value C, value ModuleID) {
  CAMLparam2(C, ModuleID);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMModule_val(Ret) =
    LLVMModuleCreateWithNameInContext(String_val(ModuleID), LLVMContext_ref(C));
  CAMLreturn(Ret);
}

/* llmodule -> unit */
value llvm_dispose_module(value M) {
  CAMLparam1(M);
  LLVMDisposeModule(LLVMModule_val(M));
  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_target_triple(value M) {
  CAMLparam1(M);
  CAMLreturn(caml_copy_string(LLVMGetTarget(LLVMModule_val(M))));
}

/* string -> llmodule -> unit */
value llvm_set_target_triple(value Trip, value M) {
  CAMLparam2(Trip, M);
  LLVMSetTarget(LLVMModule_val(M), String_val(Trip));
  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_data_layout(value M) {
  CAMLparam1(M);
  CAMLreturn(caml_copy_string(LLVMGetDataLayout(LLVMModule_val(M))));
}

/* string -> llmodule -> unit */
value llvm_set_data_layout(value Layout, value M) {
  CAMLparam2(layout, M);
  LLVMSetDataLayout(LLVMModule_val(M), String_val(Layout));
  CAMLreturn(Val_unit);
}

/* llmodule -> unit */
value llvm_dump_module(value M) {
  CAMLparam1(M);
  LLVMDumpModule(LLVMModule_val(M));
  CAMLreturn(Val_unit);
}

/* string -> llmodule -> unit */
value llvm_print_module(value Filename, value M) {
  CAMLparam2(Filename, M);
  char *Message;

  if (LLVMPrintModuleToFile(LLVMModule_val(M), String_val(Filename), &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);

  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_string_of_llmodule(value M) {
  CAMLparam1(M);
  char *ModuleCStr = LLVMPrintModuleToString(LLVMModule_val(M));
  value ModuleStr = caml_copy_string(ModuleCStr);
  LLVMDisposeMessage(ModuleCStr);

  CAMLreturn(ModuleStr);
}

/* llmodule -> string */
value llvm_get_module_identifier(value M) {
  CAMLparam1(M);
  size_t Len;
  const char *Name = LLVMGetModuleIdentifier(LLVMModule_val(M), &Len);
  CAMLreturn(cstr_to_string(Name, (mlsize_t)Len));
}

/* llmodule -> string -> unit */
value llvm_set_module_identifier(value M, value Id) {
  CAMLparam2(M, Id);
  LLVMSetModuleIdentifier(LLVMModule_val(M), String_val(Id),
                          caml_string_length(Id));
  CAMLreturn(Val_unit);
}

/* llmodule -> string -> unit */
value llvm_set_module_inline_asm(value M, value Asm) {
  CAMLparam2(M, Asm);
  LLVMSetModuleInlineAsm(LLVMModule_val(M), String_val(Asm));
  CAMLreturn(Val_unit);
}

/* llmodule -> string -> llmetadata option */
value llvm_get_module_flag(value M, value Key) {
  CAMLparam2(M, Key);
  CAMLreturn(ptr_to_option(
      LLVMGetModuleFlag(LLVMModule_val(M), String_val(Key),
                        caml_string_length(Key))));
}

/* llmodule -> ModuleFlagBehavior.t -> string -> llmetadata -> unit */
value llvm_add_module_flag(value M, value Behaviour, value Key, value Val) {
  CAMLparam4(M, Behavior, Key, Val);
  LLVMAddModuleFlag(LLVMModule_val(M), Int_val(Behaviour), String_val(Key),
                    caml_string_length(Key), LLVMMetadata_val(Val));
  CAMLreturn(Val_unit);
}

/*===-- Types -------------------------------------------------------------===*/

/* lltype -> TypeKind.t */
value llvm_classify_type(value Ty) {
  CAMLparam1(Ty);
  CAMLreturn(Val_int(LLVMGetTypeKind(LLVMType_val(Ty))));
}

value llvm_type_is_sized(value Ty) {
  CAMLparam1(Ty);
  CAMLreturn(Val_bool(LLVMTypeIsSized(LLVMType_val(Ty))));
}

/* lltype -> llcontext */
LLVMContextRef llvm_type_context(value Ty) {
  CAMLparam1(Ty);
  CAMLreturn(LLVMGetTypeContext(LLVMType_val(Ty)));
}

/* lltype -> unit */
value llvm_dump_type(value Val) {
  CAMLparam1(Val);
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
  LLVMDumpType(LLVMType_val(Val));
#else
  caml_raise_with_arg(*caml_named_value("Llvm.FeatureDisabled"),
                      caml_copy_string("dump"));
#endif
  CAMLreturn(Val_unit);
}

/* lltype -> string */
value llvm_string_of_lltype(value M) {
  CAMLparam1(M);
  CAMLlocal1(TypeStr);
  char *TypeCStr = LLVMPrintTypeToString(LLVMType_val(M));
  TypeStr = caml_copy_string(TypeCStr);
  LLVMDisposeMessage(TypeCStr);

  CAMLreturn(TypeStr);
}

/*--... Operations on integer types ........................................--*/

/* llcontext -> lltype */
value llvm_i1_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMInt1TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i8_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMInt8TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i16_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMInt16TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i32_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMInt32TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i64_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMInt64TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> int -> lltype */
value llvm_integer_type(value Context, value Width) {
  CAMLparam2(Context, Width);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMIntTypeInContext(LLVMContext_val(Context), Int_val(Width));
  CAMLreturn(Ret);
}

/* lltype -> int */
value llvm_integer_bitwidth(value IntegerTy) {
  CAMLparam1(IntegerTy);
  CAMLreturn(Val_int(LLVMGetIntTypeWidth(LLVMType_val(IntegerTy))));
}

/*--... Operations on real types ...........................................--*/

/* llcontext -> lltype */
value llvm_float_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMFloatTypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_double_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMDoubleTypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_x86fp80_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMX86FP80TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_fp128_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMFP128TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_ppc_fp128_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMPPCFP128TypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/*--... Operations on function types .......................................--*/

/* lltype -> lltype array -> lltype */
value llvm_function_type(value RetTy, value ParamTys) {
  CAMLparam2(RetTy, ParamTys);
  CAMLlocal2(Temp, Ret);
  size_t len = Wosize_val(ParamTys);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMType_val(Field(ParamTys, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMFunctionType(LLVMType_val(RetTy), (LLVMTypeRef*)Temp, len, 0);
  CAMLreturn(Ret);
}

/* lltype -> lltype array -> lltype */
value llvm_var_arg_function_type(value RetTy, value ParamTys) {
  CAMLparam2(RetTy, ParamTys);
  CAMLlocal2(Temp, Ret);
  size_t len = Wosize_val(ParamTys);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMType_val(Field(ParamTys, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMFunctionType(LLVMType_val(RetTy), (LLVMTypeRef*)Temp, len, 1);
  CAMLreturn(Ret);
}

/* lltype -> bool */
value llvm_is_var_arg(value FunTy) {
  CAMLparam1(FunTy);
  CAMLreturn(Val_bool(LLVMIsFunctionVarArg(LLVMType_val(FunTy))));
}

/* lltype -> lltype array */
value llvm_param_types(value FunTy) {
  CAMLparam1(FunTy);
  CAMLlocal2(Temp, Tys);
  unsigned len = LLVMCountParamTypes(FunTy);
  Temp = caml_alloc(len, Abstract_tag);
  LLVMGetParamTypes(LLVMType_val(FunTy), (LLVMTypeRef*)Temp);
  Tys = caml_alloc_tuple_uninit(len);
  for (size_t i = 0; i < len; ++i) {
    LLVMType_val(Field(Tys, i)) = (LLVMTypeRef) Field(Temp, i);
  }
  CAMLreturn(Tys);
}

/*--... Operations on struct types .........................................--*/

/* llcontext -> lltype array -> lltype */
value llvm_struct_type(value C, value ElementTypes) {
  CAMLparam2(C, ElementTypes);
  CAMLlocal2(Temp, Ret);
  size_t len = Wosize_val(ElementTypes);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMType_val(Field(ElementTypes, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMStructTypeInContext(LLVMContext_val(C), (LLVMTypeRef*)Temp, len, 0);
  CAMLreturn(Ret);
}

/* llcontext -> lltype array -> lltype */
value llvm_packed_struct_type(value C, value ElementTypes) {
  CAMLparam2(C, ElementTypes);
  CAMLlocal1(Temp, Ret);
  size_t len = Wosize_val(ElementTypes);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMType_val(Field(ElementTypes, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMStructTypeInContext(LLVMContext_val(C), (LLVMTypeRef*)Temp, len, 1);
  CAMLreturn(Ret);
}

/* llcontext -> string -> lltype */
value llvm_named_struct_type(value C, value Name) {
  CAMLparam2(C, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMStructCreateNamed(LLVMContext_val(C), String_val(Name));
  CAMLreturn(Ret);
}

/* lltype -> lltype array -> bool -> unit */
value llvm_struct_set_body(value Ty, value ElementTypes, value Packed) {
  CAMLparam3(Ty, ElementTypes, Packed);
  CAMLlocal1(Temp);
  size_t len = Wosize_val(ElementTypes);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMType_val(Field(ElementTypes, i));
  }
  LLVMStructSetBody(LLVMType_val(Ty), (LLVMTypeRef*)Temp, len,
                    Bool_val(Packed));
  CAMLreturn(Val_unit);
}

/* lltype -> string option */
value llvm_struct_name(value Ty) {
  CAMLparam1(Ty);
  const char *CStr = LLVMGetStructName(LLVMType_val(Ty));
  size_t Len;
  if (!CStr) {
    CAMLreturn(Val_none);
  }
  Len = strlen(CStr);
  CAMLreturn(cstr_to_string_option(CStr, Len));
}

/* lltype -> lltype array */
value llvm_struct_element_types(value StructTy) {
  CAMLparam1(StructTy);
  CAMLlocal2(Temp, Tys);
  unsigned count = LLVMCountStructElementTypes(StructTy);
  value Tys = caml_alloc_tuple_uninit(count);
  Temp = caml_alloc(count, Abstract_tag);
  LLVMGetStructElementTypes(LLVMType_val(StructTy), (LLVMTypeRef*)Temp);
  for (unsigned i = 0; i < count; ++i) {
    Field(Tys, i) = LLVMType_val(Field(Temp, i));
  }
  CAMLreturn(Tys);
}

/* lltype -> bool */
value llvm_is_packed(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsPackedStruct(LLVMType_val(StructTy))));
}

/* lltype -> bool */
value llvm_is_opaque(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsOpaqueStruct(LLVMType_val(StructTy))));
}

/* lltype -> bool */
value llvm_is_literal(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsLiteralStruct(LLVMType_val(StructTy))));
}

/*--... Operations on array, pointer, and vector types .....................--*/

/* lltype -> lltype array */
value llvm_subtypes(value Ty) {
  CAMLparam1(Ty);
  CAMLlocal2(Temp, Arr);
  unsigned Size = LLVMGetNumContainedTypes(LLVMType_val(Ty));
  Arr = caml_alloc_tuple_uninit(Size);
  Temp = caml_alloc(Size, Abstract_tag);
  LLVMGetSubtypes(LLVMType_val(Ty), (LLVMTypeRef*)Temp);
  for (unsigned int i = 0; i < Size; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    LLVMType_val(Box) = Field(Temp, i);
    Field(Arr, i) = Box;
  }
  CAMLreturn(Arr);
}

/* lltype -> int -> lltype */
value llvm_array_type(value ElementTy, value Count) {
  CAMLparam2(ElementTy, Count);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMArrayType(LLVMType_val(ElementTy), Int_val(Count));
  CAMLreturn(v);
}

/* lltype -> lltype */
value llvm_pointer_type(value ElementTy) {
  CAMLparam1(ElementTy);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMPointerType(LLVMType_val(ElementTy), 0);
  CAMLreturn(Ret);
}

/* lltype -> int -> lltype */
value llvm_qualified_pointer_type(value ElementTy, value AddressSpace) {
  CAMLparam2(ElementTy, AddressSpace);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMPointerType(LLVMType_val(ElementTy), Int_val(AddressSpace));
  CAMLreturn(v);
}

/* llcontext -> int -> lltype */
value llvm_pointer_type_in_context(value C, value AddressSpace) {
  CAMLparam2(C, AddressSpace);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) =
    LLVMPointerTypeInContext(LLVMContext_val(C), Int_val(AddressSpace));
  CAMLreturn(Ret);
}

/* lltype -> int -> lltype */
value llvm_vector_type(value ElementTy, value Count) {
  CAMLparam2(ElementTy, Count);
  CAMLparam1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMVectorType(LLVMType_val(ElementTy), Int_val(Count));
  CAMLreturn(Ret);
}

/* lltype -> int */
value llvm_array_length(value ArrayTy) {
  CAMLparam1(ArrayTy);
  CAMLreturn(Val_int(LLVMGetArrayLength(LLVMType_val(ArrayTy))));
}

/* lltype -> int */
value llvm_address_space(value PtrTy) {
  CAMLparam1(PtrTy);
  CAMLreturn(Val_int(LLVMGetPointerAddressSpace(LLVMType_val(PtrTy))));
}

/* lltype -> int */
value llvm_vector_size(value VectorTy) {
  CAMLparam1(VectorTy);
  CAMLreturn(Val_int(LLVMGetVectorSize(LLVMType_val(VectorTy))));
}

/*--... Operations on other types ..........................................--*/

/* llcontext -> lltype */
value llvm_void_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMVoidTypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_label_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMLabelTypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_x86_mmx_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMType_val(Ret) = LLVMX86MMXTypeInContext(LLVMContext_val(Context));
  CAMLreturn(Ret);
}

/* llmodule -> string -> lltype option */
value llvm_type_by_name(value M, value Name) {
  CAMLparam2(M, Name);
  CAMLreturn(
    ptr_to_option(LLVMGetTypeByName(LLVMModule_val(M), String_val(Name))));
}

/*===-- VALUES ------------------------------------------------------------===*/

/* llvalue -> lltype */
value llvm_type_of(value Val) {
  CAMLparam1(Val);
  CAMLlocal1(V);
  V = caml_alloc(1, Abstract_tag);
  LLVMType_val(V) = LLVMTypeOf(LLVMValue_val(Val));
  CAMLreturn(V);
}

/* keep in sync with ValueKind.t */
enum ValueKind {
  NullValue = 0,
  Argument,
  BasicBlock,
  InlineAsm,
  MDNode,
  MDString,
  BlockAddress,
  ConstantAggregateZero,
  ConstantArray,
  ConstantDataArray,
  ConstantDataVector,
  ConstantExpr,
  ConstantFP,
  ConstantInt,
  ConstantPointerNull,
  ConstantStruct,
  ConstantVector,
  Function,
  GlobalAlias,
  GlobalIFunc,
  GlobalVariable,
  UndefValue,
  PoisonValue,
  Instruction
};

/* llvalue -> ValueKind.t */
#define DEFINE_CASE(Val, Kind) \
    do {if (LLVMIsA##Kind(Val)) CAMLreturn(Val_int(Kind));} while(0)

value llvm_classify_value(value V) {
  CAMLparam1(V);
  LLVMValueRef Val = LLVMValue_val(V);
  if (!Val) {
    CAMLreturn(Val_int(NullValue));
  }
  if (LLVMIsAConstant(Val)) {
    DEFINE_CASE(Val, BlockAddress);
    DEFINE_CASE(Val, ConstantAggregateZero);
    DEFINE_CASE(Val, ConstantArray);
    DEFINE_CASE(Val, ConstantDataArray);
    DEFINE_CASE(Val, ConstantDataVector);
    DEFINE_CASE(Val, ConstantExpr);
    DEFINE_CASE(Val, ConstantFP);
    DEFINE_CASE(Val, ConstantInt);
    DEFINE_CASE(Val, ConstantPointerNull);
    DEFINE_CASE(Val, ConstantStruct);
    DEFINE_CASE(Val, ConstantVector);
  }
  if (LLVMIsAInstruction(Val)) {
    value result = caml_alloc_small(1, 0);
    Field(result, 0) = Val_int(LLVMGetInstructionOpcode(Val));
    CAMLreturn(result);
  }
  if (LLVMIsAGlobalValue(Val)) {
    DEFINE_CASE(Val, Function);
    DEFINE_CASE(Val, GlobalAlias);
    DEFINE_CASE(Val, GlobalIFunc);
    DEFINE_CASE(Val, GlobalVariable);
  }
  DEFINE_CASE(Val, Argument);
  DEFINE_CASE(Val, BasicBlock);
  DEFINE_CASE(Val, InlineAsm);
  DEFINE_CASE(Val, MDNode);
  DEFINE_CASE(Val, MDString);
  DEFINE_CASE(Val, UndefValue);
  DEFINE_CASE(Val, PoisonValue);
  failwith("Unknown Value class");
}

/* llvalue -> string */
value llvm_value_name(value Val) {
  CAMLparam1(Val);
  CAMLreturn(caml_copy_string(LLVMGetValueName(LLVMValue_val(Val))));
}

/* string -> llvalue -> unit */
value llvm_set_value_name(value Name, value Val) {
  CAMLparam2(Name, Val);
  LLVMSetValueName(LLVMValue_val(Val), String_val(Name));
  CAMLreturn(Val_unit);
}

/* llvalue -> unit */
value llvm_dump_value(value Val) {
  CAMLparam1(Val);
  LLVMDumpValue(LLVMValue_val(Val));
  CAMLreturn(Val_unit);
}

/* llvalue -> string */
value llvm_string_of_llvalue(value M) {
  CAMLparam1(M);
  CAMLlocal1(ValueStr);
  char *ValueCStr = LLVMPrintValueToString(LLVMValue_val(M));
  ValueStr = caml_copy_string(ValueCStr);
  LLVMDisposeMessage(ValueCStr);

  CAMLreturn(ValueStr);
}

/* llvalue -> llvalue -> unit */
value llvm_replace_all_uses_with(value OldVal, value NewVal) {
  CAMLparam2(OldVal, NewVal);
  LLVMReplaceAllUsesWith(LLVMValue_val(OldVal), LLVMValue_val(NewVal));
  CAMLreturn(Val_unit);
}

/*--... Operations on users ................................................--*/

/* llvalue -> int -> llvalue */
value llvm_operand(value V, value I) {
  CAMLparam2(V, I);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMGetOperand(LLVMValue_val(V), Int_val(I));
  CAMLreturn(Ret);
}

/* llvalue -> int -> lluse */
value llvm_operand_use(value V, value I) {
  CAMLparam2(V, I);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMUse_val(Ret) = LLVMGetOperandUse(LLVMValue_val(V), Int_val(I));
  CAMLreturn(Ret);
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_operand(value U, value I, value V) {
  CAMLparam3(U, I, V);
  LLVMSetOperand(LLVMValue_val(U), Int_val(I), LLVMValue_val(V));
  CAMLreturn(Val_unit);
}

/* llvalue -> int */
value llvm_num_operands(value V) {
  CAMLparam1(V);
  CAMLreturn(Val_int(LLVMGetNumOperands(LLVMValue_val(V))));
}

/* llvalue -> int array */
value llvm_indices(value In) {
  CAMLparam1(In);
  CAMLlocal1(indices);
  LLVMInstrRef Instr = LLVMInstr_val(In);
  unsigned n = LLVMGetNumIndices(Instr);
  const unsigned *Indices = LLVMGetIndices(Instr);
  indices = caml_alloc_tuple_uninit(n);
  for (unsigned i = 0; i < n; i++) {
    Op_val(indices)[i] = Val_int(Indices[i]);
  }
  CAMLreturn(indices);
}

/*--... Operations on constants of (mostly) any type .......................--*/

/* llvalue -> bool */
value llvm_is_constant(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsConstant(LLVMValue_val(Val))));
}

/* llvalue -> bool */
value llvm_is_null(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsNull(LLVMValue_val(Val))));
}

/* llvalue -> bool */
value llvm_is_undef(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsUndef(LLVMValue_val(Val))));
}

/* llvalue -> bool */
value llvm_is_poison(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsPoison(LLVMValue_val(Val))));
}

/* llvalue -> Opcode.t */
value llvm_constexpr_get_opcode(value Val) {
  CAMLparam1(Val);
  CAMLreturn(LLVMIsAConstantExpr(Val)
    ? Val_int(LLVMGetConstOpcode(LLVMValue_val(Val)))
    : Val_int(0));
}

/*--... Operations on instructions .........................................--*/

/* llvalue -> bool */
value llvm_has_metadata(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMHasMetadata(LLVMValue_val(Val))));
}

/* llvalue -> int -> llvalue option */
value llvm_metadata(value Val, value MDKindID) {
  CAMLparam2(Val, MDKindID);
  CAMLreturn(
    ptr_to_option(LLVMGetMetadata(LLVMValue_val(Val), Int_val(MDKindID))));
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_metadata(value Val, value MDKindID, value MD) {
  CAMLparam3(Val, MDKindID, MD);
  LLVMSetMetadata(LLVMValue_val(Val), Int_val(MDKindID), LLVMValue_val(MD));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> unit */
value llvm_clear_metadata(value Val, value MDKindID) {
  CAMLparam2(Val, MDKindID);
  LLVMSetMetadata(LLVMValue_val(Val), Int_val(MDKindID), NULL);
  CAMLreturn(Val_unit);
}

/*--... Operations on metadata .............................................--*/

/* llcontext -> string -> llvalue */
value llvm_mdstring(value C, value S) {
  CAMLparam2(C, S);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMMDStringInContext(LLVMContext_val(C), String_val(S),
                          caml_string_length(S));
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
LLVMValueRef llvm_mdnode(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int len = Wosize_val(ElementVals);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned i = 0; i < len; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMMDNodeInContext(LLVMContext_val(C), (LLVMValueRef*)Temp, len);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue */
value llvm_mdnull(value C) {
  CAMLparam1(C);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = NULL;
  CAMLreturn(Ret);
}

/* llvalue -> string option */
value llvm_get_mdstring(value V) {
  CAMLparam1(V);
  unsigned Len;
  const char *CStr = LLVMGetMDString(LLVMValue_val(V), &Len);
  CAMLreturn(cstr_to_string_option(CStr, Len));
}

/* llvalue -> llvalue array */
value llvm_get_mdnode_operands(value Value) {
  CAMLparam1(Value);
  CAMLlocal2(Temp, Operands);
  LLVMValueRef V = LLVMValue_val(Value);
  unsigned int n = LLVMGetMDNodeNumOperands(V);
  Operands = caml_alloc_tuple_uninit(n);
  Temp = caml_alloc(n, Abstract_tag);
  LLVMGetMDNodeOperands(V, (LLVMValueRef*) Temp);
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    LLVMValue_val(Box) = Field(Temp, i);
    Field(Operands, i) = Box;
  }
  CAMLreturn(Operands);
}

/* llmodule -> string -> llvalue array */
value llvm_get_namedmd(value M, value Name) {
  CAMLparam2(M, Name);
  CAMLlocal1(Nodes, Temp);
  unsigned int n =
    LLVMGetNamedMetadataNumOperands(LLVMModule_val(M), String_val(Name));
  Nodes = caml_alloc_tuple_uninit(n);
  Temp = caml_alloc(n, Abstract_tag);
  LLVMGetNamedMetadataOperands(LLVMModule_val(M), String_val(Name),
                               (LLVMValueRef*)Temp);
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    LLVMValue_val(Box) = Field(Temp, i);
    Field(Nodes, i) = Box;
  }
  CAMLreturn(Nodes);
}

/* llmodule -> string -> llvalue -> unit */
value llvm_append_namedmd(value M, value Name, value Val) {
  CAMLparam3(M, Name, Val);
  LLVMAddNamedMetadataOperand(LLVMModule_val(M), String_val(Name),
                              LLVMValue_val(Val));
  CAMLreturn(Val_unit);
}

/* llvalue -> llmetadata */
value llvm_value_as_metadata(value Val) {
  CAMLparam1(Val);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMMetadata_val(Ret) = LLVMValueAsMetadata(LLVMValue_val(Val));
  CAMLreturn(Ret);
}

/* llcontext -> llmetadata -> llvalue */
value llvm_metadata_as_value(value C, value MD) {
  CAMLparam2(C, MD);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMMetadataAsValue(LLVMContext_val(C), LLVMMetadata_val(MD));
  CAMLreturn(Ret);
}

/*--... Operations on scalar constants .....................................--*/

/* lltype -> int -> llvalue */
value llvm_const_int(value IntTy, value N) {
  CAMLparam2(IntTy, N);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstInt(LLVMType_val(IntTy), (long long)Long_val(N), 1);
  CAMLreturn(Ret);
}

/* lltype -> Int64.t -> bool -> llvalue */
value llvm_const_of_int64(value IntTy, value N, value SExt) {
  CAMLparam3(IntTy, N, SExt);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstInt(LLVMType_val(IntTy), Int64_val(N), Bool_val(SExt));
  CAMLreturn(Ret);
}

/* llvalue -> Int64.t option */
value llvm_int64_of_const(value C) {
  CAMLparam1(C);
  LLVMValueRef Const = LLVMValue_val(C);
  if (!(LLVMIsAConstantInt(Const)) ||
      !(LLVMGetIntTypeWidth(LLVMTypeOf(Const)) <= 64)) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(caml_copy_int64(LLVMConstIntGetSExtValue(Const))));
}

/* lltype -> string -> int -> llvalue */
value llvm_const_int_of_string(value IntTy, value S, value Radix) {
  CAMLparam3(IntTy, S, Radix);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstIntOfStringAndSize(LLVMType_val(IntTy), String_val(S),
                                caml_string_length(S), Int_val(Radix));
  CAMLreturn(Ret);
}

/* lltype -> float -> llvalue */
value llvm_const_float(value RealTy, value N) {
  CAMLparam2(RealTy, N);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMConstReal(LLVMType_val(RealTy), Double_val(N));
  CAMLreturn(Ret);
}

/* llvalue -> float option */
value llvm_float_of_const(value C) {
  CAMLparam1(C);
  LLVMValueRef Const = LLVMValue_val(C);
  LLVMBool LosesInfo;
  double Result;
  if (!LLVMIsAConstantFP(Const)) {
    CAMLreturn(Val_none);
  }
  Result = LLVMConstRealGetDouble(Const, &LosesInfo);
  if (LosesInfo) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(caml_copy_double(Result)));
}

/* lltype -> string -> llvalue */
value llvm_const_float_of_string(value RealTy, value S) {
  CAMLparam2(RealTy, S);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstRealOfStringAndSize(LLVMType_val(RealTy), String_val(S),
                                 caml_string_length(S));
  CAMLreturn(Ret);
}

/*--... Operations on composite constants ..................................--*/

/* llcontext -> string -> llvalue */
value llvm_const_string(value Context, value Str, value NullTerminate) {
  CAMLparam3(Context, Str, NullTerminate);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstStringInContext(LLVMContext_val(Context), String_val(Str),
                             string_length(Str), 1);
  CAMLreturn(Ret);
}

/* llcontext -> string -> llvalue */
value llvm_const_stringz(value Context, value Str, value NullTerminate) {
  CAMLparam3(Context, Str, NullTerminate);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstStringInContext(LLVMContext_val(Context), String_val(Str),
                             string_length(Str), 0);
  CAMLreturn(Ret);
}

/* lltype -> llvalue array -> llvalue */
value llvm_const_array(value ElementTy, value ElementVals) {
  CAMLparam2(ElementTy, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstArray(LLVMType_val(ElementTy), (LLVMValueRef*)temp, n);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
value llvm_const_struct(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstStructInContext(LLVMContext_val(C), (LLVMValueRef*)temp, n, 0);
  CAMLreturn(Ret);
}

/* lltype -> llvalue array -> llvalue */
value llvm_const_named_struct(value Ty, value ElementVals) {
  CAMLparam2(Ty, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstNamedStruct(LLVMType_val(Ty), (LLVMValueRef*)temp, n);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
value llvm_const_packed_struct(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstStructInContext(LLVMContext_val(C), (LLVMValueRef*)temp, n, 1);
  CAMLreturn(Ret);
}

/* llvalue array -> llvalue */
value llvm_const_vector(value ElementVals) {
  CAMLparam1(ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMConstVector((LLVMValueRef*) Temp, n);
  CAMLreturn(Ret);
}

/* llvalue -> string option */
value llvm_string_of_const(value C) {
  CAMLparam1(C);
  size_t Len;
  const char *CStr;
  LLVMValueRef Const = LLVMValue_val(C);
  if (!LLVMIsAConstantDataSequential(Const) || !LLVMIsConstantString(Const)) {
    CAMLreturn(Val_none);
  }
  CStr = LLVMGetAsString(Const, &Len);
  CAMLreturn(cstr_to_string_option(CStr, Len));
}

/* llvalue -> int -> llvalue */
value llvm_const_element(value Const, value N) {
  CAMLparam2(Const, N);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMGetElementAsConstant(LLVMValue_val(Const), Int_val(N));
  CAMLreturn(Ret);
}

/*--... Constant expressions ...............................................--*/

/* Icmp.t -> llvalue -> llvalue -> llvalue */
value llvm_const_icmp(value Pred, value LHSConstant, value RHSConstant) {
  CAMLparam3(Pred, LHSConstant, RHSConstant);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstICmp(Int_val(Pred) + LLVMIntEQ,
                  LLVMValue_val(LHSConstant), LLVMValue_val(RHSConstant));
  CAMLreturn(Ret);
}

/* Fcmp.t -> llvalue -> llvalue -> llvalue */
value llvm_const_fcmp(value Pred, value LHSConstant, value RHSConstant) {
  CAMLparam3(Pred, LHSConstant, RHSConstant);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstFCmp(Int_val(Pred),
                  LLVMValue_val(LHSConstant), LLVMValue_val(RHSConstant));
  CAMLreturn(Ret);
}

/* llvalue -> llvalue array -> llvalue */
value llvm_const_gep(value ConstantVal, value Indices) {
  CAMLparam2(ConstantVal, Indices);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(Indices);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstGEP(LLVMValue_val(ConstantVal), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* lltype -> llvalue -> llvalue array -> llvalue */
value llvm_const_gep2(value Ty, value ConstantVal, value Indices) {
  CAMLparam3(Ty, ConstantVal, Indices);
  CAMLlocal2(temp, Ret);
  unsigned int n = Wosize_val(Indices);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstGEP2(LLVMType_val(Ty), LLVMValue_val(ConstantVal),
                  (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* llvalue -> llvalue array -> llvalue */
value llvm_const_in_bounds_gep(value ConstantVal, value Indices) {
  CAMLparam2(ConstantVal, Indices);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(Indices);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = LLVMValue_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstInBoundsGEP(LLVMValue_val(ConstantVal), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* llvalue -> lltype -> is_signed:bool -> llvalue */
value llvm_const_intcast(value CV, value T, value IsSigned) {
  CAMLparam3(CV, T, IsSigned);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstIntCast(LLVMValue_val(CV), LLVMType_val(T), Bool_val(IsSigned));
  CAMLreturn(Ret);
}

/* lltype -> string -> string -> bool -> bool -> llvalue */
value llvm_const_inline_asm(value Ty, value Asm, value Constraints,
                            value HasSideEffects, value IsAlignStack) {
  CAMLparam5(Ty, Asm, Constraints, HasSideEffects, IsAlignStack);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMConstInlineAsm(LLVMType_val(Ty), String_val(Asm),
                       String_val(Constraints), Bool_val(HasSideEffects),
                       Bool_val(IsAlignStack));
  CAMLreturn(Ret);
}

/*--... Operations on global variables, functions, and aliases (globals) ...--*/

/* llvalue -> bool */
value llvm_is_declaration(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_bool(LLVMIsDeclaration(LLVMValue_val(Global))));
}

/* llvalue -> Linkage.t */
value llvm_linkage(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetLinkage(LLVMValue_val(Global))));
}

/* Linkage.t -> llvalue -> unit */
value llvm_set_linkage(value Linkage, value Global) {
  CAMLparam2(Linkage, Global);
  LLVMSetLinkage(LLVMValue_val(Global), Int_val(Linkage));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_unnamed_addr(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_bool(LLVMHasUnnamedAddr(LLVMValue_val(Global))));
}

/* bool -> llvalue -> unit */
value llvm_set_unnamed_addr(value UseUnnamedAddr, value Global) {
  CAMLparam2(UseUnnamedAddr, Global);
  LLVMSetUnnamedAddr(LLVMValue_val(Global), Bool_val(UseUnnamedAddr));
  CAMLreturn(Val_unit);
}

/* llvalue -> string */
value llvm_section(value Global) {
  CAMLparam1(Global);
  CAMLreturn(caml_copy_string(LLVMGetSection(LLVMValue_val(Global))));
}

/* string -> llvalue -> unit */
value llvm_set_section(value Section, value Global) {
  CAMLparam2(Section, Global);
  LLVMSetSection(LLVMValue_val(Global), String_val(Section));
  CAMLreturn(Val_unit);
}

/* llvalue -> Visibility.t */
value llvm_visibility(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetVisibility(LLVMValue_val(Global))));
}

/* Visibility.t -> llvalue -> unit */
value llvm_set_visibility(value Viz, value Global) {
  CAMLparam2(Viz, Global);
  LLVMSetVisibility(LLVMValue_val(Global), Int_val(Viz));
  CAMLreturn(Val_unit);
}

/* llvalue -> DLLStorageClass.t */
value llvm_dll_storage_class(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetDLLStorageClass(LLVMValue_val(Global))));
}

/* DLLStorageClass.t -> llvalue -> unit */
value llvm_set_dll_storage_class(value Viz, value Global) {
  CAMLparam2(Viz, Global);
  LLVMSetDLLStorageClass(LLVMValue_val(Global), Int_val(Viz));
  CAMLreturn(Val_unit);
}

/* llvalue -> int */
value llvm_alignment(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetAlignment(LLVMValue_val(Global))));
}

/* int -> llvalue -> unit */
value llvm_set_alignment(value Bytes, value Global) {
  CAMLparam2(Bytes, Global);
  LLVMSetAlignment(LLVMValue_val(Global), Int_val(Bytes));
  CAMLreturn(Val_unit);
}

/* llvalue -> (llmdkind * llmetadata) array */
value llvm_global_copy_all_metadata(value Global) {
  CAMLparam1(Global);
  CAMLlocal1(Array);
  size_t NumEntries;
  LLVMValueMetadataEntry *Entries =
      LLVMGlobalCopyAllMetadata(LLVMValue_val(Global), &NumEntries);
  Array = caml_alloc_tuple(NumEntries);
  for (int i = 0; i < NumEntries; i++) {
    value Metadata = caml_alloc(1, Abstract_tag);
    LLVMMetadata_val(Metadata) =
      LLVMValueMetadataEntriesGetMetadata(Entries, i);
    value Pair = caml_alloc_small(2, 0);
    Field(Pair, 0) = Val_int(LLVMValueMetadataEntriesGetKind(Entries, i));
    Field(Pair, 1) = Metadata;
    Store_field(Array, i, Pair);
  }
  LLVMDisposeValueMetadataEntries(Entries);
  CAMLreturn(Array);
}

/*--... Operations on uses .................................................--*/

/* llvalue -> lluse option */
value llvm_use_begin(value Val) {
  CAMLparam1(Val);
  CAMLreturn(ptr_to_option(LLVMGetFirstUse(LLVMValue_val(Val))));
}

/* lluse -> lluse option */
value llvm_use_succ(value U) {
  CAMLparam1(U);
  CAMLreturn(ptr_to_option(LLVMGetNextUse(LLVMUse_val(U))));
}

/* lluse -> llvalue */
value llvm_user(value UR) {
  CAMLparam1(UR);
  CAMLreturn(LLVMGetUser(LLVMUse_val(UR)));
}

/* lluse -> llvalue */
LLVMValueRef llvm_used_value(value UR) {
  CAMLparam1(UR);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMGetUsedValue(LLVMUse_val(UR));
  CAMLreturn(Ret);
}

/*--... Operations on global variables .....................................--*/

DEFINE_ITERATORS(global, Global, LLVMModuleRef, LLVMValueRef,
                 LLVMGetGlobalParent)

/* lltype -> string -> llmodule -> llvalue */
value llvm_declare_global(value Ty, value Name, value M) {
  CAMLparam3(Ty, Name, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar;
  if ((GlobalVar = LLVMGetNamedGlobal(LLVMModule_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(GlobalVar) != LLVMType_val(Ty)) {
      LLVMValue_val(Ret) =
        LLVMConstBitCast(GlobalVar, LLVMPointerType(LLVMType_val(Ty), 0));
      CAMLreturn(Ret);
    }
    LLVMValue_val(Ret) = GlobalVar;
    CAMLreturn(Ret);
  }
  LLVMValue_val(Ret) = LLVMAddGlobal(M, Ty, String_val(Name));
  CAMLreturn(Ret);
}

/* lltype -> string -> int -> llmodule -> llvalue */
value llvm_declare_qualified_global(value Ty, value Name, value AddressSpace,
                                    value M) {
  CAMLparam4(Ty, Name, AddressSpace, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar;
  if ((GlobalVar = LLVMGetNamedGlobal(LLVMModule_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(GlobalVar) != LLVMType_val(Ty)) {
      LLVMValue_val(Ret) =
        LLVMConstBitCast(GlobalVar, LLVMPointerType(LLVMType_val(Ty),
                         Int_val(AddressSpace)));
      CAMLreturn(Ret);
    }
    LLVMValue_val(Ret) = GlobalVar;
    CAMLreturn(Ret);
  }
  LLVMValue_val(Ret) =
    LLVMAddGlobalInAddressSpace(LLVMModule_val(M), LLVMType_val(Ty),
                                String_val(Name), Int_val(AddressSpace));
  CAMLreturn(Ret);
}

/* string -> llmodule -> llvalue option */
value llvm_lookup_global(value Name, value M) {
  CAMLparam2(Name, M);
  CAMLreturn(
    ptr_to_option(LLVMGetNamedGlobal(LLVMModule_val(M), String_val(Name))));
}

/* string -> llvalue -> llmodule -> llvalue */
value llvm_define_global(value Name, value Initializer, value M) {
  LLVMparam3(Name, Initializer, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar =
      LLVMAddGlobal(LLVMModule_val(M), LLVMTypeOf(LLVMValue_val(Initializer)),
                    String_val(Name));
  LLVMSetInitializer(GlobalVar, LLVMValue_val(Initializer));
  LLVMValue_val(Ret) = GlobalVar;
  CAMLreturn(Ret);
}

/* string -> llvalue -> int -> llmodule -> llvalue */
value llvm_define_qualified_global(value Name, value Initializer,
                                   value AddressSpace, value M) {
  CAMLparam4(Name, Initializer, AddressSpace, M);
  CAMllocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar = LLVMAddGlobalInAddressSpace(
      LLVMModule_val(M), LLVMTypeOf(LLVMValue_val(Initializer)),
      String_val(Name), Int_val(AddressSpace));
  LLVMSetInitializer(GlobalVar, LLVMValue_val(Initializer));
  LLVMValue_val(Ret) = GlobalVar;
  CAMLreturn(Ret);
}

/* llvalue -> unit */
value llvm_delete_global(value GlobalVar) {
  CAMLparam1(GlobalVar);
  LLVMDeleteGlobal(LLVMValue_val(GlobalVar));
  CAMLreturn(Val_unit);
}

/* llvalue -> llvalue option */
value llvm_global_initializer(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(ptr_to_option(LLVMGetInitializer(LLVMValue_val(GlobalVar))));
}

/* llvalue -> llvalue -> unit */
value llvm_set_initializer(value ConstantVal, value GlobalVar) {
  CAMLparam2(ConstantVal, GlobalVar);
  LLVMSetInitializer(LLVMValue_val(GlobalVar), LLVMValue_val(ConstantVal));
  CAMLreturn(Val_unit);
}

/* llvalue -> unit */
value llvm_remove_initializer(value GlobalVar) {
  CAMLparam1(GlobalVar);
  LLVMSetInitializer(LLVMValue_val(GlobalVar), NULL);
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_thread_local(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsThreadLocal(LLVMValue_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_thread_local(value IsThreadLocal, value GlobalVar) {
  CAMLparam2(IsThreadLocal, GlobalVar);
  LLVMSetThreadLocal(LLVMValue_val(GlobalVar), Bool_val(IsThreadLocal));
  CAMLreturn(Val_unit);
}

/* llvalue -> ThreadLocalMode.t */
value llvm_thread_local_mode(LLVMValueRef GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_int(LLVMGetThreadLocalMode(LLVMValue_val(GlobalVar))));
}

/* ThreadLocalMode.t -> llvalue -> unit */
value llvm_set_thread_local_mode(value ThreadLocalMode, value GlobalVar) {
  CAMLparam2(ThreadLocalMode, GlobalVar);
  LLVMSetThreadLocalMode(LLVMValue_val(GlobalVar), Int_val(ThreadLocalMode));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_externally_initialized(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsExternallyInitialized(LLVMValue_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_externally_initialized(value IsExternallyInitialized,
                                      value GlobalVar) {
  CAMLparam2(IsExternallyInitialized, GlobalVar);
  LLVMSetExternallyInitialized(LLVMValue_val(GlobalVar),
                               Bool_val(IsExternallyInitialized));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_global_constant(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsGlobalConstant(LLVMValue_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_global_constant(value Flag, value GlobalVar) {
  CAMLparam2(Flag, GlobalVar);
  LLVMSetGlobalConstant(LLVMValue_val(GlobalVar), Bool_val(Flag));
  CAMLreturn(Val_unit);
}

/*--... Operations on aliases ..............................................--*/

/* llmodule -> lltype -> llvalue -> string -> llvalue */
value llvm_add_alias(value M, value Ty, value Aliasee, value Name) {
  CAMLparam4(M, Ty, Aliasee, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMAddAlias(LLVMMoule_val(M), LLVMType_val(Ty),
                                    LLVMValue_val(Aliasee), String_val(Name));
  CAMLreturn(Ret);
}

/* llmodule -> lltype -> int -> llvalue -> string -> llvalue */
value llvm_add_alias2(value M, value ValueTy, value AddrSpace,
                      value Aliasee, value Name) {
  CAMLparam5(M, ValueTy, AddrSpace, Aliasee, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) =
    LLVMAddAlias2(LLVMModule_val(M), LLVMTType_val(ValueTy),
                  Int_val(AddrSpace), LLVMValue_val(Aliasee), String_val(Name));
  CAMLreturn(Ret);
}

/*--... Operations on functions ............................................--*/

DEFINE_ITERATORS(function, Function, LLVMModuleRef, LLVMValueRef,
                 LLVMGetGlobalParent)

/* string -> lltype -> llmodule -> llvalue */
value llvm_declare_function(value Name, value Ty, value M) {
  CAMLparam3(Name, Ty, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef Fn;
  if ((Fn = LLVMGetNamedFunction(LLVMModule_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(Fn) != LLVMType_val(Ty)) {
      LLVMValue_val(Ret) =
        LLVMConstBitCast(Fn, LLVMPointerType(LLVMType_val(Ty), 0));
      CAMLreturn(Ret);
    }
    LLVMValue_val(Ret) = Fn;
    CAMLreturn(Ret);
  }
  LLVMValue_val(Ret) =
    LLVMAddFunction(LLVMModule_val(M), String_val(Name), LLVMType_val(Ty));
  CAMLreturn(Ret);
}

/* string -> llmodule -> llvalue option */
value llvm_lookup_function(value Name, value M) {
  CAMLparam2(Name, M);
  CAMLreturn(
    ptr_to_option(LLVMGetNamedFunction(LLVMModule_val(M), String_val(Name))));
}

/* string -> lltype -> llmodule -> llvalue */
value llvm_define_function(value Name, value Ty, value M) {
  CAMLparam3(Name, Ty, M);
  LLVMValueRef Fn =
    LLVMAddFunction(LLVMModule_val(M), String_val(Name), LLVMType_val(Ty));
  LLVMAppendBasicBlockInContext(LLVMGetTypeContext(LLVMType_val(Ty)),
                                Fn, "entry");
  LLVMValue_val(Ret) = Fn;
  CAMLreturn(Ret);
}

/* llvalue -> unit */
value llvm_delete_function(value Fn) {
  CAMLparam1(Fn);
  LLVMDeleteFunction(LLVMValue_val(Fn));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_intrinsic(value Fn) {
  CAMLparam1(Fn);
  CAMLreturn(Val_bool(LLVMGetIntrinsicID(LLVMValue_val(Fn))));
}

/* llvalue -> int */
value llvm_function_call_conv(value Fn) {
  CAMLparam1(Fn);
  CAMLreturn(Val_int(LLVMGetFunctionCallConv(LLVMValue_val(Fn))));
}

/* int -> llvalue -> unit */
value llvm_set_function_call_conv(value Id, value Fn) {
  CAMLparam1(Fn);
  LLVMSetFunctionCallConv(LLVMValue_val(Fn), Int_val(Id));
  CAMLreturn(Val_unit);
}

/* llvalue -> string option */
value llvm_gc(value Fn) {
  CAMLparam1(Fn);
  const char *GC = LLVMGetGC(LLVMValue_val(Fn));
  if (!GC) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(caml_copy_string(GC)));
}

/* string option -> llvalue -> unit */
value llvm_set_gc(value GC, LLVMValueRef Fn) {
  CAMLparam2(GC, Fn);
  LLVMSetGC(LLVMValue_val(Fn), GC == Val_none ? 0 : String_val(Field(GC, 0)));
  CAMLreturn(Val_unit);
}

/* llvalue -> llattribute -> int -> unit */
value llvm_add_function_attr(value F, value A, value Index) {
  CAMLparam3(F, A, Index);
  LLVMAddAttributeAtIndex(LLVMValue_val(F), Int_val(Index),
                          LLVMAttribtue_val(A));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> llattribute array */
value llvm_function_attrs(value F, value Index) {
  CAMLparam2(F, Index);
  CAMLlocal2(Array, Temp);
  unsigned Length = LLVMGetAttributeCountAtIndex(F, Int_val(Index));
  Array = caml_alloc_tuple_uninit(Length);
  Temp = caml_alloc(Length, Abstract_tag);
  LLVMGetAttributesAtIndex(F, Int_val(Index),
                           (LLVMAttributeRef *)Op_val(Temp));
  for (unsigned int i = 0; i < Length; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    LLVMAttribute_val(Box) = Field(Temp, i);
    Field(Array, i) = Box;
  }
  CAMLreturn(Array);
}

/* llvalue -> llattrkind -> int -> unit */
value llvm_remove_enum_function_attr(value F, value Kind, value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveEnumAttributeAtIndex(LLVMValue_val(F), Int_val(Index),
                                 Int_val(Kind));
  CAMLreturn(Val_unit);
}

/* llvalue -> string -> int -> unit */
value llvm_remove_string_function_attr(value F, value Kind,
                                       value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveStringAttributeAtIndex(LLVMValue_val(F), Int_val(Index),
                                   String_val(Kind),
                                   caml_string_length(Kind));
  CAMLreturn(Val_unit);
}

/*--... Operations on parameters ...........................................--*/

DEFINE_ITERATORS(param, Param, LLVMValueRef, LLVMValueRef, LLVMGetParamParent)

/* llvalue -> int -> llvalue */
value llvm_param(value Fn, value Index) {
  CAMLparam2(Fn, Index);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValue_val(Ret) = LLVMGetParam(LLVMValue_val(Fn), Int_val(Index));
  CAMLreturn(Ret);
}

/* llvalue -> llvalue */
value llvm_params(value Fn) {
  CAMLparam1(Fn);
  CAMLlocal1(Params);
  Params = caml_alloc_tuple_uninit(LLVMCountParams(LLVMValue_val(Fn)));
  LLVMGetParams(Fn, (LLVMValueRef *)Op_val(Params));
  CAMLreturn(Params);
}

/*--... Operations on basic blocks .........................................--*/

DEFINE_ITERATORS(block, BasicBlock, LLVMValueRef, LLVMBasicBlockRef,
                 LLVMGetBasicBlockParent)

/* llbasicblock -> llvalue option */
value llvm_block_terminator(LLVMBasicBlockRef Block) {
  return ptr_to_option(LLVMGetBasicBlockTerminator(Block));
}

/* llvalue -> llbasicblock array */
value llvm_basic_blocks(LLVMValueRef Fn) {
  value MLArray = caml_alloc_tuple_uninit(LLVMCountBasicBlocks(Fn));
  LLVMGetBasicBlocks(Fn, (LLVMBasicBlockRef *)Op_val(MLArray));
  return MLArray;
}

/* llbasicblock -> unit */
value llvm_delete_block(LLVMBasicBlockRef BB) {
  LLVMDeleteBasicBlock(BB);
  return Val_unit;
}

/* llbasicblock -> unit */
value llvm_remove_block(LLVMBasicBlockRef BB) {
  LLVMRemoveBasicBlockFromParent(BB);
  return Val_unit;
}

/* llbasicblock -> llbasicblock -> unit */
value llvm_move_block_before(LLVMBasicBlockRef Pos, LLVMBasicBlockRef BB) {
  LLVMMoveBasicBlockBefore(BB, Pos);
  return Val_unit;
}

/* llbasicblock -> llbasicblock -> unit */
value llvm_move_block_after(LLVMBasicBlockRef Pos, LLVMBasicBlockRef BB) {
  LLVMMoveBasicBlockAfter(BB, Pos);
  return Val_unit;
}

/* string -> llvalue -> llbasicblock */
LLVMBasicBlockRef llvm_append_block(LLVMContextRef Context, value Name,
                                    LLVMValueRef Fn) {
  return LLVMAppendBasicBlockInContext(Context, Fn, String_val(Name));
}

/* string -> llbasicblock -> llbasicblock */
LLVMBasicBlockRef llvm_insert_block(LLVMContextRef Context, value Name,
                                    LLVMBasicBlockRef BB) {
  return LLVMInsertBasicBlockInContext(Context, BB, String_val(Name));
}

/* llvalue -> bool */
value llvm_value_is_block(LLVMValueRef Val) {
  return Val_bool(LLVMValueIsBasicBlock(Val));
}

/*--... Operations on instructions .........................................--*/

DEFINE_ITERATORS(instr, Instruction, LLVMBasicBlockRef, LLVMValueRef,
                 LLVMGetInstructionParent)

/* llvalue -> Opcode.t */
value llvm_instr_get_opcode(LLVMValueRef Inst) {
  LLVMOpcode o;
  if (!LLVMIsAInstruction(Inst))
    failwith("Not an instruction");
  o = LLVMGetInstructionOpcode(Inst);
  assert(o <= LLVMFreeze);
  return Val_int(o);
}

/* llvalue -> ICmp.t option */
value llvm_instr_icmp_predicate(LLVMValueRef Val) {
  int x = LLVMGetICmpPredicate(Val);
  if (!x)
    return Val_none;
  return caml_alloc_some(Val_int(x - LLVMIntEQ));
}

/* llvalue -> FCmp.t option */
value llvm_instr_fcmp_predicate(LLVMValueRef Val) {
  int x = LLVMGetFCmpPredicate(Val);
  if (!x)
    return Val_none;
  return caml_alloc_some(Val_int(x - LLVMRealPredicateFalse));
}

/* llvalue -> llvalue */
LLVMValueRef llvm_instr_clone(LLVMValueRef Inst) {
  if (!LLVMIsAInstruction(Inst))
    failwith("Not an instruction");
  return LLVMInstructionClone(Inst);
}

/*--... Operations on call sites ...........................................--*/

/* llvalue -> int */
value llvm_instruction_call_conv(LLVMValueRef Inst) {
  return Val_int(LLVMGetInstructionCallConv(Inst));
}

/* int -> llvalue -> unit */
value llvm_set_instruction_call_conv(value CC, LLVMValueRef Inst) {
  LLVMSetInstructionCallConv(Inst, Int_val(CC));
  return Val_unit;
}

/* llvalue -> llattribute -> int -> unit */
value llvm_add_call_site_attr(LLVMValueRef F, LLVMAttributeRef A, value Index) {
  LLVMAddCallSiteAttribute(F, Int_val(Index), A);
  return Val_unit;
}

/* llvalue -> int -> llattribute array */
value llvm_call_site_attrs(LLVMValueRef F, value Index) {
  unsigned Count = LLVMGetCallSiteAttributeCount(F, Int_val(Index));
  value Array = caml_alloc_tuple_uninit(Count);
  LLVMGetCallSiteAttributes(F, Int_val(Index),
                            (LLVMAttributeRef *)Op_val(Array));
  return Array;
}

/* llvalue -> llattrkind -> int -> unit */
value llvm_remove_enum_call_site_attr(LLVMValueRef F, value Kind, value Index) {
  LLVMRemoveCallSiteEnumAttribute(F, Int_val(Index), Int_val(Kind));
  return Val_unit;
}

/* llvalue -> string -> int -> unit */
value llvm_remove_string_call_site_attr(LLVMValueRef F, value Kind,
                                        value Index) {
  LLVMRemoveCallSiteStringAttribute(F, Int_val(Index), String_val(Kind),
                                    caml_string_length(Kind));
  return Val_unit;
}

/*--... Operations on call instructions (only) .............................--*/

/* llvalue -> int */
value llvm_num_arg_operands(LLVMValueRef V) {
  return Val_int(LLVMGetNumArgOperands(V));
}

/* llvalue -> bool */
value llvm_is_tail_call(LLVMValueRef CallInst) {
  return Val_bool(LLVMIsTailCall(CallInst));
}

/* bool -> llvalue -> unit */
value llvm_set_tail_call(value IsTailCall, LLVMValueRef CallInst) {
  LLVMSetTailCall(CallInst, Bool_val(IsTailCall));
  return Val_unit;
}

/*--... Operations on load/store instructions (only)........................--*/

/* llvalue -> bool */
value llvm_is_volatile(LLVMValueRef MemoryInst) {
  return Val_bool(LLVMGetVolatile(MemoryInst));
}

/* bool -> llvalue -> unit */
value llvm_set_volatile(value IsVolatile, LLVMValueRef MemoryInst) {
  LLVMSetVolatile(MemoryInst, Bool_val(IsVolatile));
  return Val_unit;
}

/*--.. Operations on terminators ...........................................--*/

/* llvalue -> int -> llbasicblock */
LLVMBasicBlockRef llvm_successor(LLVMValueRef V, value I) {
  return LLVMGetSuccessor(V, Int_val(I));
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_successor(LLVMValueRef U, value I, LLVMBasicBlockRef B) {
  LLVMSetSuccessor(U, Int_val(I), B);
  return Val_unit;
}

/* llvalue -> int */
value llvm_num_successors(LLVMValueRef V) {
  return Val_int(LLVMGetNumSuccessors(V));
}

/*--.. Operations on branch ................................................--*/

/* llvalue -> llvalue */
LLVMValueRef llvm_condition(LLVMValueRef V) { return LLVMGetCondition(V); }

/* llvalue -> llvalue -> unit */
value llvm_set_condition(LLVMValueRef B, LLVMValueRef C) {
  LLVMSetCondition(B, C);
  return Val_unit;
}

/* llvalue -> bool */
value llvm_is_conditional(LLVMValueRef V) {
  return Val_bool(LLVMIsConditional(V));
}

/*--... Operations on phi nodes ............................................--*/

/* (llvalue * llbasicblock) -> llvalue -> unit */
value llvm_add_incoming(value Incoming, LLVMValueRef PhiNode) {
  LLVMAddIncoming(PhiNode, (LLVMValueRef *)&Field(Incoming, 0),
                  (LLVMBasicBlockRef *)&Field(Incoming, 1), 1);
  return Val_unit;
}

/* llvalue -> (llvalue * llbasicblock) list */
value llvm_incoming(LLVMValueRef PhiNode) {
  unsigned I;
  CAMLparam0();
  CAMLlocal2(Hd, Tl);

  /* Build a tuple list of them. */
  Tl = Val_int(0);
  for (I = LLVMCountIncoming(PhiNode); I != 0;) {
    Hd = caml_alloc_small(2, 0);
    Field(Hd, 0) = (value)LLVMGetIncomingValue(PhiNode, --I);
    Field(Hd, 1) = (value)LLVMGetIncomingBlock(PhiNode, I);

    value Tmp = caml_alloc_small(2, 0);
    Field(Tmp, 0) = Hd;
    Field(Tmp, 1) = Tl;
    Tl = Tmp;
  }

  CAMLreturn(Tl);
}

/* llvalue -> unit */
value llvm_delete_instruction(LLVMValueRef Instruction) {
  LLVMInstructionEraseFromParent(Instruction);
  return Val_unit;
}

/*===-- Instruction builders ----------------------------------------------===*/

#define Builder_val(v) (*(LLVMBuilderRef *)(Data_custom_val(v)))

static void llvm_finalize_builder(value B) {
  LLVMDisposeBuilder(Builder_val(B));
}

static struct custom_operations builder_ops = {
    (char *)"Llvm.llbuilder",  llvm_finalize_builder,
    custom_compare_default,    custom_hash_default,
    custom_serialize_default,  custom_deserialize_default,
    custom_compare_ext_default};

static value alloc_builder(LLVMBuilderRef B) {
  value V = alloc_custom(&builder_ops, sizeof(LLVMBuilderRef), 0, 1);
  Builder_val(V) = B;
  return V;
}

/* llcontext -> llbuilder */
value llvm_builder(LLVMContextRef C) {
  return alloc_builder(LLVMCreateBuilderInContext(C));
}

/* (llbasicblock, llvalue) llpos -> llbuilder -> unit */
value llvm_position_builder(value Pos, value B) {
  if (Tag_val(Pos) == 0) {
    LLVMBasicBlockRef BB = (LLVMBasicBlockRef)Op_val(Field(Pos, 0));
    LLVMPositionBuilderAtEnd(Builder_val(B), BB);
  } else {
    LLVMValueRef I = (LLVMValueRef)Op_val(Field(Pos, 0));
    LLVMPositionBuilderBefore(Builder_val(B), I);
  }
  return Val_unit;
}

/* llbuilder -> llbasicblock */
LLVMBasicBlockRef llvm_insertion_block(value B) {
  LLVMBasicBlockRef InsertBlock = LLVMGetInsertBlock(Builder_val(B));
  if (!InsertBlock)
    caml_raise_not_found();
  return InsertBlock;
}

/* llvalue -> string -> llbuilder -> unit */
value llvm_insert_into_builder(LLVMValueRef I, value Name, value B) {
  LLVMInsertIntoBuilderWithName(Builder_val(B), I, String_val(Name));
  return Val_unit;
}

/*--... Metadata ...........................................................--*/

/* llbuilder -> llvalue -> unit */
value llvm_set_current_debug_location(value B, LLVMValueRef V) {
  LLVMSetCurrentDebugLocation(Builder_val(B), V);
  return Val_unit;
}

/* llbuilder -> unit */
value llvm_clear_current_debug_location(value B) {
  LLVMSetCurrentDebugLocation(Builder_val(B), NULL);
  return Val_unit;
}

/* llbuilder -> llvalue option */
value llvm_current_debug_location(value B) {
  return ptr_to_option(LLVMGetCurrentDebugLocation(Builder_val(B)));
}

/* llbuilder -> llvalue -> unit */
value llvm_set_inst_debug_location(value B, LLVMValueRef V) {
  LLVMSetInstDebugLocation(Builder_val(B), V);
  return Val_unit;
}

/*--... Terminators ........................................................--*/

/* llbuilder -> llvalue */
LLVMValueRef llvm_build_ret_void(value B) {
  return LLVMBuildRetVoid(Builder_val(B));
}

/* llvalue -> llbuilder -> llvalue */
LLVMValueRef llvm_build_ret(LLVMValueRef Val, value B) {
  return LLVMBuildRet(Builder_val(B), Val);
}

/* llvalue array -> llbuilder -> llvalue */
LLVMValueRef llvm_build_aggregate_ret(value RetVals, value B) {
  return LLVMBuildAggregateRet(Builder_val(B), (LLVMValueRef *)Op_val(RetVals),
                               Wosize_val(RetVals));
}

/* llbasicblock -> llbuilder -> llvalue */
LLVMValueRef llvm_build_br(LLVMBasicBlockRef BB, value B) {
  return LLVMBuildBr(Builder_val(B), BB);
}

/* llvalue -> llbasicblock -> llbasicblock -> llbuilder -> llvalue */
LLVMValueRef llvm_build_cond_br(LLVMValueRef If, LLVMBasicBlockRef Then,
                                LLVMBasicBlockRef Else, value B) {
  return LLVMBuildCondBr(Builder_val(B), If, Then, Else);
}

/* llvalue -> llbasicblock -> int -> llbuilder -> llvalue */
LLVMValueRef llvm_build_switch(LLVMValueRef Of, LLVMBasicBlockRef Else,
                               value EstimatedCount, value B) {
  return LLVMBuildSwitch(Builder_val(B), Of, Else, Int_val(EstimatedCount));
}

/* lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_malloc(LLVMTypeRef Ty, value Name, value B) {
  return LLVMBuildMalloc(Builder_val(B), Ty, String_val(Name));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_array_malloc(LLVMTypeRef Ty, LLVMValueRef Val,
                                     value Name, value B) {
  return LLVMBuildArrayMalloc(Builder_val(B), Ty, Val, String_val(Name));
}

/* llvalue -> llbuilder -> llvalue */
LLVMValueRef llvm_build_free(LLVMValueRef P, value B) {
  return LLVMBuildFree(Builder_val(B), P);
}

/* llvalue -> llvalue -> llbasicblock -> unit */
value llvm_add_case(LLVMValueRef Switch, LLVMValueRef OnVal,
                    LLVMBasicBlockRef Dest) {
  LLVMAddCase(Switch, OnVal, Dest);
  return Val_unit;
}

/* llvalue -> llbasicblock -> llbuilder -> llvalue */
LLVMValueRef llvm_build_indirect_br(LLVMValueRef Addr, value EstimatedDests,
                                    value B) {
  return LLVMBuildIndirectBr(Builder_val(B), Addr, EstimatedDests);
}

/* llvalue -> llvalue -> llbasicblock -> unit */
value llvm_add_destination(LLVMValueRef IndirectBr, LLVMBasicBlockRef Dest) {
  LLVMAddDestination(IndirectBr, Dest);
  return Val_unit;
}

/* llvalue -> llvalue array -> llbasicblock -> llbasicblock -> string ->
   llbuilder -> llvalue */
LLVMValueRef llvm_build_invoke_nat(LLVMValueRef Fn, value Args,
                                   LLVMBasicBlockRef Then,
                                   LLVMBasicBlockRef Catch, value Name,
                                   value B) {
  return LLVMBuildInvoke(Builder_val(B), Fn, (LLVMValueRef *)Op_val(Args),
                         Wosize_val(Args), Then, Catch, String_val(Name));
}

/* llvalue -> llvalue array -> llbasicblock -> llbasicblock -> string ->
   llbuilder -> llvalue */
LLVMValueRef llvm_build_invoke_bc(value Args[], int NumArgs) {
  return llvm_build_invoke_nat((LLVMValueRef)Args[0], Args[1],
                               (LLVMBasicBlockRef)Args[2],
                               (LLVMBasicBlockRef)Args[3], Args[4], Args[5]);
}

/* lltype -> llvalue -> llvalue array -> llbasicblock -> llbasicblock ->
   string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_invoke2_nat(LLVMTypeRef FnTy, LLVMValueRef Fn,
                                    value Args, LLVMBasicBlockRef Then,
                                    LLVMBasicBlockRef Catch, value Name,
                                    value B) {
  return LLVMBuildInvoke2(Builder_val(B), FnTy, Fn,
                          (LLVMValueRef *)Op_val(Args), Wosize_val(Args),
                          Then, Catch, String_val(Name));
}

/* lltype -> llvalue -> llvalue array -> llbasicblock -> llbasicblock ->
   string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_invoke2_bc(value Args[], int NumArgs) {
  return llvm_build_invoke2_nat((LLVMTypeRef)Args[0], (LLVMValueRef)Args[1],
                                Args[2], (LLVMBasicBlockRef)Args[3],
                               (LLVMBasicBlockRef)Args[4], Args[5], Args[6]);
}

/* lltype -> llvalue -> int -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_landingpad(LLVMTypeRef Ty, LLVMValueRef PersFn,
                                   value NumClauses, value Name, value B) {
  return LLVMBuildLandingPad(Builder_val(B), Ty, PersFn, Int_val(NumClauses),
                             String_val(Name));
}

/* llvalue -> llvalue -> unit */
value llvm_add_clause(LLVMValueRef LandingPadInst, LLVMValueRef ClauseVal) {
  LLVMAddClause(LandingPadInst, ClauseVal);
  return Val_unit;
}

/* llvalue -> bool */
value llvm_is_cleanup(LLVMValueRef LandingPadInst) {
  return Val_bool(LLVMIsCleanup(LandingPadInst));
}

/* llvalue -> bool -> unit */
value llvm_set_cleanup(LLVMValueRef LandingPadInst, value flag) {
  LLVMSetCleanup(LandingPadInst, Bool_val(flag));
  return Val_unit;
}

/* llvalue -> llbuilder -> llvalue */
LLVMValueRef llvm_build_resume(LLVMValueRef Exn, value B) {
  return LLVMBuildResume(Builder_val(B), Exn);
}

/* llbuilder -> llvalue */
LLVMValueRef llvm_build_unreachable(value B) {
  return LLVMBuildUnreachable(Builder_val(B));
}

/*--... Arithmetic .........................................................--*/

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_add(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildAdd(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nsw_add(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNSWAdd(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nuw_add(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNUWAdd(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fadd(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildFAdd(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_sub(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildSub(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nsw_sub(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNSWSub(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nuw_sub(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNUWSub(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fsub(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildFSub(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_mul(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildMul(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nsw_mul(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNSWMul(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nuw_mul(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildNUWMul(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fmul(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildFMul(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_udiv(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildUDiv(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_sdiv(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildSDiv(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_exact_sdiv(LLVMValueRef LHS, LLVMValueRef RHS,
                                   value Name, value B) {
  return LLVMBuildExactSDiv(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fdiv(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildFDiv(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_urem(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildURem(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_srem(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildSRem(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_frem(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildFRem(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_shl(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildShl(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_lshr(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildLShr(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_ashr(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                             value B) {
  return LLVMBuildAShr(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_and(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildAnd(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_or(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                           value B) {
  return LLVMBuildOr(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_xor(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                            value B) {
  return LLVMBuildXor(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_neg(LLVMValueRef X, value Name, value B) {
  return LLVMBuildNeg(Builder_val(B), X, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nsw_neg(LLVMValueRef X, value Name, value B) {
  return LLVMBuildNSWNeg(Builder_val(B), X, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_nuw_neg(LLVMValueRef X, value Name, value B) {
  return LLVMBuildNUWNeg(Builder_val(B), X, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fneg(LLVMValueRef X, value Name, value B) {
  return LLVMBuildFNeg(Builder_val(B), X, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_not(LLVMValueRef X, value Name, value B) {
  return LLVMBuildNot(Builder_val(B), X, String_val(Name));
}

/*--... Memory .............................................................--*/

/* lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_alloca(LLVMTypeRef Ty, value Name, value B) {
  return LLVMBuildAlloca(Builder_val(B), Ty, String_val(Name));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_array_alloca(LLVMTypeRef Ty, LLVMValueRef Size,
                                     value Name, value B) {
  return LLVMBuildArrayAlloca(Builder_val(B), Ty, Size, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_load(LLVMValueRef Pointer, value Name, value B) {
  return LLVMBuildLoad(Builder_val(B), Pointer, String_val(Name));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_load2(LLVMTypeRef Ty, LLVMValueRef Pointer, value Name,
                              value B) {
  return LLVMBuildLoad2(Builder_val(B), Ty, Pointer, String_val(Name));
}

/* llvalue -> llvalue -> llbuilder -> llvalue */
LLVMValueRef llvm_build_store(LLVMValueRef Value, LLVMValueRef Pointer,
                              value B) {
  return LLVMBuildStore(Builder_val(B), Value, Pointer);
}

/* AtomicRMWBinOp.t -> llvalue -> llvalue -> AtomicOrdering.t ->
   bool -> llbuilder -> llvalue */
LLVMValueRef llvm_build_atomicrmw_native(value BinOp, LLVMValueRef Ptr,
                                         LLVMValueRef Val, value Ord, value ST,
                                         value Name, value B) {
  LLVMValueRef Instr;
  Instr = LLVMBuildAtomicRMW(Builder_val(B), Int_val(BinOp), Ptr, Val,
                             Int_val(Ord), Bool_val(ST));
  LLVMSetValueName(Instr, String_val(Name));
  return Instr;
}

LLVMValueRef llvm_build_atomicrmw_bytecode(value *argv, int argn) {
  return llvm_build_atomicrmw_native(argv[0], (LLVMValueRef)argv[1],
                                     (LLVMValueRef)argv[2], argv[3], argv[4],
                                     argv[5], argv[6]);
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_gep(LLVMValueRef Pointer, value Indices, value Name,
                            value B) {
  return LLVMBuildGEP(Builder_val(B), Pointer, (LLVMValueRef *)Op_val(Indices),
                      Wosize_val(Indices), String_val(Name));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_gep2(LLVMTypeRef Ty, LLVMValueRef Pointer,
                             value Indices, value Name, value B) {
  return LLVMBuildGEP2(Builder_val(B), Ty, Pointer,
                       (LLVMValueRef *)Op_val(Indices), Wosize_val(Indices),
                       String_val(Name));
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_in_bounds_gep(LLVMValueRef Pointer, value Indices,
                                      value Name, value B) {
  return LLVMBuildInBoundsGEP(Builder_val(B), Pointer,
                              (LLVMValueRef *)Op_val(Indices),
                              Wosize_val(Indices), String_val(Name));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_in_bounds_gep2(LLVMTypeRef Ty, LLVMValueRef Pointer,
                                       value Indices, value Name, value B) {
  return LLVMBuildInBoundsGEP2(Builder_val(B), Ty, Pointer,
                               (LLVMValueRef *)Op_val(Indices),
                               Wosize_val(Indices), String_val(Name));
}

/* llvalue -> int -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_struct_gep(LLVMValueRef Pointer, value Index,
                                   value Name, value B) {
  return LLVMBuildStructGEP(Builder_val(B), Pointer, Int_val(Index),
                            String_val(Name));
}

/* lltype -> llvalue -> int -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_struct_gep2(LLVMTypeRef Ty, LLVMValueRef Pointer,
                                    value Index, value Name, value B) {
  return LLVMBuildStructGEP2(Builder_val(B), Ty, Pointer, Int_val(Index),
                             String_val(Name));
}

/* string -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_global_string(value Str, value Name, value B) {
  return LLVMBuildGlobalString(Builder_val(B), String_val(Str),
                               String_val(Name));
}

/* string -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_global_stringptr(value Str, value Name, value B) {
  return LLVMBuildGlobalStringPtr(Builder_val(B), String_val(Str),
                                  String_val(Name));
}

/*--... Casts ..............................................................--*/

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_trunc(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                              value B) {
  return LLVMBuildTrunc(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_zext(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                             value B) {
  return LLVMBuildZExt(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_sext(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                             value B) {
  return LLVMBuildSExt(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fptoui(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildFPToUI(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fptosi(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildFPToSI(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_uitofp(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildUIToFP(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_sitofp(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildSIToFP(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fptrunc(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                value B) {
  return LLVMBuildFPTrunc(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fpext(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                              value B) {
  return LLVMBuildFPExt(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_prttoint(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                 value B) {
  return LLVMBuildPtrToInt(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_inttoptr(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                 value B) {
  return LLVMBuildIntToPtr(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_bitcast(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                value B) {
  return LLVMBuildBitCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_zext_or_bitcast(LLVMValueRef X, LLVMTypeRef Ty,
                                        value Name, value B) {
  return LLVMBuildZExtOrBitCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_sext_or_bitcast(LLVMValueRef X, LLVMTypeRef Ty,
                                        value Name, value B) {
  return LLVMBuildSExtOrBitCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_trunc_or_bitcast(LLVMValueRef X, LLVMTypeRef Ty,
                                         value Name, value B) {
  return LLVMBuildTruncOrBitCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_pointercast(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                    value B) {
  return LLVMBuildPointerCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_intcast(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                                value B) {
  return LLVMBuildIntCast(Builder_val(B), X, Ty, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fpcast(LLVMValueRef X, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildFPCast(Builder_val(B), X, Ty, String_val(Name));
}

/*--... Comparisons ........................................................--*/

/* Icmp.t -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_icmp(value Pred, LLVMValueRef LHS, LLVMValueRef RHS,
                             value Name, value B) {
  return LLVMBuildICmp(Builder_val(B), Int_val(Pred) + LLVMIntEQ, LHS, RHS,
                       String_val(Name));
}

/* Fcmp.t -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_fcmp(value Pred, LLVMValueRef LHS, LLVMValueRef RHS,
                             value Name, value B) {
  return LLVMBuildFCmp(Builder_val(B), Int_val(Pred), LHS, RHS,
                       String_val(Name));
}

/*--... Miscellaneous instructions .........................................--*/

/* (llvalue * llbasicblock) list -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_phi(value Incoming, value Name, value B) {
  value Hd, Tl;
  LLVMValueRef FirstValue, PhiNode;

  assert(Incoming != Val_int(0) && "Empty list passed to Llvm.build_phi!");

  Hd = Field(Incoming, 0);
  FirstValue = (LLVMValueRef)Field(Hd, 0);
  PhiNode =
      LLVMBuildPhi(Builder_val(B), LLVMTypeOf(FirstValue), String_val(Name));

  for (Tl = Incoming; Tl != Val_int(0); Tl = Field(Tl, 1)) {
    value Hd = Field(Tl, 0);
    LLVMAddIncoming(PhiNode, (LLVMValueRef *)&Field(Hd, 0),
                    (LLVMBasicBlockRef *)&Field(Hd, 1), 1);
  }

  return PhiNode;
}

/* lltype -> string -> llbuilder -> value */
LLVMValueRef llvm_build_empty_phi(LLVMTypeRef Type, value Name, value B) {
  return LLVMBuildPhi(Builder_val(B), Type, String_val(Name));
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_call(LLVMValueRef Fn, value Params, value Name,
                             value B) {
  return LLVMBuildCall(Builder_val(B), Fn, (LLVMValueRef *)Op_val(Params),
                       Wosize_val(Params), String_val(Name));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_call2(LLVMTypeRef FnTy, LLVMValueRef Fn, value Params,
                              value Name, value B) {
  return LLVMBuildCall2(Builder_val(B), FnTy, Fn,
                        (LLVMValueRef *)Op_val(Params), Wosize_val(Params),
                        String_val(Name));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_select(LLVMValueRef If, LLVMValueRef Then,
                               LLVMValueRef Else, value Name, value B) {
  return LLVMBuildSelect(Builder_val(B), If, Then, Else, String_val(Name));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_va_arg(LLVMValueRef List, LLVMTypeRef Ty, value Name,
                               value B) {
  return LLVMBuildVAArg(Builder_val(B), List, Ty, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_extractelement(LLVMValueRef Vec, LLVMValueRef Idx,
                                       value Name, value B) {
  return LLVMBuildExtractElement(Builder_val(B), Vec, Idx, String_val(Name));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_insertelement(LLVMValueRef Vec, LLVMValueRef Element,
                                      LLVMValueRef Idx, value Name, value B) {
  return LLVMBuildInsertElement(Builder_val(B), Vec, Element, Idx,
                                String_val(Name));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_shufflevector(LLVMValueRef V1, LLVMValueRef V2,
                                      LLVMValueRef Mask, value Name, value B) {
  return LLVMBuildShuffleVector(Builder_val(B), V1, V2, Mask, String_val(Name));
}

/* llvalue -> int -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_extractvalue(LLVMValueRef Aggregate, value Idx,
                                     value Name, value B) {
  return LLVMBuildExtractValue(Builder_val(B), Aggregate, Int_val(Idx),
                               String_val(Name));
}

/* llvalue -> llvalue -> int -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_insertvalue(LLVMValueRef Aggregate, LLVMValueRef Val,
                                    value Idx, value Name, value B) {
  return LLVMBuildInsertValue(Builder_val(B), Aggregate, Val, Int_val(Idx),
                              String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_is_null(LLVMValueRef Val, value Name, value B) {
  return LLVMBuildIsNull(Builder_val(B), Val, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_is_not_null(LLVMValueRef Val, value Name, value B) {
  return LLVMBuildIsNotNull(Builder_val(B), Val, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_ptrdiff(LLVMValueRef LHS, LLVMValueRef RHS, value Name,
                                value B) {
  return LLVMBuildPtrDiff(Builder_val(B), LHS, RHS, String_val(Name));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_ptrdiff2(LLVMTypeRef ElemTy, LLVMValueRef LHS,
                                 LLVMValueRef RHS, value Name, value B) {
  return LLVMBuildPtrDiff2(Builder_val(B), ElemTy, LHS, RHS, String_val(Name));
}

/* llvalue -> string -> llbuilder -> llvalue */
LLVMValueRef llvm_build_freeze(LLVMValueRef X, value Name, value B) {
  return LLVMBuildFreeze(Builder_val(B), X, String_val(Name));
}

/*===-- Memory buffers ----------------------------------------------------===*/

/* string -> llmemorybuffer
   raises IoError msg on error */
LLVMMemoryBufferRef llvm_memorybuffer_of_file(value Path) {
  char *Message;
  LLVMMemoryBufferRef MemBuf;

  if (LLVMCreateMemoryBufferWithContentsOfFile(String_val(Path), &MemBuf,
                                               &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);

  return MemBuf;
}

/* unit -> llmemorybuffer
   raises IoError msg on error */
LLVMMemoryBufferRef llvm_memorybuffer_of_stdin(value Unit) {
  char *Message;
  LLVMMemoryBufferRef MemBuf;

  if (LLVMCreateMemoryBufferWithSTDIN(&MemBuf, &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);

  return MemBuf;
}

/* ?name:string -> string -> llmemorybuffer */
LLVMMemoryBufferRef llvm_memorybuffer_of_string(value Name, value String) {
  LLVMMemoryBufferRef MemBuf;
  const char *NameCStr;

  if (Name == Val_int(0))
    NameCStr = "";
  else
    NameCStr = String_val(Field(Name, 0));

  MemBuf = LLVMCreateMemoryBufferWithMemoryRangeCopy(
      String_val(String), caml_string_length(String), NameCStr);

  return MemBuf;
}

/* llmemorybuffer -> string */
value llvm_memorybuffer_as_string(LLVMMemoryBufferRef MemBuf) {
  size_t BufferSize = LLVMGetBufferSize(MemBuf);
  const char *BufferStart = LLVMGetBufferStart(MemBuf);
  return cstr_to_string(BufferStart, BufferSize);
}

/* llmemorybuffer -> unit */
value llvm_memorybuffer_dispose(LLVMMemoryBufferRef MemBuf) {
  LLVMDisposeMemoryBuffer(MemBuf);
  return Val_unit;
}

/*===-- Pass Managers -----------------------------------------------------===*/

/* unit -> [ `Module ] PassManager.t */
LLVMPassManagerRef llvm_passmanager_create(value Unit) {
  return LLVMCreatePassManager();
}

/* llmodule -> [ `Function ] PassManager.t -> bool */
value llvm_passmanager_run_module(LLVMModuleRef M, LLVMPassManagerRef PM) {
  return Val_bool(LLVMRunPassManager(PM, M));
}

/* [ `Function ] PassManager.t -> bool */
value llvm_passmanager_initialize(LLVMPassManagerRef FPM) {
  return Val_bool(LLVMInitializeFunctionPassManager(FPM));
}

/* llvalue -> [ `Function ] PassManager.t -> bool */
value llvm_passmanager_run_function(LLVMValueRef F, LLVMPassManagerRef FPM) {
  return Val_bool(LLVMRunFunctionPassManager(FPM, F));
}

/* [ `Function ] PassManager.t -> bool */
value llvm_passmanager_finalize(LLVMPassManagerRef FPM) {
  return Val_bool(LLVMFinalizeFunctionPassManager(FPM));
}

/* PassManager.any PassManager.t -> unit */
value llvm_passmanager_dispose(LLVMPassManagerRef PM) {
  LLVMDisposePassManager(PM);
  return Val_unit;
}
