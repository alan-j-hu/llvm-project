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

static value alloc_basic_block(LLVMBasicBlockRef B) {
  value V = caml_alloc(1, Abstract_tag);
  BasicBlock_val(V) = B;
  return V;
}

static value alloc_value(LLVMValueRef Val) {
  value V = caml_alloc(1, Abstract_tag);
  Value_val(V) = Val;
  return V;
}

static value alloc_variant(int tag, value Value) {
  value Iter = caml_alloc_small(1, tag);
  Field(Iter, 0) = Value;
  return Iter;
}

/* Macro to convert the C first/next/last/prev idiom to the Ocaml llpos/
   llrev_pos idiom. */
#define DEFINE_ITERATORS(camlname, cname, pty_val, cty, cty_val, pfun) \
  /* llmodule -> ('a, 'b) llpos */                                     \
  value llvm_##camlname##_begin(value Mom) {                           \
    CAMLparam1(Mom);                                                   \
    CAMLlocal1(Box);                                                   \
    Box = caml_alloc(1, Abstract_tag);                                 \
    cty First = LLVMGetFirst##cname(pty_val(Mom));                     \
    if (First) {                                                       \
      cty_val(Box) = First;                                            \
      CAMLreturn(alloc_variant(1, Box));                               \
    }                                                                  \
    CAMLreturn(alloc_variant(0, Mom));                                 \
  }                                                                    \
                                                                       \
  /* llvalue -> ('a, 'b) llpos */                                      \
  value llvm_##camlname##_succ(value Kid) {                            \
    CAMLparam1(Kid);                                                   \
    CAMLlocal1(Box);                                                   \
    Box = caml_alloc(1, Abstract_tag);                                 \
    cty Next = LLVMGetNext##cname(cty_val(Kid));                       \
    if (Next) {                                                        \
      cty_val(Box) = Next;                                             \
      CAMLreturn(alloc_variant(1, Box));                               \
    }                                                                  \
    pty_val(Box) = pfun(cty_val(Kid));                                          \
    CAMLreturn(alloc_variant(0, Box));                                 \
  }                                                                    \
                                                                       \
  /* llmodule -> ('a, 'b) llrev_pos */                                 \
  value llvm_##camlname##_end(value Mom) {                             \
    CAMLparam1(Mom);                                                   \
    CAMLlocal1(Box);                                                   \
    Box = caml_alloc(1, Abstract_tag);                                 \
    cty Last = LLVMGetLast##cname(pty_val(Mom));                       \
    if (Last) {                                                        \
      cty_val(Box) = Last;                                             \
      CAMLreturn(alloc_variant(1, Box));                               \
    }                                                                  \
    CAMLreturn(alloc_variant(0, Mom));                                 \
  }                                                                    \
                                                                       \
  /* llvalue -> ('a, 'b) llrev_pos */                                  \
  value llvm_##camlname##_pred(value Kid) {                              \
    CAMLparam1(Kid);                                                   \
    CAMLlocal1(Box);                                                   \
    Box = caml_alloc(1, Abstract_tag);                                 \
    cty Prev = LLVMGetPrevious##cname(cty_val(Kid));                   \
    if (Prev) {                                                        \
      cty_val(Box) = Prev;                                             \
      CAMLreturn(alloc_variant(1, Box));                              \
    }                                                                  \
    pty_val(Box) = pfun(cty_val(Kid));                                          \
    CAMLreturn(alloc_variant(0, Box));                                 \
  }

/*===-- Context error handling --------------------------------------------===*/

void llvm_diagnostic_handler_trampoline(LLVMDiagnosticInfoRef DI,
                                        void *DiagnosticContext) {
  value Box = caml_alloc(1, Abstract_tag);
  DiagnosticInfo_val(Box) = DI;
  caml_callback(*((value *)DiagnosticContext), Box);
}

/* Diagnostic.t -> string */
value llvm_get_diagnostic_description(value Diagnostic) {
  return llvm_string_of_message(
      LLVMGetDiagInfoDescription(DiagnosticInfo_val(Diagnostic)));
}

/* Diagnostic.t -> DiagnosticSeverity.t */
value llvm_get_diagnostic_severity(value Diagnostic) {
  return Val_int(LLVMGetDiagInfoSeverity(DiagnosticInfo_val(Diagnostic)));
}

static void llvm_remove_diagnostic_handler(value C) {
  CAMLparam1(C);
  LLVMContextRef context = Context_val(C);
  if (LLVMContextGetDiagnosticHandler(context) ==
      llvm_diagnostic_handler_trampoline) {
    value *Handler = (value *)LLVMContextGetDiagnosticContext(context);
    caml_remove_global_root(Handler);
    free(Handler);
  }
  CAMLreturn0;
}

/* llcontext -> (Diagnostic.t -> unit) option -> unit */
value llvm_set_diagnostic_handler(value C, value Handler) {
  CAMLparam2(C, Handler);
  LLVMContextRef context = Context_val(C);
  llvm_remove_diagnostic_handler(C);
  if (Handler == Val_none) {
    LLVMContextSetDiagnosticHandler(context, NULL, NULL);
  } else {
    value *DiagnosticContext = malloc(sizeof(value));
    if (DiagnosticContext == NULL)
      caml_raise_out_of_memory();
    caml_register_global_root(DiagnosticContext);
    *DiagnosticContext = Field(Handler, 0);
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
  Context_val(context_val) = LLVMContextCreate();
  CAMLreturn(context_val);
}

/* llcontext -> unit */
value llvm_dispose_context(value C) {
  CAMLparam1(C);
  llvm_remove_diagnostic_handler(C);
  LLVMContextDispose(Context_val(C));
  CAMLreturn(Val_unit);
}

/* unit -> llcontext */
value llvm_global_context(value Unit) {
  CAMLparam1(Unit);
  CAMLlocal1(context_val);
  context_val = caml_alloc(1, Abstract_tag);
  Context_val(context_val) = LLVMGetGlobalContext();
  CAMLreturn(context_val);
}

/* llcontext -> string -> int */
value llvm_mdkind_id(value C, value Name) {
  CAMLparam2(C, Name);
  unsigned MDKindID =
      LLVMGetMDKindIDInContext(Context_val(C), String_val(Name),
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
  Attribute_val(Ret) =
    LLVMCreateEnumAttribute(Context_val(C), Int_val(Kind), Int64_val(Value));
  CAMLreturn(Ret);
}

/* llattribute -> bool */
value llvm_is_enum_attr(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMIsEnumAttribute(Attribute_val(A))));
}

/* llattribute -> llattrkind */
value llvm_get_enum_attr_kind(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMGetEnumAttributeKind(Attribute_val(A))));
}

/* llattribute -> int64 */
value llvm_get_enum_attr_value(value A) {
  CAMLparam1(A);
  CAMLreturn(caml_copy_int64(LLVMGetEnumAttributeValue(Attribute_val(A))));
}

/* llcontext -> kind:string -> name:string -> llattribute */
value llvm_create_string_attr(value C, value Kind, value Value) {
  CAMLparam3(C, Kind, Value);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Attribute_val(Ret) = LLVMCreateStringAttribute(
    Context_val(C), String_val(Kind), caml_string_length(Kind),
    String_val(Value), caml_string_length(Value));
  CAMLreturn(Ret);
}

/* llattribute -> bool */
value llvm_is_string_attr(value A) {
  CAMLparam1(A);
  CAMLreturn(Val_int(LLVMIsStringAttribute(Attribute_val(A))));
}

/* llattribute -> string */
value llvm_get_string_attr_kind(value A) {
  CAMLparam1(A);
  unsigned Length;
  const char *String = LLVMGetStringAttributeKind(Attribute_val(A), &Length);
  CAMLreturn(cstr_to_string(String, Length));
}

/* llattribute -> string */
value llvm_get_string_attr_value(value A) {
  CAMLparam1(A);
  unsigned Length;
  const char *String = LLVMGetStringAttributeValue(Attribute_val(A), &Length);
  CAMLreturn(cstr_to_string(String, Length));
}

/*===-- Modules -----------------------------------------------------------===*/

/* llcontext -> string -> llmodule */
value llvm_create_module(value C, value ModuleID) {
  CAMLparam2(C, ModuleID);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Module_val(Ret) =
    LLVMModuleCreateWithNameInContext(String_val(ModuleID), Context_val(C));
  CAMLreturn(Ret);
}

/* llmodule -> unit */
value llvm_dispose_module(value M) {
  CAMLparam1(M);
  LLVMDisposeModule(Module_val(M));
  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_target_triple(value M) {
  CAMLparam1(M);
  CAMLreturn(caml_copy_string(LLVMGetTarget(Module_val(M))));
}

/* string -> llmodule -> unit */
value llvm_set_target_triple(value Trip, value M) {
  CAMLparam2(Trip, M);
  LLVMSetTarget(Module_val(M), String_val(Trip));
  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_data_layout(value M) {
  CAMLparam1(M);
  CAMLreturn(caml_copy_string(LLVMGetDataLayout(Module_val(M))));
}

/* string -> llmodule -> unit */
value llvm_set_data_layout(value Layout, value M) {
  CAMLparam2(Layout, M);
  LLVMSetDataLayout(Module_val(M), String_val(Layout));
  CAMLreturn(Val_unit);
}

/* llmodule -> unit */
value llvm_dump_module(value M) {
  CAMLparam1(M);
  LLVMDumpModule(Module_val(M));
  CAMLreturn(Val_unit);
}

/* string -> llmodule -> unit */
value llvm_print_module(value Filename, value M) {
  CAMLparam2(Filename, M);
  char *Message;

  if (LLVMPrintModuleToFile(Module_val(M), String_val(Filename), &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);

  CAMLreturn(Val_unit);
}

/* llmodule -> string */
value llvm_string_of_llmodule(value M) {
  CAMLparam1(M);
  char *ModuleCStr = LLVMPrintModuleToString(Module_val(M));
  value ModuleStr = caml_copy_string(ModuleCStr);
  LLVMDisposeMessage(ModuleCStr);

  CAMLreturn(ModuleStr);
}

/* llmodule -> string */
value llvm_get_module_identifier(value M) {
  CAMLparam1(M);
  size_t Len;
  const char *Name = LLVMGetModuleIdentifier(Module_val(M), &Len);
  CAMLreturn(cstr_to_string(Name, (mlsize_t)Len));
}

/* llmodule -> string -> unit */
value llvm_set_module_identifier(value M, value Id) {
  CAMLparam2(M, Id);
  LLVMSetModuleIdentifier(Module_val(M), String_val(Id),
                          caml_string_length(Id));
  CAMLreturn(Val_unit);
}

/* llmodule -> string -> unit */
value llvm_set_module_inline_asm(value M, value Asm) {
  CAMLparam2(M, Asm);
  LLVMSetModuleInlineAsm(Module_val(M), String_val(Asm));
  CAMLreturn(Val_unit);
}

/* llmodule -> string -> llmetadata option */
value llvm_get_module_flag(value M, value Key) {
  CAMLparam2(M, Key);
  CAMLreturn(ptr_to_option(
      LLVMGetModuleFlag(Module_val(M), String_val(Key),
                        caml_string_length(Key))));
}

/* llmodule -> ModuleFlagBehavior.t -> string -> llmetadata -> unit */
value llvm_add_module_flag(value M, value Behaviour, value Key, value Val) {
  CAMLparam4(M, Behaviour, Key, Val);
  LLVMAddModuleFlag(Module_val(M), Int_val(Behaviour), String_val(Key),
                    caml_string_length(Key), Metadata_val(Val));
  CAMLreturn(Val_unit);
}

/*===-- Types -------------------------------------------------------------===*/

/* lltype -> TypeKind.t */
value llvm_classify_type(value Ty) {
  CAMLparam1(Ty);
  CAMLreturn(Val_int(LLVMGetTypeKind(Type_val(Ty))));
}

value llvm_type_is_sized(value Ty) {
  CAMLparam1(Ty);
  CAMLreturn(Val_bool(LLVMTypeIsSized(Type_val(Ty))));
}

/* lltype -> llcontext */
value llvm_type_context(value Ty) {
  CAMLparam1(Ty);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Context_val(Ret) = LLVMGetTypeContext(Type_val(Ty));
  CAMLreturn(Ret);
}

/* lltype -> unit */
value llvm_dump_type(value Val) {
  CAMLparam1(Val);
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
  LLVMDumpType(Type_val(Val));
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
  char *TypeCStr = LLVMPrintTypeToString(Type_val(M));
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
  Type_val(Ret) = LLVMInt1TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i8_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMInt8TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i16_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMInt16TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i32_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMInt32TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_i64_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMInt64TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> int -> lltype */
value llvm_integer_type(value Context, value Width) {
  CAMLparam2(Context, Width);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMIntTypeInContext(Context_val(Context), Int_val(Width));
  CAMLreturn(Ret);
}

/* lltype -> int */
value llvm_integer_bitwidth(value IntegerTy) {
  CAMLparam1(IntegerTy);
  CAMLreturn(Val_int(LLVMGetIntTypeWidth(Type_val(IntegerTy))));
}

/*--... Operations on real types ...........................................--*/

/* llcontext -> lltype */
value llvm_float_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMFloatTypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_double_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMDoubleTypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_x86fp80_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMX86FP80TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_fp128_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMFP128TypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_ppc_fp128_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMPPCFP128TypeInContext(Context_val(Context));
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
    Field(Temp, i) = (value)Type_val(Field(ParamTys, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMFunctionType(Type_val(RetTy), (LLVMTypeRef*)Temp, len, 0);
  CAMLreturn(Ret);
}

/* lltype -> lltype array -> lltype */
value llvm_var_arg_function_type(value RetTy, value ParamTys) {
  CAMLparam2(RetTy, ParamTys);
  CAMLlocal2(Temp, Ret);
  size_t len = Wosize_val(ParamTys);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = (value)Type_val(Field(ParamTys, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMFunctionType(Type_val(RetTy), (LLVMTypeRef*)Temp, len, 1);
  CAMLreturn(Ret);
}

/* lltype -> bool */
value llvm_is_var_arg(value FunTy) {
  CAMLparam1(FunTy);
  CAMLreturn(Val_bool(LLVMIsFunctionVarArg(Type_val(FunTy))));
}

/* lltype -> lltype array */
value llvm_param_types(value FunTy) {
  CAMLparam1(FunTy);
  CAMLlocal2(Temp, Tys);
  unsigned len = LLVMCountParamTypes(Type_val(FunTy));
  Temp = caml_alloc(len, Abstract_tag);
  LLVMGetParamTypes(Type_val(FunTy), (LLVMTypeRef*)Temp);
  Tys = caml_alloc_tuple_uninit(len);
  for (size_t i = 0; i < len; ++i) {
    Type_val(Field(Tys, i)) = (LLVMTypeRef) Field(Temp, i);
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
    Field(Temp, i) = (value)Type_val(Field(ElementTypes, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMStructTypeInContext(Context_val(C), (LLVMTypeRef*)Temp, len, 0);
  CAMLreturn(Ret);
}

/* llcontext -> lltype array -> lltype */
value llvm_packed_struct_type(value C, value ElementTypes) {
  CAMLparam2(C, ElementTypes);
  CAMLlocal2(Temp, Ret);
  size_t len = Wosize_val(ElementTypes);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = (value)Type_val(Field(ElementTypes, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMStructTypeInContext(Context_val(C), (LLVMTypeRef*)Temp, len, 1);
  CAMLreturn(Ret);
}

/* llcontext -> string -> lltype */
value llvm_named_struct_type(value C, value Name) {
  CAMLparam2(C, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMStructCreateNamed(Context_val(C), String_val(Name));
  CAMLreturn(Ret);
}

/* lltype -> lltype array -> bool -> unit */
value llvm_struct_set_body(value Ty, value ElementTypes, value Packed) {
  CAMLparam3(Ty, ElementTypes, Packed);
  CAMLlocal1(Temp);
  size_t len = Wosize_val(ElementTypes);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned int i = 0; i < len; ++i) {
    Field(Temp, i) = (value)Type_val(Field(ElementTypes, i));
  }
  LLVMStructSetBody(Type_val(Ty), (LLVMTypeRef*)Temp, len,
                    Bool_val(Packed));
  CAMLreturn(Val_unit);
}

/* lltype -> string option */
value llvm_struct_name(value Ty) {
  CAMLparam1(Ty);
  const char *CStr = LLVMGetStructName(Type_val(Ty));
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
  unsigned count = LLVMCountStructElementTypes(Type_val(StructTy));
  Tys = caml_alloc_tuple_uninit(count);
  Temp = caml_alloc(count, Abstract_tag);
  LLVMGetStructElementTypes(Type_val(StructTy), (LLVMTypeRef*)Temp);
  for (unsigned i = 0; i < count; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Type_val(Box) = (LLVMTypeRef)Field(Temp, i);
    Store_field(Tys, i, Box);
  }
  CAMLreturn(Tys);
}

/* lltype -> bool */
value llvm_is_packed(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsPackedStruct(Type_val(StructTy))));
}

/* lltype -> bool */
value llvm_is_opaque(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsOpaqueStruct(Type_val(StructTy))));
}

/* lltype -> bool */
value llvm_is_literal(value StructTy) {
  CAMLparam1(StructTy);
  CAMLreturn(Val_bool(LLVMIsLiteralStruct(Type_val(StructTy))));
}

/*--... Operations on array, pointer, and vector types .....................--*/

/* lltype -> lltype array */
value llvm_subtypes(value Ty) {
  CAMLparam1(Ty);
  CAMLlocal2(Temp, Arr);
  unsigned Size = LLVMGetNumContainedTypes(Type_val(Ty));
  Arr = caml_alloc_tuple_uninit(Size);
  Temp = caml_alloc(Size, Abstract_tag);
  LLVMGetSubtypes(Type_val(Ty), (LLVMTypeRef*)Temp);
  for (unsigned int i = 0; i < Size; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Type_val(Box) = (LLVMTypeRef)Field(Temp, i);
    Field(Arr, i) = Box;
  }
  CAMLreturn(Arr);
}

/* lltype -> int -> lltype */
value llvm_array_type(value ElementTy, value Count) {
  CAMLparam2(ElementTy, Count);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMArrayType(Type_val(ElementTy), Int_val(Count));
  CAMLreturn(Ret);
}

/* lltype -> lltype */
value llvm_pointer_type(value ElementTy) {
  CAMLparam1(ElementTy);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMPointerType(Type_val(ElementTy), 0);
  CAMLreturn(Ret);
}

/* lltype -> int -> lltype */
value llvm_qualified_pointer_type(value ElementTy, value AddressSpace) {
  CAMLparam2(ElementTy, AddressSpace);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMPointerType(Type_val(ElementTy), Int_val(AddressSpace));
  CAMLreturn(Ret);
}

/* llcontext -> int -> lltype */
value llvm_pointer_type_in_context(value C, value AddressSpace) {
  CAMLparam2(C, AddressSpace);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) =
    LLVMPointerTypeInContext(Context_val(C), Int_val(AddressSpace));
  CAMLreturn(Ret);
}

/* lltype -> int -> lltype */
value llvm_vector_type(value ElementTy, value Count) {
  CAMLparam2(ElementTy, Count);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMVectorType(Type_val(ElementTy), Int_val(Count));
  CAMLreturn(Ret);
}

/* lltype -> int */
value llvm_array_length(value ArrayTy) {
  CAMLparam1(ArrayTy);
  CAMLreturn(Val_int(LLVMGetArrayLength(Type_val(ArrayTy))));
}

/* lltype -> int */
value llvm_address_space(value PtrTy) {
  CAMLparam1(PtrTy);
  CAMLreturn(Val_int(LLVMGetPointerAddressSpace(Type_val(PtrTy))));
}

/* lltype -> int */
value llvm_vector_size(value VectorTy) {
  CAMLparam1(VectorTy);
  CAMLreturn(Val_int(LLVMGetVectorSize(Type_val(VectorTy))));
}

/*--... Operations on other types ..........................................--*/

/* llcontext -> lltype */
value llvm_void_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMVoidTypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_label_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMLabelTypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llcontext -> lltype */
value llvm_x86_mmx_type(value Context) {
  CAMLparam1(Context);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Type_val(Ret) = LLVMX86MMXTypeInContext(Context_val(Context));
  CAMLreturn(Ret);
}

/* llmodule -> string -> lltype option */
value llvm_type_by_name(value M, value Name) {
  CAMLparam2(M, Name);
  CAMLreturn(
    ptr_to_option(LLVMGetTypeByName(Module_val(M), String_val(Name))));
}

/*===-- VALUES ------------------------------------------------------------===*/

/* llvalue -> lltype */
value llvm_type_of(value Val) {
  CAMLparam1(Val);
  CAMLlocal1(V);
  V = caml_alloc(1, Abstract_tag);
  Type_val(V) = LLVMTypeOf(Value_val(Val));
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
  LLVMValueRef Val = Value_val(V);
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
  caml_failwith("Unknown Value class");
}

/* llvalue -> string */
value llvm_value_name(value Val) {
  CAMLparam1(Val);
  CAMLreturn(caml_copy_string(LLVMGetValueName(Value_val(Val))));
}

/* string -> llvalue -> unit */
value llvm_set_value_name(value Name, value Val) {
  CAMLparam2(Name, Val);
  LLVMSetValueName(Value_val(Val), String_val(Name));
  CAMLreturn(Val_unit);
}

/* llvalue -> unit */
value llvm_dump_value(value Val) {
  CAMLparam1(Val);
  LLVMDumpValue(Value_val(Val));
  CAMLreturn(Val_unit);
}

/* llvalue -> string */
value llvm_string_of_llvalue(value M) {
  CAMLparam1(M);
  CAMLlocal1(ValueStr);
  char *ValueCStr = LLVMPrintValueToString(Value_val(M));
  ValueStr = caml_copy_string(ValueCStr);
  LLVMDisposeMessage(ValueCStr);

  CAMLreturn(ValueStr);
}

/* llvalue -> llvalue -> unit */
value llvm_replace_all_uses_with(value OldVal, value NewVal) {
  CAMLparam2(OldVal, NewVal);
  LLVMReplaceAllUsesWith(Value_val(OldVal), Value_val(NewVal));
  CAMLreturn(Val_unit);
}

/*--... Operations on users ................................................--*/

/* llvalue -> int -> llvalue */
value llvm_operand(value V, value I) {
  CAMLparam2(V, I);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMGetOperand(Value_val(V), Int_val(I));
  CAMLreturn(Ret);
}

/* llvalue -> int -> lluse */
value llvm_operand_use(value V, value I) {
  CAMLparam2(V, I);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Use_val(Ret) = LLVMGetOperandUse(Value_val(V), Int_val(I));
  CAMLreturn(Ret);
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_operand(value U, value I, value V) {
  CAMLparam3(U, I, V);
  LLVMSetOperand(Value_val(U), Int_val(I), Value_val(V));
  CAMLreturn(Val_unit);
}

/* llvalue -> int */
value llvm_num_operands(value V) {
  CAMLparam1(V);
  CAMLreturn(Val_int(LLVMGetNumOperands(Value_val(V))));
}

/* llvalue -> int array */
value llvm_indices(value Instr) {
  CAMLparam1(Instr);
  CAMLlocal1(indices);
  unsigned n = LLVMGetNumIndices(Value_val(Instr));
  const unsigned *Indices = LLVMGetIndices(Value_val(Instr));
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
  CAMLreturn(Val_bool(LLVMIsConstant(Value_val(Val))));
}

/* llvalue -> bool */
value llvm_is_null(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsNull(Value_val(Val))));
}

/* llvalue -> bool */
value llvm_is_undef(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsUndef(Value_val(Val))));
}

/* llvalue -> bool */
value llvm_is_poison(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMIsPoison(Value_val(Val))));
}

/* llvalue -> Opcode.t */
value llvm_constexpr_get_opcode(value Val) {
  CAMLparam1(Val);
  CAMLreturn(LLVMIsAConstantExpr(Value_val(Val))
    ? Val_int(LLVMGetConstOpcode(Value_val(Val)))
    : Val_int(0));
}

/*--... Operations on instructions .........................................--*/

/* llvalue -> bool */
value llvm_has_metadata(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMHasMetadata(Value_val(Val))));
}

/* llvalue -> int -> llvalue option */
value llvm_metadata(value Val, value MDKindID) {
  CAMLparam2(Val, MDKindID);
  CAMLreturn(
    ptr_to_option(LLVMGetMetadata(Value_val(Val), Int_val(MDKindID))));
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_metadata(value Val, value MDKindID, value MD) {
  CAMLparam3(Val, MDKindID, MD);
  LLVMSetMetadata(Value_val(Val), Int_val(MDKindID), Value_val(MD));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> unit */
value llvm_clear_metadata(value Val, value MDKindID) {
  CAMLparam2(Val, MDKindID);
  LLVMSetMetadata(Value_val(Val), Int_val(MDKindID), NULL);
  CAMLreturn(Val_unit);
}

/*--... Operations on metadata .............................................--*/

/* llcontext -> string -> llvalue */
value llvm_mdstring(value C, value S) {
  CAMLparam2(C, S);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMMDStringInContext(Context_val(C), String_val(S),
                          caml_string_length(S));
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
value llvm_mdnode(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int len = Wosize_val(ElementVals);
  Temp = caml_alloc(len, Abstract_tag);
  for (unsigned i = 0; i < len; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMMDNodeInContext(Context_val(C), (LLVMValueRef*)Temp, len);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue */
value llvm_mdnull(value C) {
  CAMLparam1(C);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = NULL;
  CAMLreturn(Ret);
}

/* llvalue -> string option */
value llvm_get_mdstring(value V) {
  CAMLparam1(V);
  unsigned Len;
  const char *CStr = LLVMGetMDString(Value_val(V), &Len);
  CAMLreturn(cstr_to_string_option(CStr, Len));
}

/* llvalue -> llvalue array */
value llvm_get_mdnode_operands(value Value) {
  CAMLparam1(Value);
  CAMLlocal2(Temp, Operands);
  LLVMValueRef V = Value_val(Value);
  unsigned int n = LLVMGetMDNodeNumOperands(V);
  Operands = caml_alloc_tuple_uninit(n);
  Temp = caml_alloc(n, Abstract_tag);
  LLVMGetMDNodeOperands(V, (LLVMValueRef*) Temp);
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Value_val(Box) = (LLVMValueRef)Field(Temp, i);
    Field(Operands, i) = Box;
  }
  CAMLreturn(Operands);
}

/* llmodule -> string -> llvalue array */
value llvm_get_namedmd(value M, value Name) {
  CAMLparam2(M, Name);
  CAMLlocal2(Nodes, Temp);
  unsigned int n =
    LLVMGetNamedMetadataNumOperands(Module_val(M), String_val(Name));
  Nodes = caml_alloc_tuple_uninit(n);
  Temp = caml_alloc(n, Abstract_tag);
  LLVMGetNamedMetadataOperands(Module_val(M), String_val(Name),
                               (LLVMValueRef*)Temp);
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Value_val(Box) = (LLVMValueRef)Field(Temp, i);
    Field(Nodes, i) = Box;
  }
  CAMLreturn(Nodes);
}

/* llmodule -> string -> llvalue -> unit */
value llvm_append_namedmd(value M, value Name, value Val) {
  CAMLparam3(M, Name, Val);
  LLVMAddNamedMetadataOperand(Module_val(M), String_val(Name),
                              Value_val(Val));
  CAMLreturn(Val_unit);
}

/* llvalue -> llmetadata */
value llvm_value_as_metadata(value Val) {
  CAMLparam1(Val);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Metadata_val(Ret) = LLVMValueAsMetadata(Value_val(Val));
  CAMLreturn(Ret);
}

/* llcontext -> llmetadata -> llvalue */
value llvm_metadata_as_value(value C, value MD) {
  CAMLparam2(C, MD);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMMetadataAsValue(Context_val(C), Metadata_val(MD));
  CAMLreturn(Ret);
}

/*--... Operations on scalar constants .....................................--*/

/* lltype -> int -> llvalue */
value llvm_const_int(value IntTy, value N) {
  CAMLparam2(IntTy, N);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstInt(Type_val(IntTy), (long long)Long_val(N), 1);
  CAMLreturn(Ret);
}

/* lltype -> Int64.t -> bool -> llvalue */
value llvm_const_of_int64(value IntTy, value N, value SExt) {
  CAMLparam3(IntTy, N, SExt);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstInt(Type_val(IntTy), Int64_val(N), Bool_val(SExt));
  CAMLreturn(Ret);
}

/* llvalue -> Int64.t option */
value llvm_int64_of_const(value C) {
  CAMLparam1(C);
  LLVMValueRef Const = Value_val(C);
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
  Value_val(Ret) =
    LLVMConstIntOfStringAndSize(Type_val(IntTy), String_val(S),
                                caml_string_length(S), Int_val(Radix));
  CAMLreturn(Ret);
}

/* lltype -> float -> llvalue */
value llvm_const_float(value RealTy, value N) {
  CAMLparam2(RealTy, N);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMConstReal(Type_val(RealTy), Double_val(N));
  CAMLreturn(Ret);
}

/* llvalue -> float option */
value llvm_float_of_const(value C) {
  CAMLparam1(C);
  LLVMValueRef Const = Value_val(C);
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
  Value_val(Ret) =
    LLVMConstRealOfStringAndSize(Type_val(RealTy), String_val(S),
                                 caml_string_length(S));
  CAMLreturn(Ret);
}

/*--... Operations on composite constants ..................................--*/

/* llcontext -> string -> llvalue */
value llvm_const_string(value Context, value Str, value NullTerminate) {
  CAMLparam3(Context, Str, NullTerminate);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstStringInContext(Context_val(Context), String_val(Str),
                             caml_string_length(Str), 1);
  CAMLreturn(Ret);
}

/* llcontext -> string -> llvalue */
value llvm_const_stringz(value Context, value Str, value NullTerminate) {
  CAMLparam3(Context, Str, NullTerminate);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstStringInContext(Context_val(Context), String_val(Str),
                             caml_string_length(Str), 0);
  CAMLreturn(Ret);
}

/* lltype -> llvalue array -> llvalue */
value llvm_const_array(value ElementTy, value ElementVals) {
  CAMLparam2(ElementTy, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstArray(Type_val(ElementTy), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
value llvm_const_struct(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstStructInContext(Context_val(C), (LLVMValueRef*)Temp, n, 0);
  CAMLreturn(Ret);
}

/* lltype -> llvalue array -> llvalue */
value llvm_const_named_struct(value Ty, value ElementVals) {
  CAMLparam2(Ty, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstNamedStruct(Type_val(Ty), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* llcontext -> llvalue array -> llvalue */
value llvm_const_packed_struct(value C, value ElementVals) {
  CAMLparam2(C, ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstStructInContext(Context_val(C), (LLVMValueRef*)Temp, n, 1);
  CAMLreturn(Ret);
}

/* llvalue array -> llvalue */
value llvm_const_vector(value ElementVals) {
  CAMLparam1(ElementVals);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(ElementVals);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(ElementVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMConstVector((LLVMValueRef*) Temp, n);
  CAMLreturn(Ret);
}

/* llvalue -> string option */
value llvm_string_of_const(value C) {
  CAMLparam1(C);
  size_t Len;
  const char *CStr;
  LLVMValueRef Const = Value_val(C);
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
  Value_val(Ret) =
    LLVMGetElementAsConstant(Value_val(Const), Int_val(N));
  CAMLreturn(Ret);
}

/*--... Constant expressions ...............................................--*/

/* Icmp.t -> llvalue -> llvalue -> llvalue */
value llvm_const_icmp(value Pred, value LHSConstant, value RHSConstant) {
  CAMLparam3(Pred, LHSConstant, RHSConstant);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstICmp(Int_val(Pred) + LLVMIntEQ,
                  Value_val(LHSConstant), Value_val(RHSConstant));
  CAMLreturn(Ret);
}

/* Fcmp.t -> llvalue -> llvalue -> llvalue */
value llvm_const_fcmp(value Pred, value LHSConstant, value RHSConstant) {
  CAMLparam3(Pred, LHSConstant, RHSConstant);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstFCmp(Int_val(Pred),
                  Value_val(LHSConstant), Value_val(RHSConstant));
  CAMLreturn(Ret);
}

/* llvalue -> llvalue array -> llvalue */
value llvm_const_gep(value ConstantVal, value Indices) {
  CAMLparam2(ConstantVal, Indices);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(Indices);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstGEP(Value_val(ConstantVal), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* lltype -> llvalue -> llvalue array -> llvalue */
value llvm_const_gep2(value Ty, value ConstantVal, value Indices) {
  CAMLparam3(Ty, ConstantVal, Indices);
  CAMLlocal2(Temp, Ret);
  unsigned int n = Wosize_val(Indices);
  Temp = caml_alloc(n, Abstract_tag);
  for (unsigned int i = 0; i < n; ++i) {
    Field(Temp, i) = (value)Value_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstGEP2(Type_val(Ty), Value_val(ConstantVal),
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
    Field(Temp, i) = (value)Value_val(Field(Indices, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstInBoundsGEP(Value_val(ConstantVal), (LLVMValueRef*)Temp, n);
  CAMLreturn(Ret);
}

/* llvalue -> lltype -> is_signed:bool -> llvalue */
value llvm_const_intcast(value CV, value T, value IsSigned) {
  CAMLparam3(CV, T, IsSigned);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstIntCast(Value_val(CV), Type_val(T), Bool_val(IsSigned));
  CAMLreturn(Ret);
}

/* lltype -> string -> string -> bool -> bool -> llvalue */
value llvm_const_inline_asm(value Ty, value Asm, value Constraints,
                            value HasSideEffects, value IsAlignStack) {
  CAMLparam5(Ty, Asm, Constraints, HasSideEffects, IsAlignStack);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMConstInlineAsm(Type_val(Ty), String_val(Asm),
                       String_val(Constraints), Bool_val(HasSideEffects),
                       Bool_val(IsAlignStack));
  CAMLreturn(Ret);
}

/*--... Operations on global variables, functions, and aliases (globals) ...--*/

/* llvalue -> bool */
value llvm_is_declaration(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_bool(LLVMIsDeclaration(Value_val(Global))));
}

/* llvalue -> Linkage.t */
value llvm_linkage(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetLinkage(Value_val(Global))));
}

/* Linkage.t -> llvalue -> unit */
value llvm_set_linkage(value Linkage, value Global) {
  CAMLparam2(Linkage, Global);
  LLVMSetLinkage(Value_val(Global), Int_val(Linkage));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_unnamed_addr(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_bool(LLVMHasUnnamedAddr(Value_val(Global))));
}

/* bool -> llvalue -> unit */
value llvm_set_unnamed_addr(value UseUnnamedAddr, value Global) {
  CAMLparam2(UseUnnamedAddr, Global);
  LLVMSetUnnamedAddr(Value_val(Global), Bool_val(UseUnnamedAddr));
  CAMLreturn(Val_unit);
}

/* llvalue -> string */
value llvm_section(value Global) {
  CAMLparam1(Global);
  CAMLreturn(caml_copy_string(LLVMGetSection(Value_val(Global))));
}

/* string -> llvalue -> unit */
value llvm_set_section(value Section, value Global) {
  CAMLparam2(Section, Global);
  LLVMSetSection(Value_val(Global), String_val(Section));
  CAMLreturn(Val_unit);
}

/* llvalue -> Visibility.t */
value llvm_visibility(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetVisibility(Value_val(Global))));
}

/* Visibility.t -> llvalue -> unit */
value llvm_set_visibility(value Viz, value Global) {
  CAMLparam2(Viz, Global);
  LLVMSetVisibility(Value_val(Global), Int_val(Viz));
  CAMLreturn(Val_unit);
}

/* llvalue -> DLLStorageClass.t */
value llvm_dll_storage_class(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetDLLStorageClass(Value_val(Global))));
}

/* DLLStorageClass.t -> llvalue -> unit */
value llvm_set_dll_storage_class(value Viz, value Global) {
  CAMLparam2(Viz, Global);
  LLVMSetDLLStorageClass(Value_val(Global), Int_val(Viz));
  CAMLreturn(Val_unit);
}

/* llvalue -> int */
value llvm_alignment(value Global) {
  CAMLparam1(Global);
  CAMLreturn(Val_int(LLVMGetAlignment(Value_val(Global))));
}

/* int -> llvalue -> unit */
value llvm_set_alignment(value Bytes, value Global) {
  CAMLparam2(Bytes, Global);
  LLVMSetAlignment(Value_val(Global), Int_val(Bytes));
  CAMLreturn(Val_unit);
}

/* llvalue -> (llmdkind * llmetadata) array */
value llvm_global_copy_all_metadata(value Global) {
  CAMLparam1(Global);
  CAMLlocal1(Array);
  size_t NumEntries;
  LLVMValueMetadataEntry *Entries =
      LLVMGlobalCopyAllMetadata(Value_val(Global), &NumEntries);
  Array = caml_alloc_tuple(NumEntries);
  for (int i = 0; i < NumEntries; i++) {
    value Metadata = caml_alloc(1, Abstract_tag);
    Metadata_val(Metadata) =
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
  CAMLreturn(ptr_to_option(LLVMGetFirstUse(Value_val(Val))));
}

/* lluse -> lluse option */
value llvm_use_succ(value U) {
  CAMLparam1(U);
  CAMLreturn(ptr_to_option(LLVMGetNextUse(Use_val(U))));
}

/* lluse -> llvalue */
value llvm_user(value UR) {
  CAMLparam1(UR);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMGetUser(Use_val(UR));
  CAMLreturn(Ret);
}

/* lluse -> llvalue */
value llvm_used_value(value UR) {
  CAMLparam1(UR);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMGetUsedValue(Use_val(UR));
  CAMLreturn(Ret);
}

/*--... Operations on global variables .....................................--*/

DEFINE_ITERATORS(global, Global, Module_val, LLVMValueRef, Value_val,
                 LLVMGetGlobalParent)

/* lltype -> string -> llmodule -> llvalue */
value llvm_declare_global(value Ty, value Name, value M) {
  CAMLparam3(Ty, Name, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar;
  if ((GlobalVar = LLVMGetNamedGlobal(Module_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(GlobalVar) != Type_val(Ty)) {
      Value_val(Ret) =
        LLVMConstBitCast(GlobalVar, LLVMPointerType(Type_val(Ty), 0));
      CAMLreturn(Ret);
    }
    Value_val(Ret) = GlobalVar;
    CAMLreturn(Ret);
  }
  Value_val(Ret) =
    LLVMAddGlobal(Module_val(M), Type_val(Ty), String_val(Name));
  CAMLreturn(Ret);
}

/* lltype -> string -> int -> llmodule -> llvalue */
value llvm_declare_qualified_global(value Ty, value Name, value AddressSpace,
                                    value M) {
  CAMLparam4(Ty, Name, AddressSpace, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar;
  if ((GlobalVar = LLVMGetNamedGlobal(Module_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(GlobalVar) != Type_val(Ty)) {
      Value_val(Ret) =
        LLVMConstBitCast(GlobalVar, LLVMPointerType(Type_val(Ty),
                         Int_val(AddressSpace)));
      CAMLreturn(Ret);
    }
    Value_val(Ret) = GlobalVar;
    CAMLreturn(Ret);
  }
  Value_val(Ret) =
    LLVMAddGlobalInAddressSpace(Module_val(M), Type_val(Ty),
                                String_val(Name), Int_val(AddressSpace));
  CAMLreturn(Ret);
}

/* string -> llmodule -> llvalue option */
value llvm_lookup_global(value Name, value M) {
  CAMLparam2(Name, M);
  CAMLreturn(
    ptr_to_option(LLVMGetNamedGlobal(Module_val(M), String_val(Name))));
}

/* string -> llvalue -> llmodule -> llvalue */
value llvm_define_global(value Name, value Initializer, value M) {
  CAMLparam3(Name, Initializer, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar =
      LLVMAddGlobal(Module_val(M), LLVMTypeOf(Value_val(Initializer)),
                    String_val(Name));
  LLVMSetInitializer(GlobalVar, Value_val(Initializer));
  Value_val(Ret) = GlobalVar;
  CAMLreturn(Ret);
}

/* string -> llvalue -> int -> llmodule -> llvalue */
value llvm_define_qualified_global(value Name, value Initializer,
                                   value AddressSpace, value M) {
  CAMLparam4(Name, Initializer, AddressSpace, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef GlobalVar = LLVMAddGlobalInAddressSpace(
      Module_val(M), LLVMTypeOf(Value_val(Initializer)),
      String_val(Name), Int_val(AddressSpace));
  LLVMSetInitializer(GlobalVar, Value_val(Initializer));
  Value_val(Ret) = GlobalVar;
  CAMLreturn(Ret);
}

/* llvalue -> unit */
value llvm_delete_global(value GlobalVar) {
  CAMLparam1(GlobalVar);
  LLVMDeleteGlobal(Value_val(GlobalVar));
  CAMLreturn(Val_unit);
}

/* llvalue -> llvalue option */
value llvm_global_initializer(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(ptr_to_option(LLVMGetInitializer(Value_val(GlobalVar))));
}

/* llvalue -> llvalue -> unit */
value llvm_set_initializer(value ConstantVal, value GlobalVar) {
  CAMLparam2(ConstantVal, GlobalVar);
  LLVMSetInitializer(Value_val(GlobalVar), Value_val(ConstantVal));
  CAMLreturn(Val_unit);
}

/* llvalue -> unit */
value llvm_remove_initializer(value GlobalVar) {
  CAMLparam1(GlobalVar);
  LLVMSetInitializer(Value_val(GlobalVar), NULL);
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_thread_local(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsThreadLocal(Value_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_thread_local(value IsThreadLocal, value GlobalVar) {
  CAMLparam2(IsThreadLocal, GlobalVar);
  LLVMSetThreadLocal(Value_val(GlobalVar), Bool_val(IsThreadLocal));
  CAMLreturn(Val_unit);
}

/* llvalue -> ThreadLocalMode.t */
value llvm_thread_local_mode(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_int(LLVMGetThreadLocalMode(Value_val(GlobalVar))));
}

/* ThreadLocalMode.t -> llvalue -> unit */
value llvm_set_thread_local_mode(value ThreadLocalMode, value GlobalVar) {
  CAMLparam2(ThreadLocalMode, GlobalVar);
  LLVMSetThreadLocalMode(Value_val(GlobalVar), Int_val(ThreadLocalMode));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_externally_initialized(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsExternallyInitialized(Value_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_externally_initialized(value IsExternallyInitialized,
                                      value GlobalVar) {
  CAMLparam2(IsExternallyInitialized, GlobalVar);
  LLVMSetExternallyInitialized(Value_val(GlobalVar),
                               Bool_val(IsExternallyInitialized));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_global_constant(value GlobalVar) {
  CAMLparam1(GlobalVar);
  CAMLreturn(Val_bool(LLVMIsGlobalConstant(Value_val(GlobalVar))));
}

/* bool -> llvalue -> unit */
value llvm_set_global_constant(value Flag, value GlobalVar) {
  CAMLparam2(Flag, GlobalVar);
  LLVMSetGlobalConstant(Value_val(GlobalVar), Bool_val(Flag));
  CAMLreturn(Val_unit);
}

/*--... Operations on aliases ..............................................--*/

/* llmodule -> lltype -> llvalue -> string -> llvalue */
value llvm_add_alias(value M, value Ty, value Aliasee, value Name) {
  CAMLparam4(M, Ty, Aliasee, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMAddAlias(Module_val(M), Type_val(Ty),
                                    Value_val(Aliasee), String_val(Name));
  CAMLreturn(Ret);
}

/* llmodule -> lltype -> int -> llvalue -> string -> llvalue */
value llvm_add_alias2(value M, value ValueTy, value AddrSpace,
                      value Aliasee, value Name) {
  CAMLparam5(M, ValueTy, AddrSpace, Aliasee, Name);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMAddAlias2(Module_val(M), Type_val(ValueTy),
                  Int_val(AddrSpace), Value_val(Aliasee), String_val(Name));
  CAMLreturn(Ret);
}

/*--... Operations on functions ............................................--*/

DEFINE_ITERATORS(function, Function, Module_val, LLVMValueRef, Value_val,
                 LLVMGetGlobalParent)

/* string -> lltype -> llmodule -> llvalue */
value llvm_declare_function(value Name, value Ty, value M) {
  CAMLparam3(Name, Ty, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef Fn;
  if ((Fn = LLVMGetNamedFunction(Module_val(M), String_val(Name)))) {
    if (LLVMGlobalGetValueType(Fn) != Type_val(Ty)) {
      Value_val(Ret) =
        LLVMConstBitCast(Fn, LLVMPointerType(Type_val(Ty), 0));
      CAMLreturn(Ret);
    }
    Value_val(Ret) = Fn;
    CAMLreturn(Ret);
  }
  Value_val(Ret) =
    LLVMAddFunction(Module_val(M), String_val(Name), Type_val(Ty));
  CAMLreturn(Ret);
}

/* string -> llmodule -> llvalue option */
value llvm_lookup_function(value Name, value M) {
  CAMLparam2(Name, M);
  CAMLreturn(
    ptr_to_option(LLVMGetNamedFunction(Module_val(M), String_val(Name))));
}

/* string -> lltype -> llmodule -> llvalue */
value llvm_define_function(value Name, value Ty, value M) {
  CAMLparam3(Name, Ty, M);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  LLVMValueRef Fn =
    LLVMAddFunction(Module_val(M), String_val(Name), Type_val(Ty));
  LLVMAppendBasicBlockInContext(LLVMGetTypeContext(Type_val(Ty)),
                                Fn, "entry");
  Value_val(Ret) = Fn;
  CAMLreturn(Ret);
}

/* llvalue -> unit */
value llvm_delete_function(value Fn) {
  CAMLparam1(Fn);
  LLVMDeleteFunction(Value_val(Fn));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_intrinsic(value Fn) {
  CAMLparam1(Fn);
  CAMLreturn(Val_bool(LLVMGetIntrinsicID(Value_val(Fn))));
}

/* llvalue -> int */
value llvm_function_call_conv(value Fn) {
  CAMLparam1(Fn);
  CAMLreturn(Val_int(LLVMGetFunctionCallConv(Value_val(Fn))));
}

/* int -> llvalue -> unit */
value llvm_set_function_call_conv(value Id, value Fn) {
  CAMLparam1(Fn);
  LLVMSetFunctionCallConv(Value_val(Fn), Int_val(Id));
  CAMLreturn(Val_unit);
}

/* llvalue -> string option */
value llvm_gc(value Fn) {
  CAMLparam1(Fn);
  const char *GC = LLVMGetGC(Value_val(Fn));
  if (!GC) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(caml_copy_string(GC)));
}

/* string option -> llvalue -> unit */
value llvm_set_gc(value GC, value Fn) {
  CAMLparam2(GC, Fn);
  LLVMSetGC(Value_val(Fn), GC == Val_none ? 0 : String_val(Field(GC, 0)));
  CAMLreturn(Val_unit);
}

/* llvalue -> llattribute -> int -> unit */
value llvm_add_function_attr(value F, value A, value Index) {
  CAMLparam3(F, A, Index);
  LLVMAddAttributeAtIndex(Value_val(F), Int_val(Index),
                          Attribute_val(A));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> llattribute array */
value llvm_function_attrs(value F, value Index) {
  CAMLparam2(F, Index);
  CAMLlocal2(Array, Temp);
  unsigned Length =
    LLVMGetAttributeCountAtIndex(Value_val(F), Int_val(Index));
  Array = caml_alloc_tuple_uninit(Length);
  Temp = caml_alloc(Length, Abstract_tag);
  LLVMGetAttributesAtIndex(Value_val(F), Int_val(Index),
                           (LLVMAttributeRef *)Op_val(Temp));
  for (unsigned int i = 0; i < Length; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Attribute_val(Box) = (LLVMAttributeRef)Field(Temp, i);
    Store_field(Array, i, Box);
  }
  CAMLreturn(Array);
}

/* llvalue -> llattrkind -> int -> unit */
value llvm_remove_enum_function_attr(value F, value Kind, value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveEnumAttributeAtIndex(Value_val(F), Int_val(Index),
                                 Int_val(Kind));
  CAMLreturn(Val_unit);
}

/* llvalue -> string -> int -> unit */
value llvm_remove_string_function_attr(value F, value Kind,
                                       value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveStringAttributeAtIndex(Value_val(F), Int_val(Index),
                                   String_val(Kind),
                                   caml_string_length(Kind));
  CAMLreturn(Val_unit);
}

/*--... Operations on parameters ...........................................--*/

DEFINE_ITERATORS(param, Param, Value_val, LLVMValueRef, Value_val,
                 LLVMGetParamParent)

/* llvalue -> int -> llvalue */
value llvm_param(value Fn, value Index) {
  CAMLparam2(Fn, Index);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMGetParam(Value_val(Fn), Int_val(Index));
  CAMLreturn(Ret);
}

/* llvalue -> llvalue array */
value llvm_params(value Fn) {
  CAMLparam1(Fn);
  CAMLlocal2(Temp, Params);
  unsigned int n = LLVMCountParams(Value_val(Fn));
  Temp = caml_alloc(n, Abstract_tag);
  Params = caml_alloc_tuple_uninit(n);
  LLVMGetParams(Value_val(Fn), (LLVMValueRef *)Op_val(Temp));
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Value_val(Box) = (LLVMValueRef)Field(Temp, i);
    Store_field(Params, i, Box);
  }
  CAMLreturn(Params);
}

/*--... Operations on basic blocks .........................................--*/

DEFINE_ITERATORS(block, BasicBlock, Value_val, LLVMBasicBlockRef,
                 BasicBlock_val, LLVMGetBasicBlockParent)

/* llbasicblock -> llvalue option */
value llvm_block_terminator(value Block) {
  CAMLparam1(Block);
  CAMLreturn(
    ptr_to_option(LLVMGetBasicBlockTerminator(BasicBlock_val(Block))));
}

/* llvalue -> llbasicblock array */
value llvm_basic_blocks(value Fn) {
  CAMLparam1(Fn);
  CAMLlocal2(Temp, MLArray);
  unsigned int n = LLVMCountBasicBlocks(Value_val(Fn));
  Temp = caml_alloc(n, Abstract_tag);
  MLArray = caml_alloc_tuple_uninit(n);
  LLVMGetBasicBlocks(Value_val(Fn), (LLVMBasicBlockRef *)Op_val(Temp));
  for (unsigned int i = 0; i < n; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    BasicBlock_val(Box) = (LLVMBasicBlockRef)Field(Temp, i);
    Store_field(MLArray, i, Box);
  }
  CAMLreturn(MLArray);
}

/* llbasicblock -> unit */
value llvm_delete_block(value BB) {
  CAMLparam1(BB);
  LLVMDeleteBasicBlock(BasicBlock_val(BB));
  CAMLreturn(Val_unit);
}

/* llbasicblock -> unit */
value llvm_remove_block(value BB) {
  CAMLparam1(BB);
  LLVMRemoveBasicBlockFromParent(BasicBlock_val(BB));
  CAMLreturn(Val_unit);
}

/* llbasicblock -> llbasicblock -> unit */
value llvm_move_block_before(value Pos, value BB) {
  CAMLparam2(Pos, BB);
  LLVMMoveBasicBlockBefore(BasicBlock_val(BB), BasicBlock_val(Pos));
  CAMLreturn(Val_unit);
}

/* llbasicblock -> llbasicblock -> unit */
value llvm_move_block_after(value Pos, value BB) {
  CAMLparam2(Pos, BB);
  LLVMMoveBasicBlockAfter(BasicBlock_val(BB), BasicBlock_val(Pos));
  CAMLreturn(Val_unit);
}

/* string -> llvalue -> llbasicblock */
value llvm_append_block(value Context, value Name, value Fn) {
  CAMLparam3(Context, Name, Fn);
  CAMLlocal1(Ret);
  BasicBlock_val(Ret) =
    LLVMAppendBasicBlockInContext(Context_val(Context),
                                  Value_val(Fn), String_val(Name));
  CAMLreturn(Ret);
}

/* llcontext -> string -> llbasicblock -> llbasicblock */
value llvm_insert_block(value Context, value Name, value BB) {
  CAMLparam3(Context, Name, BB);
  CAMLlocal1(Ret);
  BasicBlock_val(Ret) = LLVMInsertBasicBlockInContext(
    Context_val(Context), BasicBlock_val(BB), String_val(Name));
  CAMLreturn(Ret);
}

/* llvalue -> bool */
value llvm_value_is_block(value Val) {
  CAMLparam1(Val);
  CAMLreturn(Val_bool(LLVMValueIsBasicBlock(Value_val(Val))));
}

/*--... Operations on instructions .........................................--*/

DEFINE_ITERATORS(instr, Instruction, BasicBlock_val, LLVMValueRef, Value_val,
                 LLVMGetInstructionParent)

/* llvalue -> Opcode.t */
value llvm_instr_get_opcode(value Inst) {
  CAMLparam1(Inst);
  LLVMOpcode o;
  if (!LLVMIsAInstruction(Value_val(Inst)))
    caml_failwith("Not an instruction");
  o = LLVMGetInstructionOpcode(Value_val(Inst));
  assert(o <= LLVMFreeze);
  CAMLreturn(Val_int(o));
}

/* llvalue -> ICmp.t option */
value llvm_instr_icmp_predicate(value Val) {
  CAMLparam1(Val);
  int x = LLVMGetICmpPredicate(Value_val(Val));
  if (!x) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(Val_int(x - LLVMIntEQ)));
}

/* llvalue -> FCmp.t option */
value llvm_instr_fcmp_predicate(value Val) {
  CAMLparam1(Val);
  int x = LLVMGetFCmpPredicate(Value_val(Val));
  if (!x) {
    CAMLreturn(Val_none);
  }
  CAMLreturn(caml_alloc_some(Val_int(x - LLVMRealPredicateFalse)));
}

/* llvalue -> llvalue */
value llvm_instr_clone(value Inst) {
  CAMLparam1(Inst);
  CAMLlocal1(Ret);
  if (!LLVMIsAInstruction(Value_val(Inst)))
    caml_failwith("Not an instruction");
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) = LLVMInstructionClone(Value_val(Inst));
  CAMLreturn(Ret);
}

/*--... Operations on call sites ...........................................--*/

/* llvalue -> int */
value llvm_instruction_call_conv(value Inst) {
  CAMLparam1(Inst);
  CAMLreturn(Val_int(LLVMGetInstructionCallConv(Value_val(Inst))));
}

/* int -> llvalue -> unit */
value llvm_set_instruction_call_conv(value CC, value Inst) {
  CAMLparam2(CC, Inst);
  LLVMSetInstructionCallConv(Value_val(Inst), Int_val(CC));
  CAMLreturn(Val_unit);
}

/* llvalue -> llattribute -> int -> unit */
value llvm_add_call_site_attr(value F, value A, value Index) {
  CAMLparam3(F, A, Index);
  LLVMAddCallSiteAttribute(Value_val(F), Int_val(Index),
                           Attribute_val(A));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> llattribute array */
value llvm_call_site_attrs(value F, value Index) {
  CAMLparam2(F, Index);
  CAMLlocal2(Temp, Array);
  unsigned Count =
    LLVMGetCallSiteAttributeCount(Value_val(F), Int_val(Index));
  Temp = caml_alloc(1, Abstract_tag);
  Array = caml_alloc_tuple_uninit(Count);
  LLVMGetCallSiteAttributes(Value_val(F), Int_val(Index),
                            (LLVMAttributeRef *)Op_val(Temp));
  for (unsigned int i = 0; i < Count; ++i) {
    value Box = caml_alloc(1, Abstract_tag);
    Attribute_val(Box) = (LLVMAttributeRef)Field(Temp, i);
    Store_field(Array, i, Box);
  }
  CAMLreturn(Array);
}

/* llvalue -> llattrkind -> int -> unit */
value llvm_remove_enum_call_site_attr(value F, value Kind, value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveCallSiteEnumAttribute(Value_val(F), Int_val(Index),
                                  Int_val(Kind));
  CAMLreturn(Val_unit);
}

/* llvalue -> string -> int -> unit */
value llvm_remove_string_call_site_attr(value F, value Kind, value Index) {
  CAMLparam3(F, Kind, Index);
  LLVMRemoveCallSiteStringAttribute(Value_val(F), Int_val(Index),
                                    String_val(Kind),
                                    caml_string_length(Kind));
  CAMLreturn(Val_unit);
}

/*--... Operations on call instructions (only) .............................--*/

/* llvalue -> int */
value llvm_num_arg_operands(value V) {
  CAMLparam1(V);
  CAMLreturn(Val_int(LLVMGetNumArgOperands(Value_val(V))));
}

/* llvalue -> bool */
value llvm_is_tail_call(value CallInst) {
  CAMLparam1(CallInst);
  CAMLreturn(Val_bool(LLVMIsTailCall(Value_val(CallInst))));
}

/* bool -> llvalue -> unit */
value llvm_set_tail_call(value IsTailCall, value CallInst) {
  CAMLparam2(IsTailCall, CallInst);
  LLVMSetTailCall(Value_val(CallInst), Bool_val(IsTailCall));
  CAMLreturn(Val_unit);
}

/*--... Operations on load/store instructions (only)........................--*/

/* llvalue -> bool */
value llvm_is_volatile(value MemoryInst) {
  CAMLparam1(MemoryInst);
  CAMLreturn(Val_bool(LLVMGetVolatile(Value_val(MemoryInst))));
}

/* bool -> llvalue -> unit */
value llvm_set_volatile(value IsVolatile, value MemoryInst) {
  CAMLparam1(MemoryInst);
  LLVMSetVolatile(Value_val(MemoryInst), Bool_val(IsVolatile));
  CAMLreturn(Val_unit);
}

/*--.. Operations on terminators ...........................................--*/

/* llvalue -> int -> llbasicblock */
value llvm_successor(value V, value I) {
  CAMLparam2(V, I);
  CAMLreturn(alloc_basic_block(LLVMGetSuccessor(Value_val(V), Int_val(I))));
}

/* llvalue -> int -> llvalue -> unit */
value llvm_set_successor(value U, value I, value B) {
  CAMLparam3(U, I, B);
  LLVMSetSuccessor(Value_val(U), Int_val(I), BasicBlock_val(B));
  CAMLreturn(Val_unit);
}

/* llvalue -> int */
value llvm_num_successors(value V) {
  CAMLparam1(V);
  CAMLreturn(Val_int(LLVMGetNumSuccessors(Value_val(V))));
}

/*--.. Operations on branch ................................................--*/

/* llvalue -> llvalue */
value llvm_condition(value V) {
  CAMLparam1(V);
  CAMLreturn(alloc_value(LLVMGetCondition(Value_val(V))));
}

/* llvalue -> llvalue -> unit */
value llvm_set_condition(value B, value C) {
  CAMLparam2(B, C);
  LLVMSetCondition(Value_val(B), Value_val(C));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_conditional(value V) {
  CAMLparam1(V);
  CAMLreturn(Val_bool(LLVMIsConditional(Value_val(V))));
}

/*--... Operations on phi nodes ............................................--*/

/* (llvalue * llbasicblock) -> llvalue -> unit */
value llvm_add_incoming(value Incoming, value PhiNode) {
  CAMLparam2(Incoming, PhiNode);
  LLVMAddIncoming(Value_val(PhiNode), &Value_val(Field(Incoming, 0)),
                  &BasicBlock_val(Field(Incoming, 1)), 1);
  CAMLreturn(Val_unit);
}

/* llvalue -> (llvalue * llbasicblock) list */
value llvm_incoming(value Phi) {
  unsigned I;
  CAMLparam1(Phi);
  CAMLlocal2(Hd, Tl);
  LLVMValueRef PhiNode = Value_val(Phi);

  /* Build a tuple list of them. */
  Tl = Val_int(0);
  for (I = LLVMCountIncoming(PhiNode); I != 0;) {
    value BoxedValue = caml_alloc(1, Abstract_tag);
    Value_val(BoxedValue) = LLVMGetIncomingValue(PhiNode, --I);
    value BoxedBlock = caml_alloc(1, Abstract_tag);
    BasicBlock_val(BoxedBlock) = LLVMGetIncomingBlock(PhiNode, I);
    Hd = caml_alloc_small(2, 0);
    Field(Hd, 0) = BoxedValue;
    Field(Hd, 1) = BoxedBlock;

    value Tmp = caml_alloc_small(2, 0);
    Field(Tmp, 0) = Hd;
    Field(Tmp, 1) = Tl;
    Tl = Tmp;
  }

  CAMLreturn(Tl);
}

/* llvalue -> unit */
value llvm_delete_instruction(value Instruction) {
  CAMLparam1(Instruction);
  LLVMInstructionEraseFromParent(Value_val(Instruction));
  CAMLreturn(Val_unit);
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
  value V = caml_alloc_custom(&builder_ops, sizeof(LLVMBuilderRef), 0, 1);
  Builder_val(V) = B;
  return V;
}

/* llcontext -> llbuilder */
value llvm_builder(value C) {
  CAMLparam1(C);
  CAMLreturn(alloc_builder(LLVMCreateBuilderInContext(Context_val(C))));
}

/* (llbasicblock, llvalue) llpos -> llbuilder -> unit */
value llvm_position_builder(value Pos, value B) {
  CAMLparam2(Pos, B);
  if (Tag_val(Pos) == 0) {
    LLVMBasicBlockRef BB = (LLVMBasicBlockRef)Op_val(Field(Pos, 0));
    LLVMPositionBuilderAtEnd(Builder_val(B), BB);
  } else {
    LLVMValueRef I = (LLVMValueRef)Op_val(Field(Pos, 0));
    LLVMPositionBuilderBefore(Builder_val(B), I);
  }
  CAMLreturn(Val_unit);
}

/* llbuilder -> llbasicblock */
value llvm_insertion_block(value B) {
  CAMLparam1(B);
  LLVMBasicBlockRef InsertBlock = LLVMGetInsertBlock(Builder_val(B));
  if (!InsertBlock)
    caml_raise_not_found();
  CAMLreturn(alloc_basic_block(InsertBlock));
}

/* llvalue -> string -> llbuilder -> unit */
value llvm_insert_into_builder(value I, value Name, value B) {
  CAMLparam3(I, Name, B);
  LLVMInsertIntoBuilderWithName(Builder_val(B), Value_val(I),
                                String_val(Name));
  CAMLreturn(Val_unit);
}

/*--... Metadata ...........................................................--*/

/* llbuilder -> llvalue -> unit */
value llvm_set_current_debug_location(value B, value V) {
  CAMLparam2(B, V);
  LLVMSetCurrentDebugLocation(Builder_val(B), Value_val(V));
  CAMLreturn(Val_unit);
}

/* llbuilder -> unit */
value llvm_clear_current_debug_location(value B) {
  CAMLparam1(B);
  LLVMSetCurrentDebugLocation(Builder_val(B), NULL);
  CAMLreturn(Val_unit);
}

/* llbuilder -> llvalue option */
value llvm_current_debug_location(value B) {
  CAMLparam1(B);
  CAMLreturn(ptr_to_option(LLVMGetCurrentDebugLocation(Builder_val(B))));
}

/* llbuilder -> llvalue -> unit */
value llvm_set_inst_debug_location(value B, value V) {
  CAMLparam2(B, V);
  LLVMSetInstDebugLocation(Builder_val(B), Value_val(V));
  CAMLreturn(Val_unit);
}

/*--... Terminators ........................................................--*/

/* llbuilder -> llvalue */
value llvm_build_ret_void(value B) {
  CAMLparam1(B);
  CAMLreturn(alloc_value(LLVMBuildRetVoid(Builder_val(B))));
}

/* llvalue -> llbuilder -> llvalue */
value llvm_build_ret(value Val, value B) {
  CAMLparam2(Val, B);
  CAMLreturn(alloc_value(LLVMBuildRet(Builder_val(B), Value_val(Val))));
}

/* llvalue array -> llbuilder -> llvalue */
value llvm_build_aggregate_ret(value RetVals, value B) {
  CAMLparam2(RetVals, B);
  CAMLlocal2(Temp, Ret);
  unsigned int Count = Wosize_val(RetVals);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value)Value_val(Field(RetVals, i));
  }
  Ret = caml_alloc(1, Abstract_tag);
  Value_val(Ret) =
    LLVMBuildAggregateRet(Builder_val(B), (LLVMValueRef *)Op_val(Temp), Count);
  CAMLreturn(Ret);
}

/* llbasicblock -> llbuilder -> llvalue */
value llvm_build_br(value BB, value B) {
  CAMLparam2(BB, B);
  CAMLreturn(alloc_value(LLVMBuildBr(Builder_val(B), BasicBlock_val(BB))));
}

/* llvalue -> llbasicblock -> llbasicblock -> llbuilder -> llvalue */
value llvm_build_cond_br(value If, value Then, value Else, value B) {
  CAMLparam4(If, Then, Else, B);
  CAMLreturn(
    alloc_value(LLVMBuildCondBr(Builder_val(B), Value_val(If),
                                BasicBlock_val(Then), BasicBlock_val(Else))));
}

/* llvalue -> llbasicblock -> int -> llbuilder -> llvalue */
value llvm_build_switch(value Of, value Else, value EstimatedCount, value B) {
  CAMLparam4(Of, Else, EstimatedCount, B);
  CAMLreturn(
    alloc_value(LLVMBuildSwitch(Builder_val(B), Value_val(Of),
                              BasicBlock_val(Else), Int_val(EstimatedCount))));
}

/* lltype -> string -> llbuilder -> llvalue */
value llvm_build_malloc(value Ty, value Name, value B) {
  CAMLparam3(Ty, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildMalloc(Builder_val(B), Type_val(Ty),
                                String_val(Name))));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_array_malloc(value Ty, value Val, value Name, value B) {
  CAMLparam4(Ty, Val, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildArrayMalloc(Builder_val(B), Type_val(Ty),
                                     Value_val(Val), String_val(Name))));
}

/* llvalue -> llbuilder -> llvalue */
value llvm_build_free(value P, value B) {
  CAMLparam2(P, B);
  CAMLreturn(alloc_value(LLVMBuildFree(Builder_val(B), Value_val(P))));
}

/* llvalue -> llvalue -> llbasicblock -> unit */
value llvm_add_case(value Switch, value OnVal, value Dest) {
  CAMLparam3(Switch, OnVal, Dest);
  LLVMAddCase(Value_val(Switch), Value_val(OnVal), BasicBlock_val(Dest));
  CAMLreturn(Val_unit);
}

/* llvalue -> int -> llbuilder -> llvalue */
value llvm_build_indirect_br(value Addr, value EstimatedDests, value B) {
  CAMLparam3(Addr, EstimatedDests, B);
  CAMLreturn(
    alloc_value(LLVMBuildIndirectBr(Builder_val(B), Value_val(Addr),
                                    Int_val(EstimatedDests))));
}

/* llvalue -> llbasicblock -> unit */
value llvm_add_destination(value IndirectBr, value Dest) {
  CAMLparam2(IndirectBr, Dest);
  LLVMAddDestination(Value_val(IndirectBr), BasicBlock_val(Dest));
  CAMLreturn(Val_unit);
}

/* llvalue -> llvalue array -> llbasicblock -> llbasicblock -> string ->
   llbuilder -> llvalue */
value llvm_build_invoke_nat(value Fn, value Args, value Then, value Catch,
                            value Name, value B) {
  CAMLparam5(Fn, Args, Then, Catch, Name);
  CAMLxparam1(B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Args);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Args, i));
  }
  CAMLreturn(
    alloc_value(LLVMBuildInvoke(Builder_val(B), Value_val(Fn),
               (LLVMValueRef *)Op_val(Temp), Count, BasicBlock_val(Then),
               BasicBlock_val(Catch), String_val(Name))));
}

/* llvalue -> llvalue array -> llbasicblock -> llbasicblock -> string ->
   llbuilder -> llvalue */
value llvm_build_invoke_bc(value Args[], int NumArgs) {
  return llvm_build_invoke_nat(Args[0], Args[1], Args[2],
                               Args[3], Args[4], Args[5]);
}

/* lltype -> llvalue -> llvalue array -> llbasicblock -> llbasicblock ->
   string -> llbuilder -> llvalue */
value llvm_build_invoke2_nat(value FnTy, value Fn, value Args, value Then,
                             value Catch, value Name, value B) {
  CAMLparam5(FnTy, Fn, Args, Then, Catch);
  CAMLxparam2(Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Args);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value)Value_val(Field(Args, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildInvoke2(Builder_val(B), Type_val(FnTy), Value_val(Fn),
                     (LLVMValueRef *)Op_val(Temp), Count,
                     BasicBlock_val(Then), BasicBlock_val(Catch),
                     String_val(Name))));
}

/* lltype -> llvalue -> llvalue array -> llbasicblock -> llbasicblock ->
   string -> llbuilder -> llvalue */
value llvm_build_invoke2_bc(value Args[], int NumArgs) {
  return llvm_build_invoke2_nat(Args[0], Args[1], Args[2], Args[3],
                                Args[4], Args[5], Args[6]);
}

/* lltype -> llvalue -> int -> string -> llbuilder -> llvalue */
value llvm_build_landingpad(value Ty, value PersFn, value NumClauses,
                            value Name, value B) {
  CAMLparam5(Ty, PersFn, NumClauses, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildLandingPad(Builder_val(B), Type_val(Ty),
                                    Value_val(PersFn), Int_val(NumClauses),
                                    String_val(Name))));
}

/* llvalue -> llvalue -> unit */
value llvm_add_clause(value LandingPadInst, value ClauseVal) {
  CAMLparam2(LandingPadInst, ClauseVal);
  LLVMAddClause(Value_val(LandingPadInst), Value_val(ClauseVal));
  CAMLreturn(Val_unit);
}

/* llvalue -> bool */
value llvm_is_cleanup(value LandingPadInst) {
  CAMLparam1(LandingPadInst);
  CAMLreturn(Val_bool(LLVMIsCleanup(Value_val(LandingPadInst))));
}

/* llvalue -> bool -> unit */
value llvm_set_cleanup(value LandingPadInst, value flag) {
  CAMLparam2(LandingPadInst, flag);
  LLVMSetCleanup(Value_val(LandingPadInst), Bool_val(flag));
  CAMLreturn(Val_unit);
}

/* llvalue -> llbuilder -> llvalue */
value llvm_build_resume(value Exn, value B) {
  CAMLparam2(Exn, B);
  CAMLreturn(alloc_value(LLVMBuildResume(Builder_val(B), Value_val(Exn))));
}

/* llbuilder -> llvalue */
value llvm_build_unreachable(value B) {
  CAMLparam1(B);
  CAMLreturn(alloc_value(LLVMBuildUnreachable(Builder_val(B))));
}

/*--... Arithmetic .........................................................--*/

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_add(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildAdd(Builder_val(B), Value_val(LHS), Value_val(RHS),
                             String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nsw_add(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNSWAdd(Builder_val(B), Value_val(LHS), Value_val(RHS),
                                String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nuw_add(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNUWAdd(Builder_val(B), Value_val(LHS),
                                Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fadd(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFAdd(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_sub(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildSub(Builder_val(B), Value_val(LHS), Value_val(RHS),
                             String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nsw_sub(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNSWSub(Builder_val(B), Value_val(LHS), Value_val(RHS),
                                String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nuw_sub(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(
      LLVMBuildNUWSub(Builder_val(B), Value_val(LHS), Value_val(RHS),
                      String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fsub(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFSub(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_mul(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildMul(Builder_val(B), Value_val(LHS), Value_val(RHS),
                             String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nsw_mul(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNSWMul(Builder_val(B), Value_val(LHS),
                                Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nuw_mul(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNUWMul(Builder_val(B), Value_val(LHS), Value_val(RHS),
                                String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fmul(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFMul(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_udiv(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildUDiv(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_sdiv(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildSDiv(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_exact_sdiv(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildExactSDiv(Builder_val(B), Value_val(LHS),
                                   Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fdiv(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFDiv(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_urem(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildURem(Builder_val(B), Value_val(LHS),
                              Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_srem(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildSRem(Builder_val(B), Value_val(LHS),
                              Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_frem(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFRem(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_shl(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildShl(Builder_val(B), Value_val(LHS), Value_val(RHS),
                             String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_lshr(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildLShr(Builder_val(B), Value_val(LHS), Value_val(RHS),
                              String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_ashr(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildAShr(Builder_val(B), Value_val(LHS), Value_val(RHS),
                String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_and(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildAnd(Builder_val(B), Value_val(LHS),
                             Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_or(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildOr(Builder_val(B), Value_val(LHS),
                            Value_val(RHS), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_xor(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildXor(Builder_val(B), Value_val(LHS), Value_val(RHS),
                             String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_neg(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNeg(Builder_val(B), Value_val(X), String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nsw_neg(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNSWNeg(Builder_val(B), Value_val(X),
                                String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_nuw_neg(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNUWNeg(Builder_val(B), Value_val(X),
                                String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fneg(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildFNeg(Builder_val(B), Value_val(X), String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_not(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(
    alloc_value(LLVMBuildNot(Builder_val(B), Value_val(X), String_val(Name))));
}

/*--... Memory .............................................................--*/

/* lltype -> string -> llbuilder -> llvalue */
value llvm_build_alloca(value Ty, value Name, value B) {
  CAMLparam3(Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildAlloca(Builder_val(B), Type_val(Ty), String_val(Name))));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_array_alloca(value Ty, value Size, value Name, value B) {
  CAMLparam4(Ty, Size, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildArrayAlloca(Builder_val(B), Type_val(Ty), Value_val(Size),
                         String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_load(value Pointer, value Name, value B) {
  CAMLparam3(Pointer, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildLoad(Builder_val(B), Value_val(Pointer), String_val(Name))));
}

/* lltype -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_load2(value Ty, value Pointer, value Name, value B) {
  CAMLparam4(Ty, Pointer, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildLoad2(Builder_val(B), Type_val(Ty), Value_val(Pointer),
                   String_val(Name))));
}

/* llvalue -> llvalue -> llbuilder -> llvalue */
LLVMValueRef llvm_build_store(LLVMValueRef Value, LLVMValueRef Pointer,
                              value B) {
  return LLVMBuildStore(Builder_val(B), Value, Pointer);
}

/* AtomicRMWBinOp.t -> llvalue -> llvalue -> AtomicOrdering.t ->
   bool -> string -> llbuilder -> llvalue */
value llvm_build_atomicrmw_native(value BinOp, value Ptr, value Val, value Ord,
                                  value ST, value Name, value B) {
  CAMLparam5(BinOp, Ptr, Val, Ord, ST);
  CAMLxparam2(Name, B);
  LLVMValueRef Instr;
  Instr = LLVMBuildAtomicRMW(Builder_val(B), Int_val(BinOp), Value_val(Ptr),
                             Value_val(Val), Int_val(Ord), Bool_val(ST));
  LLVMSetValueName(Instr, String_val(Name));
  CAMLreturn(alloc_value(Instr));
}

value llvm_build_atomicrmw_bytecode(value *argv, int argn) {
  return llvm_build_atomicrmw_native(argv[0], argv[1], argv[2], argv[3],
                                     argv[4], argv[5], argv[6]);
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_gep(value Pointer, value Indices, value Name, value B) {
  CAMLparam4(Pointer, Indices, Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Indices);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Indices, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildGEP(Builder_val(B), Value_val(Pointer),
                 (LLVMValueRef *)Op_val(Temp), Count, String_val(Name))));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_gep2(value Ty, value Pointer, value Indices, value Name,
                      value B) {
  CAMLparam5(Ty, Pointer, Indices, Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Indices);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Indices, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildGEP2(Builder_val(B), Type_val(Ty), Value_val(Pointer),
                  (LLVMValueRef *)Op_val(Temp), Count, String_val(Name))));
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_in_bounds_gep(value Pointer, value Indices, value Name,
                               value B) {
  CAMLparam4(Pointer, Indices, Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Indices);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Indices, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildInBoundsGEP(Builder_val(B), Value_val(Pointer),
                         (LLVMValueRef *)Op_val(Temp),
                         Count, String_val(Name))));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_in_bounds_gep2(value Ty, value Pointer, value Indices,
                                value Name, value B) {
  CAMLparam5(Ty, Pointer, Indices, Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Indices);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Indices, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildInBoundsGEP2(Builder_val(B), Type_val(Ty), Value_val(Pointer),
                          (LLVMValueRef *)Op_val(Temp), Count,
                          String_val(Name))));
}

/* llvalue -> int -> string -> llbuilder -> llvalue */
value llvm_build_struct_gep(value Pointer, value Index, value Name, value B) {
  CAMLparam4(Pointer, Index, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildStructGEP(Builder_val(B), Value_val(Pointer), Int_val(Index),
                       String_val(Name))));
}

/* lltype -> llvalue -> int -> string -> llbuilder -> llvalue */
value llvm_build_struct_gep2(value Ty, value Pointer, value Index, value Name,
                             value B) {
  CAMLparam5(Ty, Pointer, Index, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildStructGEP2(Builder_val(B), Type_val(Ty), Value_val(Pointer),
                        Int_val(Index), String_val(Name))));
}

/* string -> string -> llbuilder -> llvalue */
value llvm_build_global_string(value Str, value Name, value B) {
  CAMLparam3(Str, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildGlobalString(Builder_val(B), String_val(Str), String_val(Name))));
}

/* string -> string -> llbuilder -> llvalue */
value llvm_build_global_stringptr(value Str, value Name, value B) {
  CAMLparam3(Str, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildGlobalStringPtr(Builder_val(B), String_val(Str),
                             String_val(Name))));
}

/*--... Casts ..............................................................--*/

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_trunc(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildTrunc(Builder_val(B), Value_val(X), Type_val(Ty),
                   String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_zext(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildZExt(Builder_val(B), Value_val(X), Type_val(Ty),
    String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_sext(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildSExt(Builder_val(B), Value_val(X), Type_val(Ty),
                  String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_fptoui(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFPToUI(Builder_val(B), Value_val(X), Type_val(Ty),
                    String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_fptosi(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFPToSI(Builder_val(B), Value_val(X), Type_val(Ty),
                    String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_uitofp(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildUIToFP(Builder_val(B), Value_val(X), Type_val(Ty),
                    String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_sitofp(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildSIToFP(Builder_val(B), Value_val(X), Type_val(Ty),
                    String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_fptrunc(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFPTrunc(Builder_val(B), Value_val(X), Type_val(Ty),
                     String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_fpext(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFPExt(Builder_val(B), Value_val(X), Type_val(Ty),
                   String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_prttoint(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildPtrToInt(Builder_val(B), Value_val(X), Type_val(Ty),
                      String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_inttoptr(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildIntToPtr(Builder_val(B), Value_val(X), Type_val(Ty),
                      String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_bitcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildBitCast(Builder_val(B), Value_val(X), Type_val(Ty),
                     String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_zext_or_bitcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildZExtOrBitCast(Builder_val(B), Value_val(X), Type_val(Ty),
                           String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_sext_or_bitcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildSExtOrBitCast(Builder_val(B), Value_val(X), Type_val(Ty),
                           String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_trunc_or_bitcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildTruncOrBitCast(Builder_val(B), Value_val(X), Type_val(Ty),
                            String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_pointercast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildPointerCast(Builder_val(B), Value_val(X), Type_val(Ty),
                         String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_intcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildIntCast(Builder_val(B), Value_val(X), Type_val(Ty),
                     String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_fpcast(value X, value Ty, value Name, value B) {
  CAMLparam4(X, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFPCast(Builder_val(B), Value_val(X), Type_val(Ty),
                    String_val(Name))));
}

/*--... Comparisons ........................................................--*/

/* Icmp.t -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_icmp(value Pred, value LHS, value RHS, value Name, value B) {
  CAMLparam5(Pred, LHS, RHS, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildICmp(Builder_val(B), Int_val(Pred) + LLVMIntEQ, Value_val(LHS),
                  Value_val(RHS), String_val(Name))));
}

/* Fcmp.t -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_fcmp(value Pred, value LHS, value RHS, value Name, value B) {
  CAMLparam5(Pred, LHS, RHS, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFCmp(Builder_val(B), Int_val(Pred), Value_val(LHS), Value_val(RHS),
                  String_val(Name))));
}

/*--... Miscellaneous instructions .........................................--*/

/* (llvalue * llbasicblock) list -> string -> llbuilder -> llvalue */
value llvm_build_phi(value Incoming, value Name, value B) {
  CAMLparam3(Incoming, Name, B);
  value Hd, Tl;
  LLVMValueRef FirstValue, PhiNode;

  assert(Incoming != Val_int(0) && "Empty list passed to Llvm.build_phi!");

  Hd = Field(Incoming, 0);
  FirstValue = Value_val(Field(Hd, 0));
  PhiNode =
      LLVMBuildPhi(Builder_val(B), LLVMTypeOf(FirstValue), String_val(Name));

  for (Tl = Incoming; Tl != Val_int(0); Tl = Field(Tl, 1)) {
    value Hd = Field(Tl, 0);
    LLVMAddIncoming(PhiNode, &Value_val(Field(Hd, 0)),
                    &BasicBlock_val(Field(Hd, 1)), 1);
  }

  CAMLreturn(alloc_value(PhiNode));
}

/* lltype -> string -> llbuilder -> value */
value llvm_build_empty_phi(value Type, value Name, value B) {
  CAMLparam3(Type, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildPhi(Builder_val(B), Type_val(Type), String_val(Name))));
}

/* llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_call(value Fn, value Params, value Name, value B) {
  CAMLparam4(Fn, Params, Name, B);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Params);
  Temp = caml_alloc(1, Abstract_tag);
  for (int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Params, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildCall(Builder_val(B), Value_val(Fn), (LLVMValueRef *)Op_val(Temp),
                  Count, String_val(Name))));
}

/* lltype -> llvalue -> llvalue array -> string -> llbuilder -> llvalue */
value llvm_build_call2(value FnTy, value Fn, value Params, value Name, value B) {
  CAMLparam5(FnTy, Fn, Params, Name, B);
  CAMLlocal1(Temp);
  unsigned Count = Wosize_val(Params);
  Temp = caml_alloc(1, Abstract_tag);
  for (int i = 0; i < Count; ++i) {
    Field(Temp, i) = (value) Value_val(Field(Params, i));
  }
  CAMLreturn(alloc_value(
    LLVMBuildCall2(Builder_val(B), Type_val(FnTy), Value_val(Fn),
                   (LLVMValueRef *)Op_val(Temp), Count, String_val(Name))));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_select(value If, value Then, value Else, value Name, value B) {
  CAMLparam5(If, Then, Else, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildSelect(Builder_val(B), Value_val(If), Value_val(Then),
                    Value_val(Else), String_val(Name))));
}

/* llvalue -> lltype -> string -> llbuilder -> llvalue */
value llvm_build_va_arg(value List, value Ty, value Name, value B) {
  CAMLparam4(List, Ty, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildVAArg(Builder_val(B), Value_val(List), Type_val(Ty),
                   String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_extractelement(value Vec, value Idx, value Name, value B) {
  CAMLparam4(Vec, Idx, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildExtractElement(Builder_val(B), Value_val(Vec),
                            Value_val(Idx), String_val(Name))));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_insertelement(value Vec, value Element, value Idx, value Name,
                               value B) {
  CAMLparam5(Vec, Element, Idx, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildInsertElement(Builder_val(B), Value_val(Vec), Value_val(Element),
                           Value_val(Idx), String_val(Name))));
}

/* llvalue -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_shufflevector(value V1, value V2, value Mask, value Name,
                               value B) {
  CAMLparam5(V1, V2, Mask, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildShuffleVector(Builder_val(B), Value_val(V1), Value_val(V2),
                           Value_val(Mask), String_val(Name))));
}

/* llvalue -> int -> string -> llbuilder -> llvalue */
value llvm_build_extractvalue(value Aggregate, value Idx, value Name, value B) {
  CAMLparam4(Aggregate, Idx, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildExtractValue(Builder_val(B), Value_val(Aggregate), Int_val(Idx),
                          String_val(Name))));
}

/* llvalue -> llvalue -> int -> string -> llbuilder -> llvalue */
value llvm_build_insertvalue(value Aggregate, value Val, value Idx, value Name,
                             value B) {
  CAMLparam5(Aggregate, Val, Idx, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildInsertValue(Builder_val(B), Value_val(Aggregate), Value_val(Val),
                         Int_val(Idx), String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_is_null(value Val, value Name, value B) {
  CAMLparam3(Val, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildIsNull(Builder_val(B), Value_val(Val), String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_is_not_null(value Val, value Name, value B) {
  CAMLparam3(Val, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildIsNotNull(Builder_val(B), Value_val(Val), String_val(Name))));
}

/* llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_ptrdiff(value LHS, value RHS, value Name, value B) {
  CAMLparam4(LHS, RHS, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildPtrDiff(Builder_val(B), Value_val(LHS), Value_val(RHS),
                     String_val(Name))));
}

/* lltype -> llvalue -> llvalue -> string -> llbuilder -> llvalue */
value llvm_build_ptrdiff2(value ElemTy, value LHS, value RHS, value Name,
                          value B) {
  CAMLparam5(ElemTy, LHS, RHS, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildPtrDiff2(Builder_val(B), Type_val(ElemTy), Value_val(LHS),
                      Value_val(RHS), String_val(Name))));
}

/* llvalue -> string -> llbuilder -> llvalue */
value llvm_build_freeze(value X, value Name, value B) {
  CAMLparam3(X, Name, B);
  CAMLreturn(alloc_value(
    LLVMBuildFreeze(Builder_val(B), Value_val(X), String_val(Name))));
}

/*===-- Memory buffers ----------------------------------------------------===*/

/* string -> llmemorybuffer
   raises IoError msg on error */
value llvm_memorybuffer_of_file(value Path) {
  CAMLparam1(Path);
  CAMLlocal1(Ret);
  char *Message;
  LLVMMemoryBufferRef MemBuf;

  if (LLVMCreateMemoryBufferWithContentsOfFile(String_val(Path), &MemBuf,
                                               &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);
  Ret = caml_alloc(1, Abstract_tag);
  MemoryBuffer_val(Ret) = MemBuf;
  CAMLreturn(Ret);
}

/* unit -> llmemorybuffer
   raises IoError msg on error */
value llvm_memorybuffer_of_stdin(value Unit) {
  CAMLparam1(Unit);
  CAMLlocal1(Ret);
  char *Message;
  LLVMMemoryBufferRef MemBuf;

  if (LLVMCreateMemoryBufferWithSTDIN(&MemBuf, &Message))
    llvm_raise(*caml_named_value("Llvm.IoError"), Message);
  Ret = caml_alloc(1, Abstract_tag);
  MemoryBuffer_val(Ret) = MemBuf;
  CAMLreturn(Ret);
}

/* ?name:string -> string -> llmemorybuffer */
value llvm_memorybuffer_of_string(value Name, value String) {
  CAMLparam2(Name, String);
  CAMLlocal1(Ret);
  LLVMMemoryBufferRef MemBuf;
  const char *NameCStr;

  if (Name == Val_int(0))
    NameCStr = "";
  else
    NameCStr = String_val(Field(Name, 0));

  MemBuf = LLVMCreateMemoryBufferWithMemoryRangeCopy(
      String_val(String), caml_string_length(String), NameCStr);
  Ret = caml_alloc(1, Abstract_tag);
  MemoryBuffer_val(Ret) = MemBuf;
  CAMLreturn(Ret);
}

/* llmemorybuffer -> string */
value llvm_memorybuffer_as_string(value MB) {
  CAMLparam1(MB);
  LLVMMemoryBufferRef MemBuf = MemoryBuffer_val(MB);
  size_t BufferSize = LLVMGetBufferSize(MemBuf);
  const char *BufferStart = LLVMGetBufferStart(MemBuf);
  CAMLreturn(cstr_to_string(BufferStart, BufferSize));
}

/* llmemorybuffer -> unit */
value llvm_memorybuffer_dispose(value MemBuf) {
  CAMLparam1(MemBuf);
  LLVMDisposeMemoryBuffer(MemoryBuffer_val(MemBuf));
  CAMLreturn(Val_unit);
}

/*===-- Pass Managers -----------------------------------------------------===*/

/* unit -> [ `Module ] PassManager.t */
value llvm_passmanager_create(value Unit) {
  CAMLparam1(Unit);
  CAMLlocal1(Ret);
  Ret = caml_alloc(1, Abstract_tag);
  PassManager_val(Ret) = LLVMCreatePassManager();
  CAMLreturn(Ret);
}

/* llmodule -> [ `Function ] PassManager.t -> bool */
value llvm_passmanager_run_module(value M, value PM) {
  CAMLparam2(M, PM);
  CAMLreturn(Val_bool(LLVMRunPassManager(PassManager_val(PM), Module_val(M))));
}

/* [ `Function ] PassManager.t -> bool */
value llvm_passmanager_initialize(value FPM) {
  CAMLparam1(FPM);
  CAMLreturn(Val_bool(LLVMInitializeFunctionPassManager(PassManager_val(FPM))));
}

/* llvalue -> [ `Function ] PassManager.t -> bool */
value llvm_passmanager_run_function(value F, value FPM) {
  CAMLparam2(F, FPM);
  CAMLreturn(
    Val_bool(LLVMRunFunctionPassManager(PassManager_val(FPM), Value_val(F))));
}

/* [ `Function ] PassManager.t -> bool */
value llvm_passmanager_finalize(value FPM) {
  CAMLparam1(FPM);
  CAMLreturn(Val_bool(LLVMFinalizeFunctionPassManager(PassManager_val(FPM))));
}

/* PassManager.any PassManager.t -> unit */
value llvm_passmanager_dispose(value PM) {
  CAMLparam1(PM);
  LLVMDisposePassManager(PassManager_val(PM));
  CAMLreturn(Val_unit);
}
