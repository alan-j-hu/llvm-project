/*===-- debuginfo_ocaml.c - LLVM OCaml Glue ---------------------*- C++ -*-===*\
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

#include <string.h>

#include "caml/memory.h"
#include "caml/mlvalues.h"
#include "llvm-c/Core.h"
#include "llvm-c/DebugInfo.h"
#include "llvm-c/Support.h"

#include "llvm_ocaml.h"

// This is identical to the definition in llvm_debuginfo.ml:DIFlag.t
typedef enum {
  i_DIFlagZero,
  i_DIFlagPrivate,
  i_DIFlagProtected,
  i_DIFlagPublic,
  i_DIFlagFwdDecl,
  i_DIFlagAppleBlock,
  i_DIFlagReservedBit4,
  i_DIFlagVirtual,
  i_DIFlagArtificial,
  i_DIFlagExplicit,
  i_DIFlagPrototyped,
  i_DIFlagObjcClassComplete,
  i_DIFlagObjectPointer,
  i_DIFlagVector,
  i_DIFlagStaticMember,
  i_DIFlagLValueReference,
  i_DIFlagRValueReference,
  i_DIFlagReserved,
  i_DIFlagSingleInheritance,
  i_DIFlagMultipleInheritance,
  i_DIFlagVirtualInheritance,
  i_DIFlagIntroducedVirtual,
  i_DIFlagBitField,
  i_DIFlagNoReturn,
  i_DIFlagTypePassByValue,
  i_DIFlagTypePassByReference,
  i_DIFlagEnumClass,
  i_DIFlagFixedEnum,
  i_DIFlagThunk,
  i_DIFlagNonTrivial,
  i_DIFlagBigEndian,
  i_DIFlagLittleEndian,
  i_DIFlagIndirectVirtualBase,
  i_DIFlagAccessibility,
  i_DIFlagPtrToMemberRep
} LLVMDIFlag_i;

static LLVMDIFlags map_DIFlag(LLVMDIFlag_i DIF) {
  switch (DIF) {
  case i_DIFlagZero:
    return LLVMDIFlagZero;
  case i_DIFlagPrivate:
    return LLVMDIFlagPrivate;
  case i_DIFlagProtected:
    return LLVMDIFlagProtected;
  case i_DIFlagPublic:
    return LLVMDIFlagPublic;
  case i_DIFlagFwdDecl:
    return LLVMDIFlagFwdDecl;
  case i_DIFlagAppleBlock:
    return LLVMDIFlagAppleBlock;
  case i_DIFlagReservedBit4:
    return LLVMDIFlagReservedBit4;
  case i_DIFlagVirtual:
    return LLVMDIFlagVirtual;
  case i_DIFlagArtificial:
    return LLVMDIFlagArtificial;
  case i_DIFlagExplicit:
    return LLVMDIFlagExplicit;
  case i_DIFlagPrototyped:
    return LLVMDIFlagPrototyped;
  case i_DIFlagObjcClassComplete:
    return LLVMDIFlagObjcClassComplete;
  case i_DIFlagObjectPointer:
    return LLVMDIFlagObjectPointer;
  case i_DIFlagVector:
    return LLVMDIFlagVector;
  case i_DIFlagStaticMember:
    return LLVMDIFlagStaticMember;
  case i_DIFlagLValueReference:
    return LLVMDIFlagLValueReference;
  case i_DIFlagRValueReference:
    return LLVMDIFlagRValueReference;
  case i_DIFlagReserved:
    return LLVMDIFlagReserved;
  case i_DIFlagSingleInheritance:
    return LLVMDIFlagSingleInheritance;
  case i_DIFlagMultipleInheritance:
    return LLVMDIFlagMultipleInheritance;
  case i_DIFlagVirtualInheritance:
    return LLVMDIFlagVirtualInheritance;
  case i_DIFlagIntroducedVirtual:
    return LLVMDIFlagIntroducedVirtual;
  case i_DIFlagBitField:
    return LLVMDIFlagBitField;
  case i_DIFlagNoReturn:
    return LLVMDIFlagNoReturn;
  case i_DIFlagTypePassByValue:
    return LLVMDIFlagTypePassByValue;
  case i_DIFlagTypePassByReference:
    return LLVMDIFlagTypePassByReference;
  case i_DIFlagEnumClass:
    return LLVMDIFlagEnumClass;
  case i_DIFlagFixedEnum:
    return LLVMDIFlagFixedEnum;
  case i_DIFlagThunk:
    return LLVMDIFlagThunk;
  case i_DIFlagNonTrivial:
    return LLVMDIFlagNonTrivial;
  case i_DIFlagBigEndian:
    return LLVMDIFlagBigEndian;
  case i_DIFlagLittleEndian:
    return LLVMDIFlagLittleEndian;
  case i_DIFlagIndirectVirtualBase:
    return LLVMDIFlagIndirectVirtualBase;
  case i_DIFlagAccessibility:
    return LLVMDIFlagAccessibility;
  case i_DIFlagPtrToMemberRep:
    return LLVMDIFlagPtrToMemberRep;
  }
}

value llvm_debug_metadata_version(value Unit) {
  return Val_int(LLVMDebugMetadataVersion());
}

value llvm_get_module_debug_metadata_version(value Module) {
  return Val_int(LLVMGetModuleDebugMetadataVersion(Module_val(Module)));
}

#define DIFlags_val(v) (*(LLVMDIFlags *)(Data_custom_val(v)))

static struct custom_operations diflags_ops = {
    (char *)"DebugInfo.lldiflags", custom_finalize_default,
    custom_compare_default,        custom_hash_default,
    custom_serialize_default,      custom_deserialize_default,
    custom_compare_ext_default};

static value alloc_diflags(LLVMDIFlags Flags) {
  value V = alloc_custom(&diflags_ops, sizeof(LLVMDIFlags), 0, 1);
  DIFlags_val(V) = Flags;
  return V;
}

LLVMDIFlags llvm_diflags_get(value i_Flag) {
  LLVMDIFlags Flags = map_DIFlag(Int_val(i_Flag));
  return alloc_diflags(Flags);
}

LLVMDIFlags llvm_diflags_set(value Flags, value i_Flag) {
  LLVMDIFlags FlagsNew = DIFlags_val(Flags) | map_DIFlag(Int_val(i_Flag));
  return alloc_diflags(FlagsNew);
}

value llvm_diflags_test(value Flags, value i_Flag) {
  LLVMDIFlags Flag = map_DIFlag(Int_val(i_Flag));
  return Val_bool((DIFlags_val(Flags) & Flag) == Flag);
}

#define DIBuilder_val(v) (*(LLVMDIBuilderRef *)(Data_custom_val(v)))

static void llvm_finalize_dibuilder(value B) {
  LLVMDIBuilderFinalize(DIBuilder_val(B));
  LLVMDisposeDIBuilder(DIBuilder_val(B));
}

static struct custom_operations dibuilder_ops = {
    (char *)"DebugInfo.lldibuilder", llvm_finalize_dibuilder,
    custom_compare_default,          custom_hash_default,
    custom_serialize_default,        custom_deserialize_default,
    custom_compare_ext_default};

static value alloc_dibuilder(LLVMDIBuilderRef B) {
  value V = alloc_custom(&dibuilder_ops, sizeof(LLVMDIBuilderRef), 0, 1);
  DIBuilder_val(V) = B;
  return V;
}

/* llmodule -> lldibuilder */
value llvm_dibuilder(value M) {
  CAMLparam1(M);
  CAMLreturn(alloc_dibuilder(LLVMCreateDIBuilder(Module_val(M))));
}

value llvm_dibuild_finalize(value Builder) {
  LLVMDIBuilderFinalize(DIBuilder_val(Builder));
  return Val_unit;
}

value llvm_dibuild_create_compile_unit_native(
    value Builder, value Lang, value FileRef, value Producer,
    value IsOptimized, value Flags, value RuntimeVer, value SplitName,
    value Kind, value DWOId, value SplitDebugInline,
    value DebugInfoForProfiling, value SysRoot, value SDK) {
  CAMLparam5(Builder, Lang, FileRef, Producer, IsOptimized);
  CAMLxparam5(Flags, RuntimeVer, SplitName, Kind, DWOId);
  CAMLxparam4(SplitDebugInline, DebugInfoForProfiling, SysRoot, SDK);
  CAMLreturn(to_val(LLVMDIBuilderCreateCompileUnit(
      DIBuilder_val(Builder), Int_val(Lang), Metadata_val(FileRef),
      String_val(Producer), caml_string_length(Producer), Bool_val(IsOptimized),
      String_val(Flags), caml_string_length(Flags), Int_val(RuntimeVer),
      String_val(SplitName), caml_string_length(SplitName), Int_val(Kind),
      Int_val(DWOId), Bool_val(SplitDebugInline),
      Bool_val(DebugInfoForProfiling), String_val(SysRoot),
      caml_string_length(SysRoot), String_val(SDK), caml_string_length(SDK))));
}

value llvm_dibuild_create_compile_unit_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_compile_unit_native(
      argv[0],                  // Builder
      argv[1],                  // Lang
      argv[2],                  // FileRef
      argv[3],                  // Producer
      argv[4],                  // IsOptimized
      argv[5],                  // Flags
      argv[6],                  // RuntimeVer
      argv[7],                  // SplitName
      argv[8],                  // Kind
      argv[9],                  // DWOId
      argv[10],                 // SplitDebugInline
      argv[11],                 // DebugInfoForProfiling
      argv[12],                 // SysRoot
      argv[13]                  // SDK
  );
}

value llvm_dibuild_create_file(value Builder, value Filename, value Directory) {
  CAMLparam3(Builder, Filename, Directory);
  CAMLreturn(to_val(LLVMDIBuilderCreateFile(
    DIBuilder_val(Builder),
    String_val(Filename),
    caml_string_length(Filename),
    String_val(Directory),
    caml_string_length(Directory))));
}

value
llvm_dibuild_create_module_native(value Builder, value ParentScope,
                                  value Name, value ConfigMacros,
                                  value IncludePath, value SysRoot) {
  CAMLparam5(Builder, ParentScope, Name, ConfigMacros, IncludePath);
  CAMLxparam1(SysRoot);
  CAMLreturn(to_val(LLVMDIBuilderCreateModule(
      DIBuilder_val(Builder), Metadata_val(ParentScope), String_val(Name),
      caml_string_length(Name), String_val(ConfigMacros),
      caml_string_length(ConfigMacros), String_val(IncludePath),
      caml_string_length(IncludePath), String_val(SysRoot),
      caml_string_length(SysRoot))));
}

value llvm_dibuild_create_module_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_module_native(
      argv[0],                  // Builder
      argv[1],                  // ParentScope
      argv[2],                  // Name
      argv[3],                  // ConfigMacros
      argv[4],                  // IncludePath
      argv[5]                   // SysRoot
  );
}

value llvm_dibuild_create_namespace(value Builder,
                                    value ParentScope,
                                    value Name, value ExportSymbols) {
  CAMLparam4(Builder, ParentScope, Name, ExportSymbols);
  CAMLreturn(to_val(LLVMDIBuilderCreateNameSpace(
      DIBuilder_val(Builder), Metadata_val(ParentScope), String_val(Name),
      caml_string_length(Name), Bool_val(ExportSymbols))));
}

value llvm_dibuild_create_function_native(
    value Builder, value Scope, value Name, value LinkageName,
    value File, value LineNo, value Ty, value IsLocalToUnit,
    value IsDefinition, value ScopeLine, value Flags, value IsOptimized) {
  CAMLreturn(to_val(LLVMDIBuilderCreateFunction(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), String_val(LinkageName),
      caml_string_length(LinkageName), Metadata_val(File), Int_val(LineNo),
      Metadata_val(Ty), Bool_val(IsLocalToUnit), Bool_val(IsDefinition),
      Int_val(ScopeLine), DIFlags_val(Flags), Bool_val(IsOptimized))));
}

value llvm_dibuild_create_function_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_function_native(argv[0], // Builder,
                                             argv[1], // Scope
                                             argv[2],                  // Name
                                             argv[3], // LinkageName
                                             argv[4], // File
                                             argv[5],                  // LineNo
                                             argv[6], // Ty
                                             argv[7],  // IsLocalUnit
                                             argv[8],  // IsDefinition
                                             argv[9],  // ScopeLine
                                             argv[10], // Flags
                                             argv[11]  // IsOptimized
  );
}

value llvm_dibuild_create_lexical_block(value Builder, value Scope, value File,
                                        value Line, value Column) {
  CAMLparam5(Builder, Scope, File, Line, Column);
  CAMLreturn(to_val(LLVMDIBuilderCreateLexicalBlock(
    DIBuilder_val(Builder), Metadata_val(Scope), Metadata_val(File),
    Int_val(Line), Int_val(Column))));
}

value llvm_metadata_null() { return to_val(NULL); }

value llvm_dibuild_create_debug_location(value Ctx, value Line, value Column,
                                         value Scope, value InlinedAt) {
  CAMLparam5(Ctx, Line, Column, Scope, InlinedAt);
  CAMLreturn(to_val(
    LLVMDIBuilderCreateDebugLocation(Context_val(Ctx), Int_val(Line),
                                     Int_val(Column), Metadata_val(Scope),
                                     Metadata_val(InlinedAt))));
}

value llvm_di_location_get_line(value Location) {
  CAMLParam1(Location);
  CAMLreturn(Val_int(LLVMDILocationGetLine(Metadata_val(Location))));
}

value llvm_di_location_get_column(value Location) {
  CAMLparam1(Location);
  CAMLreturn(Val_int(LLVMDILocationGetColumn(Metadata_val(Location))));
}

value llvm_di_location_get_scope(value Location) {
  CAMLparam1(Location);
  CAMLreturn(to_val(LLVMDILocationGetScope(Metadata_val(Location))));
}

value llvm_di_location_get_inlined_at(value Location) {
  CAMLparam1(Location);
  CAMLreturn(ptr_to_option(LLVMDILocationGetInlinedAt(Metadata_val(Location))));
}

value llvm_di_scope_get_file(value Scope) {
  CAMLparam1(Scope);
  CAMLreturn(ptr_to_option(LLVMDIScopeGetFile(Metadata_val(Scope))));
}

value llvm_di_file_get_directory(value File) {
  CAMLparam1(File);
  unsigned Len;
  const char *Directory = LLVMDIFileGetDirectory(Metadata_val(File), &Len);
  CAMLreturn(cstr_to_string(Directory, Len));
}

value llvm_di_file_get_filename(value File) {
  CAMLparam1(File);
  unsigned Len;
  const char *Filename = LLVMDIFileGetFilename(Metadata_val(File), &Len);
  CAMLreturn(cstr_to_string(Filename, Len));
}

value llvm_di_file_get_source(value File) {
  unsigned Len;
  const char *Source = LLVMDIFileGetSource(Metadata_val(File), &Len);
  return cstr_to_string(Source, Len);
}

value llvm_dibuild_get_or_create_type_array(value Builder, value Data) {
  CAMLparam2(Builder, Data);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Data);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = from_val(Field(Data, i));
  }
  CAMLreturn(to_val(LLVMDIBuilderGetOrCreateTypeArray(
    DIBuilder_val(Builder),
    (LLVMMetadataRef *)Op_val(Temp),
    Count)));
}

value llvm_dibuild_get_or_create_array(value Builder, value Data) {
  CAMLparam2(Builder, Data);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Data);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = from_val(Field(Data, i));
  }
  CAMLreturn(to_val(LLVMDIBuilderGetOrCreateArray(
    DIBuilder_val(Builder),
    (LLVMMetadataRef *)Op_val(Temp),
    Count)));
}

value llvm_dibuild_create_subroutine_type(value Builder, value File,
                                          value ParameterTypes, value Flags) {
  CAMLparam4(Builder, File, ParameterTypes, Flags);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(ParameterTypes);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = from_val(Field(ParameterTypes, i));
  }

  CAMLreturn(to_val(LLVMDIBuilderCreateSubroutineType(
      DIBuilder_val(Builder), Metadata_val(File),
      (LLVMMetadataRef *)Op_val(Temp),
      Wosize_val(ParameterTypes), DIFlags_val(Flags))));
}

value llvm_dibuild_create_enumerator(value Builder, value Name,
                                     value Value, value IsUnsigned) {
  CAMLparam4(Builder, Name, Value, IsUnsigned);
  CAMLreturn(to_val(LLVMDIBuilderCreateEnumerator(
      DIBuilder_val(Builder), String_val(Name), caml_string_length(Name),
      (int64_t)Int_val(Value), Bool_val(IsUnsigned))));
}

value llvm_dibuild_create_enumeration_type_native(
    value Builder, value Scope, value Name, value File,
    value LineNumber, value SizeInBits, value AlignInBits, value Elements,
    value ClassTy) {
  CAMLparam5(Builder, Scope, Name, File, LineNumber);
  CAMLxparam4(SizeInBits, AlignInBits, Elements, ClassTy);
  CAMLlocal1(Temp);
  unsigned int Count = Wosize_val(Elements);
  Temp = caml_alloc(Count, Abstract_tag);
  for (unsigned int i = 0; i < Count; ++i) {
    Field(Temp, i) = from_val(Field(Elements, i));
  }
  CAMLreturn(to_val(LLVMDIBuilderCreateEnumerationType(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNumber),
      (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits),
      (LLVMMetadataRef *)Op_val(Temp), Count, Metadata_val(ClassTy))));
}

value llvm_dibuild_create_enumeration_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_enumeration_type_native(
      argv[0], // Builder
      argv[1], // Scope
      argv[2], // Name
      argv[3], // File
      argv[4], // LineNumber
      argv[5], // SizeInBits
      argv[6], // AlignInBits
      argv[7], // Elements
      argv[8]  // ClassTy
  );
}

value llvm_dibuild_create_union_type_native(
    value Builder, value Scope, value Name, value File,
    value LineNumber, value SizeInBits, value AlignInBits, value Flags,
    value Elements, value RunTimeLanguage, value UniqueId) {
  CAMLparam5(Builder, Scope, Name, File, LineNumber);
  CAMLxparam5(SizeInBits, AlignInBits, Flags);
  CAMLxparam1(UniqueId);
  void* Temp = alloc_temp(Elements);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateUnionType(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNumber),
      (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits), DIFlags_val(Flags),
      (LLVMMetadataRef *)Temp, Wosize_val(Elements),
      Int_val(RunTimeLanguage), String_val(UniqueId),
      caml_string_length(UniqueId));
  free(Temp);
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_union_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_union_type_native(
      argv[0], // Builder
      argv[1], // Scope
      argv[2], // Name
      argv[3], // File
      argv[4], // LineNumber
      argv[5], // SizeInBits
      argv[6], // AlignInBits
      argv[7], // Flags
      argv[8], // Elements
      argv[9], // RunTimeLanguage
      argv[10] // UniqueId
  );
}

value llvm_dibuild_create_array_type(value Builder, value Size,
                                     value AlignInBits, value Ty,
                                     value Subscripts) {
  CAMLparam5(Builder, Size, AlignInBits, Ty, Subscripts);
  void* Temp = alloc_temp(Subscripts);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateArrayType(
      DIBuilder_val(Builder), (uint64_t)Int_val(Size), Int_val(AlignInBits), Ty,
      (LLVMMetadataRef *)Temp, Wosize_val(Subscripts));
  free(Temp);
  CAMLreturn(to_val(Metadata);
}

value llvm_dibuild_create_vector_type(value Builder, value Size,
                                      value AlignInBits, value Ty,
                                      value Subscripts) {
  CAMLparam5(Builder, Size, AlignInBits, Ty, Subscripts);
  void* Temp = alloc_temp(Subscripts);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateVectorType(
      DIBuilder_val(Builder), (uint64_t)Int_val(Size), Int_val(AlignInBits), Ty,
      (LLVMMetadataRef *)Temp, Wosize_val(Subscripts));
  free(Temp);
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_unspecified_type(value Builder, value Name) {
  CAMLparam2(Builder, Name);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateUnspecifiedType(
    DIBuilder_val(Builder), String_val(Name), caml_string_length(Name));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_basic_type(value Builder, value Name,
                                     value SizeInBits, value Encoding,
                                     value Flags) {
  CAMLparam5(Builder, Name, SizeInBits, Encoding, Flags);
  LLVMMetadtaRef Metadata = LLVMDIBuilderCreateBasicType(
      DIBuilder_val(Builder), String_val(Name), caml_string_length(Name),
      (uint64_t)Int_val(SizeInBits), Int_val(Encoding), DIFlags_val(Flags));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_pointer_type_native(
    value Builder, value PointeeTy, value SizeInBits,
    value AlignInBits, value AddressSpace, value Name) {
  CAMLparam5(Builder, PointeeTy, SizeInBits, AlignInBits, AddressSpace);
  CAMLxparam1(Name);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreatePointerType(
      DIBuilder_val(Builder), Metadata_val(PointeeTy),
      (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits),
      Int_val(AddressSpace), String_val(Name), caml_string_length(Name));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_pointer_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_pointer_type_native(
      argv[0], // Builder
      argv[1], // PointeeTy
      argv[2], // SizeInBits
      argv[3], // AlignInBits
      argv[4], // AddressSpace
      argv[5]  // Name
  );
}

value llvm_dibuild_create_struct_type_native(
    value Builder, value Scope, value Name, value File,
    value LineNumber, value SizeInBits, value AlignInBits, value Flags,
    value DerivedFrom, value Elements, value RunTimeLanguage,
    value VTableHolder, value UniqueId) {
  CAMLparam5(Builder, Scope, Name, File, LineNumber);
  CAMLxparam5(SizeInBits, AlignInBits, Flags, DerivedFrom, Elements);
  CAMLxparam3(RunTimeLanguage, VTableHolder, UniqueOd);
  void* Temp = alloc_temp(Elements);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateStructType(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNumber),
      (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits), DIFlags_val(Flags),
      Metadata_val(DerivedFrom), (LLVMMetadataRef *)Temp, Wosize_val(Elements),
      Int_val(RunTimeLanguage), Metadata_val(VTableHolder),
      String_val(UniqueId), caml_string_length(UniqueId));
  free(Temp);
  CAMLreturn(to_val(Temp));
}

value llvm_dibuild_create_struct_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_struct_type_native(
      argv[0],  // Builder
      argv[1],  // Scope
      argv[2],  // Name
      argv[3],  // File
      argv[4],  // LineNumber
      argv[5],  // SizeInBits
      argv[6],  // AlignInBits
      argv[7],  // Flags
      argv[8],  // DeriviedFrom
      argv[9],  // Elements
      argv[10], // RunTimeLanguage
      argv[11], // VTableHolder
      argv[12]  // UniqueId
  );
}

value llvm_dibuild_create_member_type_native(
    value Builder, LLVMMetadataRef Scope, value Name, LLVMMetadataRef File,
    value LineNumber, value SizeInBits, value AlignInBits, value OffsetInBits,
    value Flags, LLVMMetadataRef Ty) {
  CAMLparam5(Builder, Scope, Name, File, LineNumber);
  CAMLxparam5(SizeInBits, AlignInBits, OffsetInBits, Flags, Ty);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateMemberType(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNumber),
      (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits),
      (uint64_t)Int_val(OffsetInBits), DIFlags_val(Flags), Ty);
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_member_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_member_type_native(
      argv[0], // Builder
      argv[1], // Scope
      argv[2], // Name
      argv[3], // File
      argv[4], // LineNumber
      argv[5], // SizeInBits
      argv[6], // AlignInBits
      argv[7], // OffsetInBits
      argv[8], // Flags
      argv[9]  // Ty
  );
}

value llvm_dibuild_create_static_member_type_native(
    value Builder, value Scope, value Name, value File,
    value LineNumber, value Type, value Flags,
    value ConstantVal, value AlignInBits) {
  CAMLparam5(Builder, Scope, Name, File, LineNumber);
  CAMLxparam4(Type, Flags, ConstantVal, AlignInBits);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateStaticMemberType(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNumber),
      Metadata_val(Type), DIFlags_val(Flags), Value_val(ConstantVal),
      Int_val(AlignInBits));
  CAMLparam(to_val(Metadata));
}

value llvm_dibuild_create_static_member_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_static_member_type_native(
      argv[0], // Builder
      argv[1], // Scope
      argv[2], // Name
      argv[3], // File
      argv[4], // LineNumber
      argv[5], // Type
      argv[6], // Flags,
      argv[7], // ConstantVal
      argv[8]  // AlignInBits
  );
}

value llvm_dibuild_create_member_pointer_type_native(
    value Builder, value PointeeType, value ClassType, value SizeInBits,
    value AlignInBits, value Flags) {
  CAMLparam(Builder, PointeeType, ClassType, SizeInBits, AlignInBits);
  CAMLxparam(Flags);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateMemberPointerType(
      DIBuilder_val(Builder), Metadata_val(PointeeType),
      Metadata_val(ClassType), (uint64_t)Int_val(SizeInBits),
      Int_val(AlignInBits), llvm_diflags_get(Flags));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_member_pointer_type_bytecode(value *argv, int argn) {
  return llvm_dibuild_create_member_pointer_type_native(
      argv[0], // Builder
      argv[1], // PointeeType
      argv[2], // ClassType
      argv[3], // SizeInBits
      argv[4], // AlignInBits
      argv[5]  // Flags
  );
}

value llvm_dibuild_create_object_pointer_type(value Builder, value Type) {
  CAMLparam2(Builder, Type);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateObjectPointerType(
    DIBuilder_val(Builder), Metadata_val(Type)
  );
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_qualified_type(value Builder, value Tag, value Type) {
  CAMLparam3(Builder, Tag, Type);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateQualifiedType(
    DIBuilder_val(Builder), Int_val(Tag), Metadata_val(Type)
  );
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_reference_type(value Builder, value Tag, value Type) {
  CAMLparam3(Builder, Tag, Type);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateReferenceType(
    DIBuilder_val(Builder), Int_val(Tag), Metadata_val(Type)
  );
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_null_ptr_type(value Builder) {

  CAMLparam1(Builder);
  CAMLreturn(to_val(LLVMDIBuilderCreateNullPtrType(DIBuilder_val(Builder))));
}

value llvm_dibuild_create_typedef_native(
    value Builder, value Type, value Name, value File, value LineNo,
    value Scope, value AlignInBits) {

  CAMLparam5(Builder, Type, Name, File, LineNo);
  CAMLxparam2(Scope, AlignInBits);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateTypedef(
      DIBuilder_val(Builder), Metadata_val(Type), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(LineNo),
      Metadata_val(Scope), Int_val(AlignInBits));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_typedef_bytecode(value *argv, int argn) {

  return llvm_dibuild_create_typedef_native(argv[0], // Builder
                                            argv[1], // Type
                                            argv[2], // Name
                                            argv[3], // File
                                            argv[4], // LineNo
                                            argv[5], // Scope
                                            argv[6]  // AlignInBits
  );
}

value
llvm_dibuild_create_inheritance_native(value Builder, value Ty,
                                       value BaseTy, value BaseOffset,
                                       value VBPtrOffset, value Flags) {
  CAMLparam5(Builder, Ty, BaseTy, BaseOffset, VBPtrOffset);
  CAMLxparam1(Flags);
  LLVMMetadataRef Metadata =
    LLVMDIBuilderCreateInheritance(DIBuilder_val(Builder), Metadata_val(Ty),
                                   Metadata_val(BaseTy),
                                   (uint64_t)Int_val(BaseOffset),
                                   Int_val(VBPtrOffset), DIFlags_val(Flags));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_inheritance_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_inheritance_native(
      argv[0], // Builder
      argv[1], // Ty
      argv[2], // BaseTy
      argv[3], // BaseOffset
      argv[4], // VBPtrOffset
      argv[5]  // Flags
  );
}

value llvm_dibuild_create_forward_decl_native(
    value Builder, value Tag, value Name, value Scope,
    value File, value Line, value RuntimeLang, value SizeInBits,
    value AlignInBits, value UniqueIdentifier) {
  CAMLparam5(Builder, Tag, Name, Scope, File);
  CAMLxparam5(Line, RuntimeLang, SizeInBits, AlignInBits, UniqueIdentifier);
  LLVMMetadataRef Metadata = LLVMDIBuilderCreateForwardDecl(
      DIBuilder_val(Builder), Int_val(Tag), String_val(Name),
      caml_string_length(Name), Metadata_val(Scope), Metadata_val(File),
      Int_val(Line), Int_val(RuntimeLang), (uint64_t)Int_val(SizeInBits),
      Int_val(AlignInBits), String_val(UniqueIdentifier),
      caml_string_length(UniqueIdentifier));
  CAMLreturn(to_val(Metadata));
}

value llvm_dibuild_create_forward_decl_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_forward_decl_native(
      argv[0], // Builder
      argv[1], // Tag
      argv[2], // Name
      argv[3], // Scope
      argv[4], // File
      argv[5], // Line
      argv[6], // RuntimeLang
      argv[7], // SizeInBits
      argv[8], // AlignInBits
      argv[9]  // UniqueIdentifier
  );
}

LLVMMetadataRef llvm_dibuild_create_replaceable_composite_type_native(
    value Builder, value Tag, value Name, LLVMMetadataRef Scope,
    LLVMMetadataRef File, value Line, value RuntimeLang, value SizeInBits,
    value AlignInBits, value Flags, value UniqueIdentifier) {

  return LLVMDIBuilderCreateReplaceableCompositeType(
      DIBuilder_val(Builder), Int_val(Tag), String_val(Name),
      caml_string_length(Name), Scope, File, Int_val(Line),
      Int_val(RuntimeLang), (uint64_t)Int_val(SizeInBits), Int_val(AlignInBits),
      DIFlags_val(Flags), String_val(UniqueIdentifier),
      caml_string_length(UniqueIdentifier));
}

LLVMMetadataRef
llvm_dibuild_create_replaceable_composite_type_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_replaceable_composite_type_native(
      argv[0],                  // Builder
      argv[1],                  // Tag
      argv[2],                  // Name
      (LLVMMetadataRef)argv[3], // Scope
      (LLVMMetadataRef)argv[4], // File
      argv[5],                  // Line
      argv[6],                  // RuntimeLang
      argv[7],                  // SizeInBits
      argv[8],                  // AlignInBits
      argv[9],                  // Flags
      argv[10]                  // UniqueIdentifier
  );
}

LLVMMetadataRef llvm_dibuild_create_bit_field_member_type_native(
    value Builder, LLVMMetadataRef Scope, value Name, LLVMMetadataRef File,
    value LineNum, value SizeInBits, value OffsetInBits,
    value StorageOffsetInBits, value Flags, LLVMMetadataRef Ty) {

  return LLVMDIBuilderCreateBitFieldMemberType(
      DIBuilder_val(Builder), Scope, String_val(Name), caml_string_length(Name),
      File, Int_val(LineNum), (uint64_t)Int_val(SizeInBits),
      (uint64_t)Int_val(OffsetInBits), (uint64_t)Int_val(StorageOffsetInBits),
      DIFlags_val(Flags), Ty);
}

LLVMMetadataRef llvm_dibuild_create_bit_field_member_type_bytecode(value *argv,
                                                                   int arg) {

  return llvm_dibuild_create_bit_field_member_type_native(
      argv[0],                  // Builder
      (LLVMMetadataRef)argv[1], // Scope
      argv[2],                  // Name
      (LLVMMetadataRef)argv[3], // File
      argv[4],                  // LineNum
      argv[5],                  // SizeInBits
      argv[6],                  // OffsetInBits
      argv[7],                  // StorageOffsetInBits
      argv[8],                  // Flags
      (LLVMMetadataRef)argv[9]  // Ty
  );
}

LLVMMetadataRef llvm_dibuild_create_class_type_native(
    value Builder, LLVMMetadataRef Scope, value Name, LLVMMetadataRef File,
    value LineNumber, value SizeInBits, value AlignInBits, value OffsetInBits,
    value Flags, LLVMMetadataRef DerivedFrom, value Elements,
    LLVMMetadataRef VTableHolder, LLVMMetadataRef TemplateParamsNode,
    value UniqueIdentifier) {

  return LLVMDIBuilderCreateClassType(
      DIBuilder_val(Builder), Scope, String_val(Name), caml_string_length(Name),
      File, Int_val(LineNumber), (uint64_t)Int_val(SizeInBits),
      Int_val(AlignInBits), (uint64_t)Int_val(OffsetInBits), DIFlags_val(Flags),
      DerivedFrom, (LLVMMetadataRef *)Op_val(Elements), Wosize_val(Elements),
      VTableHolder, TemplateParamsNode, String_val(UniqueIdentifier),
      caml_string_length(UniqueIdentifier));
}

LLVMMetadataRef llvm_dibuild_create_class_type_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_class_type_native(
      argv[0],                   // Builder
      (LLVMMetadataRef)argv[1],  // Scope
      argv[2],                   // Name
      (LLVMMetadataRef)argv[3],  // File
      argv[4],                   // LineNumber
      argv[5],                   // SizeInBits
      argv[6],                   // AlignInBits
      argv[7],                   // OffsetInBits
      argv[8],                   // Flags
      (LLVMMetadataRef)argv[9],  // DerivedFrom
      argv[10],                  // Elements
      (LLVMMetadataRef)argv[11], // VTableHolder
      (LLVMMetadataRef)argv[12], // TemplateParamsNode
      argv[13]                   // UniqueIdentifier
  );
}

LLVMMetadataRef llvm_dibuild_create_artificial_type(value Builder,
                                                    LLVMMetadataRef Type) {
  return LLVMDIBuilderCreateArtificialType(DIBuilder_val(Builder), Type);
}

value llvm_di_type_get_name(LLVMMetadataRef DType) {
  size_t Len;
  const char *Name = LLVMDITypeGetName(DType, &Len);
  return cstr_to_string(Name, Len);
}

value llvm_di_type_get_size_in_bits(LLVMMetadataRef DType) {
  uint64_t Size = LLVMDITypeGetSizeInBits(DType);
  return Val_int((int)Size);
}

value llvm_di_type_get_offset_in_bits(LLVMMetadataRef DType) {
  uint64_t Size = LLVMDITypeGetOffsetInBits(DType);
  return Val_int((int)Size);
}

value llvm_di_type_get_align_in_bits(LLVMMetadataRef DType) {
  uint32_t Size = LLVMDITypeGetAlignInBits(DType);
  return Val_int(Size);
}

value llvm_di_type_get_line(LLVMMetadataRef DType) {
  unsigned Line = LLVMDITypeGetLine(DType);
  return Val_int(Line);
}

value llvm_di_type_get_flags(LLVMMetadataRef DType) {
  LLVMDIFlags Flags = LLVMDITypeGetLine(DType);
  return alloc_diflags(Flags);
}

value llvm_get_subprogram(LLVMValueRef Func) {
  return (ptr_to_option(LLVMGetSubprogram(Func)));
}

value llvm_set_subprogram(LLVMValueRef Func, LLVMMetadataRef SP) {
  LLVMSetSubprogram(Func, SP);
  return Val_unit;
}

value llvm_di_subprogram_get_line(LLVMMetadataRef Subprogram) {
  return Val_int(LLVMDISubprogramGetLine(Subprogram));
}

value llvm_instr_get_debug_loc(LLVMValueRef Inst) {
  return (ptr_to_option(LLVMInstructionGetDebugLoc(Inst)));
}

value llvm_instr_set_debug_loc(LLVMValueRef Inst, LLVMMetadataRef Loc) {
  LLVMInstructionSetDebugLoc(Inst, Loc);
  return Val_unit;
}

LLVMMetadataRef llvm_dibuild_create_constant_value_expression(value Builder,
                                                              value Value) {
  return LLVMDIBuilderCreateConstantValueExpression(DIBuilder_val(Builder),
                                                    (uint64_t)Int_val(Value));
}

LLVMMetadataRef llvm_dibuild_create_global_variable_expression_native(
    value Builder, LLVMMetadataRef Scope, value Name, value Linkage,
    LLVMMetadataRef File, value Line, LLVMMetadataRef Ty, value LocalToUnit,
    LLVMMetadataRef Expr, LLVMMetadataRef Decl, value AlignInBits) {
  return LLVMDIBuilderCreateGlobalVariableExpression(
      DIBuilder_val(Builder), Scope, String_val(Name), caml_string_length(Name),
      String_val(Linkage), caml_string_length(Linkage), File, Int_val(Line), Ty,
      Bool_val(LocalToUnit), Expr, Decl, Int_val(AlignInBits));
}

LLVMMetadataRef
llvm_dibuild_create_global_variable_expression_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_global_variable_expression_native(
      argv[0],                  // Builder
      (LLVMMetadataRef)argv[1], // Scope
      argv[2],                  // Name
      argv[3],                  // Linkage
      (LLVMMetadataRef)argv[4], // File
      argv[5],                  // Line
      (LLVMMetadataRef)argv[6], // Ty
      argv[7],                  // LocalToUnit
      (LLVMMetadataRef)argv[8], // Expr
      (LLVMMetadataRef)argv[9], // Decl
      argv[10]                  // AlignInBits
  );
}

value llvm_di_global_variable_expression_get_variable(LLVMMetadataRef GVE) {
  return (ptr_to_option(LLVMDIGlobalVariableExpressionGetVariable(GVE)));
}

value llvm_di_variable_get_line(LLVMMetadataRef Variable) {
  return Val_int(LLVMDIVariableGetLine(Variable));
}

value llvm_di_variable_get_file(LLVMMetadataRef Variable) {
  return (ptr_to_option(LLVMDIVariableGetFile(Variable)));
}

value llvm_get_metadata_kind(LLVMMetadataRef Metadata) {
  return Val_int(LLVMGetMetadataKind(Metadata));
}

value llvm_dibuild_create_auto_variable_native(
    value Builder, value Scope, value Name, value File,
    value Line, value Ty, value AlwaysPreserve, value Flags,
    value AlignInBits) {
  CAMLparam5(Builder, Scope, Name, File, Line);
  CAMLxparam4(Ty, AlwaysPreserve, Flags, AlignInBits);
  CAMLreturn(to_val(LLVMDIBuilderCreateAutoVariable(
      DIBuilder_val(Builder), Metadata_val(Scope), String_val(Name),
      caml_string_length(Name), Metadata_val(File), Int_val(Line),
      Metadata_val(Ty), Bool_val(AlwaysPreserve), DIFlags_val(Flags),
      Int_val(AlignInBits)));
}

value llvm_dibuild_create_auto_variable_bytecode(value *argv, int arg) {

  return llvm_dibuild_create_auto_variable_native(
      argv[0], // Builder
      argv[1], // Scope
      argv[2], // Name
      argv[3], // File
      argv[4], // Line
      argv[5], // Ty
      argv[6], // AlwaysPreserve
      argv[7], // Flags
      argv[8]  // AlignInBits
  );
}

LLVMMetadataRef llvm_dibuild_create_parameter_variable_native(
    value Builder, LLVMMetadataRef Scope, value Name, unsigned ArgNo,
    LLVMMetadataRef File, value Line, LLVMMetadataRef Ty, value AlwaysPreserve,
    value Flags) {
  return LLVMDIBuilderCreateParameterVariable(
      DIBuilder_val(Builder), Scope, String_val(Name), caml_string_length(Name),
      ArgNo, File, Int_val(Line), Ty, Bool_val(AlwaysPreserve),
      DIFlags_val(Flags));
}

LLVMMetadataRef llvm_dibuild_create_parameter_variable_bytecode(value *argv,
                                                                int arg) {

  return llvm_dibuild_create_parameter_variable_native(
      argv[0],                  // Builder
      (LLVMMetadataRef)argv[1], // Scope
      argv[2],                  // Name
      argv[3],                  // ArgNo
      (LLVMMetadataRef)argv[4], // File
      argv[5],                  // Line
      (LLVMMetadataRef)argv[6], // Ty
      argv[7],                  // AlwaysPreserve
      argv[8]                   // Flags
  );
}

LLVMValueRef llvm_dibuild_insert_declare_before_native(
    value Builder, LLVMValueRef Storage, LLVMMetadataRef VarInfo,
    LLVMMetadataRef Expr, LLVMMetadataRef DebugLoc, LLVMValueRef Instr) {
  return LLVMDIBuilderInsertDeclareBefore(DIBuilder_val(Builder), Storage,
                                          VarInfo, Expr, DebugLoc, Instr);
}

LLVMValueRef llvm_dibuild_insert_declare_before_bytecode(value *argv, int arg) {

  return llvm_dibuild_insert_declare_before_native(
      argv[0],                  // Builder
      (LLVMValueRef)argv[1],    // Storage
      (LLVMMetadataRef)argv[2], // VarInfo
      (LLVMMetadataRef)argv[3], // Expr
      (LLVMMetadataRef)argv[4], // DebugLoc
      (LLVMValueRef)argv[5]     // Instr
  );
}

LLVMValueRef llvm_dibuild_insert_declare_at_end_native(
    value Builder, LLVMValueRef Storage, LLVMMetadataRef VarInfo,
    LLVMMetadataRef Expr, LLVMMetadataRef DebugLoc, LLVMBasicBlockRef Block) {
  return LLVMDIBuilderInsertDeclareAtEnd(DIBuilder_val(Builder), Storage,
                                         VarInfo, Expr, DebugLoc, Block);
}

LLVMValueRef llvm_dibuild_insert_declare_at_end_bytecode(value *argv, int arg) {

  return llvm_dibuild_insert_declare_at_end_native(
      argv[0],                   // Builder
      (LLVMValueRef)argv[1],     // Storage
      (LLVMMetadataRef)argv[2],  // VarInfo
      (LLVMMetadataRef)argv[3],  // Expr
      (LLVMMetadataRef)argv[4],  // DebugLoc
      (LLVMBasicBlockRef)argv[5] // Block
  );
}

LLVMMetadataRef llvm_dibuild_expression(value Builder, value Addr) {
  return LLVMDIBuilderCreateExpression(
      DIBuilder_val(Builder), (uint64_t *)Op_val(Addr), Wosize_val(Addr));
}
