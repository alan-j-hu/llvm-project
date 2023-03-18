add_ocaml_library(llvm_passmgr_builder
  OCAML    llvm_passmgr_builder
  OCAMLDEP llvm
  C        passmgr_builder_ocaml
  CFLAGS   "-I${CMAKE_CURRENT_SOURCE_DIR}/../../llvm"
  LLVM     ipo)
