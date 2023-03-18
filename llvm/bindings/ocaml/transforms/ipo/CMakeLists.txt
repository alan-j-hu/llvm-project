add_ocaml_library(llvm_ipo
  OCAML    llvm_ipo
  OCAMLDEP llvm
  C        ipo_ocaml
  CFLAGS   "-I${CMAKE_CURRENT_SOURCE_DIR}/../../llvm"
  LLVM     ipo)
