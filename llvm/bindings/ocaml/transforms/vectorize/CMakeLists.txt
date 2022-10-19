add_ocaml_library(llvm_vectorize
  OCAML    llvm_vectorize
  OCAMLDEP llvm
  C        vectorize_ocaml
  CFLAGS   "-I${CMAKE_CURRENT_SOURCE_DIR}/../../llvm"
  LLVM     Vectorize)
