add_ocaml_library(llvm_error
  OCAML    llvm_error
  OCAMLDEP llvm
  C        error_ocaml
  CFLAGS   "-I${CMAKE_CURRENT_SOURCE_DIR} -I${CMAKE_CURRENT_SOURCE_DIR}/../llvm"
  LLVM     Support)
