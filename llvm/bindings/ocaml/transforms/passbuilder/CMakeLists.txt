add_ocaml_library(llvm_passbuilder
  OCAML    llvm_passbuilder
  OCAMLDEP llvm
  C        passbuilder_ocaml
  LLVM     Passes)
