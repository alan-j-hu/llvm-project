(* RUN: rm -rf %t && mkdir -p %t && cp %s %t/error.ml
 * RUN: %ocamlc -g -w +A -package llvm.error -linkpkg %t/error.ml -o %t/executable
 * RUN: %t/executable
 * RUN: %ocamlopt -g -w +A -package llvm.error -linkpkg %t/error.ml -o %t/executable
 * RUN: %t/executable
 * XFAIL: vg_leak
 *)

let error1 = Llvm_error.create_string_error "message1"
let error2 = Llvm_error.create_string_error "message2"

let () =
  assert ("message1" = Llvm_error.get_error_message error1);
  assert ("message2" = Llvm_error.get_error_message error2)
