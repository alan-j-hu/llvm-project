(* RUN: rm -rf %t && mkdir -p %t && cp %s %t/passbuilder.ml
 * RUN: %ocamlc -g -w +A -package llvm.passbuilder -package llvm.all_backends -linkpkg %t/passbuilder.ml -o %t/executable
 * RUN: %t/executable
 * RUN: %ocamlopt -g -w +A -package llvm.passbuilder -package llvm.all_backends -linkpkg %t/passbuilder.ml -o %t/executable
 * RUN: %t/executable
 * XFAIL: vg_leak
 *)

let () = Llvm_all_backends.initialize ()

(*===-- Fixture -----------------------------------------------------------===*)

let context = Llvm.global_context ()

let m = Llvm.create_module context "mymodule"

let target =
  Llvm_target.Target.by_triple (Llvm_target.Target.default_triple ())

let machine =
  Llvm_target.TargetMachine.create
    ~triple:(Llvm_target.Target.default_triple ()) target

let options = Llvm_passbuilder.create_passbuilder_options ()

(*===-- PassBuilder -------------------------------------------------------===*)

let () =
  match Llvm_passbuilder.run_passes m "no-op-module" machine options with
  | Error _ -> assert false
  | Ok () -> ()

let () =
  Llvm_passbuilder.dispose_passbuilder_options options;
  Llvm.dispose_module m
