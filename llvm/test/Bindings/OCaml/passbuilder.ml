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
  Llvm_passbuilder.passbuilder_options_set_verify_each options true;
  Llvm_passbuilder.passbuilder_options_set_debug_logging options true;
  Llvm_passbuilder.passbuilder_options_set_loop_interleaving options true;
  Llvm_passbuilder.passbuilder_options_set_loop_vectorization options true;
  Llvm_passbuilder.passbuilder_options_set_slp_vectorization options true;
  Llvm_passbuilder.passbuilder_options_set_loop_unrolling options true;
  Llvm_passbuilder.passbuilder_options_set_forget_all_scev_in_loop_unroll
    options true;
  Llvm_passbuilder.passbuilder_options_set_licm_mssa_opt_cap options 2;
  Llvm_passbuilder.passbuilder_options_set_licm_mssa_no_acc_for_promotion_cap
    options 2;
  Llvm_passbuilder.passbuilder_options_set_call_graph_profile options true;
  Llvm_passbuilder.passbuilder_options_set_merge_functions options true;
  Llvm_passbuilder.passbuilder_options_set_inliner_threshold options 2;
  match Llvm_passbuilder.run_passes m "no-op-module" machine options with
  | Error _ -> assert false
  | Ok () -> ()

let () =
  Llvm_passbuilder.dispose_passbuilder_options options;
  Llvm.dispose_module m
