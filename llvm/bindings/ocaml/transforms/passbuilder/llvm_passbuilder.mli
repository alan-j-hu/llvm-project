(*===-- llvm_passbuilder.mli - LLVM OCaml Interface ------------*- OCaml -*-===*
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===----------------------------------------------------------------------===*)

type llpassbuilder_options

(** [run_passes m passes tm opts] runs a set of passes over a module. The
    format of the string [passes] is the same as opt's -passes argument for
    the new pass manager. Individual passes may be specified, separated by
    commas. Full pipelines may also be invoked. *)
val run_passes
  : Llvm.llmodule
  -> string
  -> Llvm_target.TargetMachine.t
  -> llpassbuilder_options
  -> (unit, Llvm_error.llerror) result

(** Creates a new set of options for a PassBuilder. *)
val create_passbuilder_options : unit -> llpassbuilder_options

(** Toggles adding the VerifierPass for the PassBuilder. *)
val set_verify_each : llpassbuilder_options -> bool -> unit

(** Toggles debug logging. *)
val set_debug_logging : llpassbuilder_options -> bool -> unit

(** Disposes of the options. *)
val dispose_passbuilder_options : llpassbuilder_options -> unit
