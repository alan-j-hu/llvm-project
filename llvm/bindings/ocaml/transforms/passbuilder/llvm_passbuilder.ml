(*===-- llvm_passbuilder.ml - LLVM OCaml Interface -------------*- OCaml -*-===*
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===----------------------------------------------------------------------===*)

type llpassbuilder_options

external create_passbuilder_options : unit -> llpassbuilder_options =
  "llvm_create_passbuilder_options"

external dispose_passbuilder_options : llpassbuilder_options -> unit =
  "llvm_dispose_passbuilder_options"

external run_passes
  : Llvm.llmodule
  -> string
  -> Llvm_target.TargetMachine.t
  -> llpassbuilder_options
  -> (unit, Llvm_error.llerror) result
  = "llvm_run_passes"
