(*===-- llvm_error.mli - LLVM OCaml Interface ------------------*- OCaml -*-===*
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===----------------------------------------------------------------------===*)

type llerror

(** Creates a StringError. *)
val create_string_error : string -> llerror

(** Returns the error message. This operation consumes the error, which is not
    usable once this call returns. *)
val get_error_message : llerror -> string
