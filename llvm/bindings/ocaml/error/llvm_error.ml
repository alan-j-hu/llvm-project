(*===-- llvm_error.ml - LLVM OCaml Interface -------------------*- OCaml -*-===*
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===----------------------------------------------------------------------===*)

type llerror

external create_string_error : string -> llerror = "llvm_create_string_error"
external get_error_message : llerror -> string = "llvm_get_error_message"
