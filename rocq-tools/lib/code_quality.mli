(*
 * Copyright (C) 2023-2025 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

type pos = {
  line : int; (* Line number.  *)
  c0   : int; (* Start column. *)
  c1   : int; (* End column.   *)
}

type warning = {
  w_file : string;     (* File where the warning originated.     *)
  w_pos  : pos option; (* Optional warning position in the file. *)
  w_name : string;     (* Name for the warning.                  *)
  w_text : string;     (* Text from the warning.                 *)
  w_full : string;     (* Original content including headers     *)
}

type error = {
  e_file : string;
  e_pos  : pos option;
  e_text : string;
  e_full : string;
}

val get_lines : In_channel.t -> (string -> 'a) -> 'a list

type line =
  | Header of { file : string; pos: pos option; full: string (* full line *) }
  | Data of string * bool (* Is this the last warning line? *)

val parse_line : string -> line
val parse_lines : line list -> (int * string) list * warning list * error list
