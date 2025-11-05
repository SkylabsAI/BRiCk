(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
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

open Rocq_tools.Extra

type pos = {
  line : int; (* Line number.  *)
  c0   : int; (* Start column. *)
  c1   : int; (* End column.   *)
}

let dummy_pos : pos = {line = 0; c0 = -1; c1 = -1}

type warning = {
  w_file : string;     (* File where the warning originated.     *)
  w_pos  : pos option; (* Optional warning position in the file. *)
  w_name : string;     (* Name for the warning.                  *)
  w_text : string;     (* Text from the warning.                 *)
}

type error = {
  e_file : string;
  e_pos  : pos option;
  e_text : string;
}

let get_lines : In_channel.t -> (string -> 'a) -> 'a list = fun ic f ->
  let rec loop rev_lines =
    match In_channel.input_line ic with
    | None -> List.rev rev_lines
    | Some(line) -> loop (f line :: rev_lines)
  in
  loop []

type line =
  | Header of string * pos option
  | Data of string * bool (* Is this the last warning line? *)

let normalize_path : string -> string = fun path ->
  if String.starts_with ~prefix:"./" path then
    String.sub path 2 (String.length path - 2)
  else
    path

let parse_line : string -> line = fun line ->
  try
    Scanf.sscanf line "File %S, line %i, characters %i-%i:" @@
      fun w_file line c0 c1 ->
    let w_file = normalize_path w_file in
    let w_pos = if line = 0 then None else Some({line; c0; c1}) in
    Header(w_file, w_pos)
  with
  | End_of_file
  | Scanf.Scan_failure(_) ->
    let last_warning_line =
      let re = "^.*[[][^ ]+[]]$" in
      Str.string_match (Str.regexp re) line 0
    in
    Data(line, last_warning_line)

type item =
  | Warning of warning
  | Error of error
  | Line of int * string

let make_warning : string -> pos option -> string -> warning =
    fun w_file w_pos data ->
  let (w_name, w_text) =
    if not (String.starts_with ~prefix:"Warning:" data) then
      panic "Invalid warning (no leading  \"Warning:\").";
    let len = String.length data in
    let ibracket = String.rindex_from data (len - 1) '[' in
    let tags = String.sub data (ibracket + 1) (len - ibracket - 2) in
    let tags = String.split_on_char ',' tags in
    let text = String.sub data 9 (len - 8 - (len - ibracket) - 2) in
    (List.hd tags, String.trim text)
  in
  {w_file; w_pos; w_name; w_text}

let make_error : string -> pos option -> string -> error =
    fun e_file e_pos e_text ->
  {e_file; e_pos; e_text}

type kind =
  | E (* Error *)
  | W (* Warning *)
  | U (* Unknown *)

let kind_of_prefix : string -> kind =
  fun data ->
  let data = String.trim data in
  if String.starts_with ~prefix:"Error:" data then E
  else if String.starts_with ~prefix:"Warning:" data then W
  else U                        (* TODO: panic? *)

let make_item : kind -> string -> pos option -> string list -> item =
  fun kind file pos data ->
  let data = String.trim (String.concat "\n" data) in
  match kind with
  | E -> Error (make_error file pos data)
  | W -> Warning (make_warning file pos data)
  | U -> assert false

let gather : line list -> item list = fun lines ->
  let rec gather i rev_items header lines =
    let gather = gather (i+1) in
    match (header, lines) with
    | (None                 , []                        ) ->
        List.rev rev_items
    | (Some(W, _, _, _), []                     ) ->
      panic "Unexpected end of warning at line %i." i
    | (Some(_, _, _, []), []                     ) ->
      panic "File and position header without content after it in line %i." i
    | (Some(U, _, _, _ :: _), _                     ) ->
      panic "Unknown output in line %i." i
    | (Some(E, file, pos, data), []                     ) ->
      let item = make_item E file pos (List.rev data) in
      gather (item :: rev_items) None lines
    | (None                 , Header(file, pos) :: lines) ->
        gather rev_items (Some(U, file, pos, [])) lines
    | (None                 , Data(line, false) :: lines) ->
        gather (Line(i, line) :: rev_items) header lines
    | (None                 , Data(_   , true ) :: _    ) ->
        panic "Dangling output at line %i." i
    | (Some(U, file, pos, []), Data(line, is_last_warning_line) :: lines) ->
        let kind = kind_of_prefix line in
        if kind = W && is_last_warning_line then
          let item = make_item W file pos [line] in
          gather (item :: rev_items) None lines
        else
          gather rev_items (Some(kind, file, pos, [line])) lines
    | (Some(E as kind, file, pos, data), Data(line, _) :: lines) ->
        gather rev_items (Some(kind, file, pos, line :: data)) lines
    | (Some(E, file, pos, data), Header(h_file, h_pos) :: lines) ->
      let item = make_item E file pos (List.rev data) in
      gather (item :: rev_items) (Some(U, h_file, h_pos, [])) lines
    | (Some(W as kind, file, pos, data), Data(line, false) :: lines) ->
        gather rev_items (Some(kind, file, pos, line :: data)) lines
    | (Some(W, file, pos, data), Data(line, true ) :: lines) ->
        let item = make_item W file pos (List.rev (line :: data)) in
        gather (item :: rev_items) None lines
    | (Some((W | U), _, _, _),      Header(_   , _  ) :: _    ) ->
        panic "Nested warning at line %i." i
  in
  gather 1 [] None lines

let main () =
  let items = gather (get_lines stdin parse_line) in
  let (lines, warnings, errors) =
    let f item (lines, warnings, errors) =
      match item with
      | Line(i, line) -> ((i, line) :: lines, warnings, errors)
      | Error(e)      -> (lines, warnings, e :: errors)
      | Warning(w)    -> (lines, w :: warnings, errors)
    in
    List.fold_right f items ([], [], [])
  in
  let warn_line (i, line) =
    Printf.eprintf "Warning: dangling input line.\n% 5i | %s\n%!" i line
  in
  List.iter warn_line lines;
  let to_json file pos text (kind : [`Error|`Warning of string])  =
    let name =
      match kind with
      | `Error -> "error"
      | `Warning name -> "warning:" ^ name
    in
    let fingerprint =
      let data =
        let pos = match pos with Some(pos) -> pos | None -> dummy_pos in
        Printf.sprintf "%s,%i,%i,%i,%s,%s"
          file pos.line pos.c0 pos.c1 name text
      in
      Digest.to_hex (Digest.string data)
    in
    let pos =
      let pos = match pos with Some(pos) -> pos | None -> dummy_pos in
      let line = ("line", `Int(pos.line)) in
      let b = `Assoc([line; ("column", `Int(pos.c0))]) in 
      let e = `Assoc([line; ("column", `Int(pos.c1))]) in 
      `Assoc([("begin", b); ("end", e)])
    in
    let location = [("path", `String(file)); ("positions", pos)] in
    let severity =
      match kind with
      | `Error -> "critical"
      | `Warning _ -> "minor"
    in
    let fields =
      ("description", `String(text)       ) ::
      ("check_name" , `String(name)       ) ::
      ("fingerprint", `String(fingerprint)) ::
      ("severity"   , `String(severity)   ) ::
      ("location"   , `Assoc(location)    ) :: []
    in
    `Assoc(fields)
  in
  let error_to_json e =  to_json e.e_file e.e_pos e.e_text (`Error) in
  let warning_to_json w = to_json w.w_file w.w_pos w.w_text (`Warning(w.w_name)) in
  let json = `List(List.map error_to_json errors @ List.map warning_to_json warnings) in
  Printf.printf "%a\n%!" (Yojson.Basic.pretty_to_channel ~std:true) json

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
