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

open Rocq_tools.Extra
open Rocq_tools.Code_quality

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

module W = struct
  include Warning
  let pp : Format.formatter -> t -> unit =
    fun fmt {full; _} ->
    Format.fprintf fmt "%s" full
end
module E = struct
  include Error
  let pp : Format.formatter -> t -> unit =
    fun fmt {full; _} ->
    Format.fprintf fmt "%s" full
end


module WS = struct
  include Set.Make(W)
  let pp pp_w fmt ws =
    iter (fun w -> pp_w fmt w) ws
end
module ES = struct
  include Set.Make(E)
  let pp pp_w fmt ws =
    iter (fun w -> pp_w fmt w) ws
end

module Analysis = struct
  type t = {
    e_appeared : ES.t;
    e_disappeared : ES.t;
    w_appeared : WS.t;
    w_disappeared : WS.t;
  }
end

module Markdown = struct
  let output fmt (a : Analysis.t) =
    let Analysis.{e_appeared; e_disappeared; w_appeared; w_disappeared} = a in

    if WS.is_empty w_appeared &&
       WS.is_empty w_disappeared &&
       ES.is_empty e_appeared &&
       ES.is_empty e_disappeared
    then begin
      Format.fprintf fmt "# No Changes in Warnings or Errors\n%!";
    end
    else begin
      let header fmt symbol title num =
        Format.fprintf fmt "# %s %s (%i)\n" symbol title num;
      in
      let code_block pp_content fmt content =
        Format.fprintf fmt "```\n%a\n```\n" pp_content content
      in
      if not @@ ES.is_empty e_appeared then begin
        header fmt ":x:" "New Errors" (ES.cardinal e_appeared);
        Format.fprintf fmt "\n%a\n" (code_block @@ ES.pp E.pp) e_appeared;
      end;

      if not @@ WS.is_empty w_appeared then begin
        header fmt ":warning:" "New Warnings" (WS.cardinal w_appeared);
        Format.fprintf fmt "%a\n" (code_block @@ WS.pp W.pp) w_appeared;
      end;

      if not @@ ES.is_empty e_disappeared then begin
        header fmt ":negative_squared_cross_mark:" "Fixed Errors" (ES.cardinal e_disappeared);
        Format.fprintf fmt "\n%a\n" (code_block @@ ES.pp E.pp) e_disappeared;
      end;
      if not @@ WS.is_empty w_disappeared then begin
        header fmt ":green_heart:" "Fixed Warnings" (WS.cardinal w_disappeared);
        Format.fprintf fmt "\n%a\n" (code_block @@ WS.pp W.pp) w_disappeared;
      end
    end
end

let analyse fmt file1 file2 =
  let file1 = open_in file1 in
  let file2 = open_in file2 in
  let (_, warnings1, errors1) = parse_lines (get_lines file1 parse_line) in
  let (_, warnings2, errors2) = parse_lines (get_lines file2 parse_line) in

  (* Format.efprintf fmt "size of warnings1 = %i\n" (List.length warnings1);  *)
  (* Format.efprintf fmt "size of warnings2 = %i\n" (List.length warnings2);  *)
  (* Format.efprintf fmt "size of errors1 = %i\n" (List.length errors1);  *)
  (* Format.efprintf fmt "size of errors2 = %i\n" (List.length errors2);  *)

  let w1 = WS.of_list warnings1 in
  let w2 = WS.of_list warnings2 in

  (* let w_both = WS.union w1 w2 in *)
  let w_appeared = WS.diff w2 w1 in
  let w_disappeared = WS.diff w1 w2 in

  let e1 = ES.of_list errors1 in
  let e2 = ES.of_list errors2 in

  (* let e_both = ES.union e1 e2 in *)
  let e_appeared = ES.diff e2 e1 in
  let e_disappeared = ES.diff e1 e2 in

  Markdown.output fmt {e_appeared; e_disappeared; w_appeared; w_disappeared}


let einfo : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (fmt ^^ "%!")

let usage : string -> bool -> 'a = fun prog_name error ->
  if error then panic "Usage: %s code_quality_report_ref.json code_quality_report.json" prog_name;
  einfo "Usage: %s code_quality_report_ref.json code_quality_report.json\n" prog_name;
  exit 0

let main () =
  let (prog_name, args) =
    let args = List.tl (Array.to_list Sys.argv) in
    (Sys.argv.(0), args)
  in
  let rec parse_args files args =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    match args with
    | ("--help" | "-h")             :: _                     ->
        usage prog_name false
    | arg                           :: _ when is_flag arg    ->
        panic "Invalid command line argument \"%s\"." arg;
    | file                          :: args                  ->
        if try Sys.is_directory file with Sys_error(_) -> false then
          panic "File expected, [%s] is a directory." file;
        if not (Sys.file_exists file) then
          panic "No such file or directory [%s]." file;
        parse_args (file :: files) args
    | []                                                     ->
        List.rev files

  in
  let files = parse_args [] args in
  match files with
  | [file1; file2] -> analyse (Format.formatter_of_out_channel stdout) file1 file2
  | _                          ->
      let n = List.length files in
      panic "at least 2 file paths expected on the command line (%i given)." n

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
