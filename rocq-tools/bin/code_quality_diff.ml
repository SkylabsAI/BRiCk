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
    Format.fprintf fmt "%s\n" full
end
module E = struct
  include Error
  let pp : Format.formatter -> t -> unit =
    fun fmt {full; _} ->
    Format.fprintf fmt "%s\n" full
end


module WS = struct
  include Set.Make(W)
  let pp pp_w fmt ws =
    iter (fun w -> Format.fprintf fmt "%a" pp_w w) ws
end
module ES = struct
  include Set.Make(E)
  let pp pp_w fmt ws =
    iter (fun w -> Format.fprintf fmt "%a" pp_w w) ws
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
        Format.fprintf fmt "```\n%a```\n" pp_content content
      in
      if not @@ ES.is_empty e_appeared then begin
        header fmt ":x:" "New Errors" (ES.cardinal e_appeared);
        Format.fprintf fmt "\n%a\n" (ES.pp @@ code_block E.pp) e_appeared;
      end;

      if not @@ WS.is_empty w_appeared then begin
        header fmt ":warning:" "New Warnings" (WS.cardinal w_appeared);
        Format.fprintf fmt "\n%a\n" (WS.pp @@ code_block W.pp) w_appeared;
      end;

      if not @@ ES.is_empty e_disappeared then begin
        header fmt ":negative_squared_cross_mark:" "Fixed Errors" (ES.cardinal e_disappeared);
        Format.fprintf fmt "\n%a\n" (ES.pp @@ code_block E.pp) e_disappeared;
      end;
      if not @@ WS.is_empty w_disappeared then begin
        header fmt ":green_heart:" "Fixed Warnings" (WS.cardinal w_disappeared);
        Format.fprintf fmt "\n%a\n" (WS.pp @@ code_block W.pp) w_disappeared;
      end
    end
end

type glob_out = {
  src_file : string;
  std_out : string list;
  std_err : string list;
}

let ensure_file file =
  if try Sys.is_directory file with Sys_error(_) -> false then
    panic "File expected, [%s] is a directory." file;
  if not (Sys.file_exists file) then
    panic "No such file or directory [%s]." file

let to_glob_out : strip_prefix:string -> string -> glob_out option =
  let re = Str.regexp {|\.glob\.\(stdout\|stderr\)$|} in
  fun ~strip_prefix filename ->
  let is_std_out = String.ends_with ~suffix:".glob.stdout" filename in
  let is_std_err = String.ends_with ~suffix:".glob.stderr" filename in
  if not (is_std_out || is_std_err) then begin
    Printf.eprintf "%s is neither a .glob.stdout nor a .glob.stderr file" filename;
    None
  end
  else begin
    let src_file = Str.replace_first re ".v" filename in
    let src_file = if String.starts_with ~prefix:strip_prefix src_file then
        let n = String.length strip_prefix in
        String.sub src_file n (String.length src_file - n)
      else
        src_file
    in
    let std_out =
      if is_std_out then begin
        ensure_file filename;
        get_lines (open_in filename) (fun x -> x)
      end
      else
        []
    in
    let std_err =
      if is_std_err then begin
        ensure_file filename;
        get_lines (open_in filename) (fun x -> x)
      end
      else
        []
    in
    Some { src_file; std_out; std_err }
  end

type dune_out = {
  src_file : string;
  output : string list;      (* dune does not dinstinguish stderr and stdout. *)
}

let to_dune_out : fname:string -> dune_out list =
  let re = Str.regexp {|\bcoqc.* \([^ ]+\.v\))$|} in
  fun ~fname ->
  let open Yojson.Basic in
  let json = from_file ~fname fname in
  let list = Util.to_list json in
  let list = List.map Util.to_assoc list in
  let list =
    let f a =
      (Util.to_string @@ List.assoc "command" a,
      List.map Util.to_string @@ Util.to_list @@ List.assoc "output" a)
    in
    List.map f list in
  let list =
    let f (cmd, out) =
      let found =
        try
          let _ = Str.search_forward re cmd 0 in
          true
        with Not_found -> false
      in
      if not found then None else begin
        let src_file = Str.matched_group 1 cmd in
        let output = List.filter (fun x -> x <> "") out in
        Some { src_file; output }
      end
    in
    List.filter_map f list
  in
  list

let analyse fmt ~before_dune ~after_dune ~before_globs ~after_globs =

  let nonempty_stdout_warning src_file output =
    let text = Format.sprintf "File \"%s\", line 0, characters 0-0:\nWarning: Non-empty stdout when building using coqc:\n%s\n[non-empty-stdout,dummy]" src_file output in
    W.{ file = src_file; pos = None; name = "non-empty-stdout,dummy"; text; full = text }
  in
  let dangling_output_warning src_file output =
    let text = Format.sprintf "File \"%s\", line 0, characters 0-0:\nWarning: Dangling output when building using coqc:\n%s\n[dangling-output-stdout,dummy]" src_file output in
    W.{ file = src_file; pos = None; name = "dangling-output,dummy"; text; full = text }
  in

  let parse globs dunes =
    let glob (ws, es) {src_file; std_err; std_out} =
      let (dangling_lines, w,e) = parse_lines (List.map parse_line std_err) in
      let dangling = List.map (fun (_, txt) -> dangling_output_warning src_file txt) dangling_lines in
      let w =
        if std_out = [] then w else begin
          nonempty_stdout_warning src_file (String.concat "\n" std_out) :: w
        end
      in
      (List.rev_append w @@ List.rev_append dangling ws, List.rev_append e es)
    in

    let dune (ws, es) {src_file; output} =
      let (dangling_lines, w, e) = parse_lines (List.map parse_line output) in
      let dangling = List.map (fun (_, txt) -> dangling_output_warning src_file txt) dangling_lines in
      (List.rev_append w @@ List.rev_append dangling ws, List.rev_append e es)
    in

    List.fold_left glob ([], []) globs |> fun res ->
    List.fold_left dune res dunes
  in

  let (warnings1, errors1) = parse before_globs before_dune in
  let (warnings2, errors2) = parse after_globs after_dune in

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

module Args = struct
  type t = {
    before_globs: glob_out list;
    before_dune : dune_out list;
    after_globs : glob_out list;
    after_dune : dune_out list;
  }
  let empty = {
    before_globs = [];
    after_globs = [];
    before_dune = [];
    after_dune = [];
  }
end
open Args

let usage : ?error:bool -> string -> 'a = fun ?(error=false) prog_name ->
  if error then panic "Usage: %s [--before-globs-from-file file-with-glob-files ..] [--after-globs-from-file file-with-glob-files ..] [--before-dune dune-log.json ..] [--after-dune dune-log.json ..]" prog_name;
  einfo "Usage: %s [--before-globs-from-file file-with-glob-files ..] [--after-globs-from-file file-with-glob-files ..] [--before-dune dune-log.json ..] [--after-dune dune-log.json ..]" prog_name;
  exit 0

let main () =
  let (prog_name, args) =
    let args = List.tl (Array.to_list Sys.argv) in
    (Sys.argv.(0), args)
  in
  let rec parse_args state args =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    match args with
    | ("--help" | "-h")             :: _                     ->
        usage prog_name
    | "--before-globs-from-file" :: file  :: args            ->
        ensure_file file;
        let strip_prefix = Filename.dirname file ^ "/" in
        let new_before_globs = List.filter_map (fun x -> x) @@ get_lines (open_in file) (to_glob_out ~strip_prefix) in
        let before_globs = List.rev_append new_before_globs state.before_globs in
        parse_args {state with before_globs} args
    | "--after-globs-from-file" :: file   :: args            ->
        ensure_file file;
        let strip_prefix = Filename.dirname file ^ "/" in
        let new_after_globs = List.filter_map (fun x -> x) @@ get_lines (open_in file) (to_glob_out ~strip_prefix) in
        let after_globs = List.rev_append new_after_globs state.after_globs in
        parse_args {state with after_globs} args
    | "--before-dune" :: file       :: args                  ->
        ensure_file file;
        let new_before_dune = to_dune_out ~fname:file in
        let before_dune = List.rev_append new_before_dune state.before_dune in
        parse_args {state with before_dune} args
    | "--after-dune" :: file       :: args                  ->
        ensure_file file;
        let new_after_dune = to_dune_out ~fname:file in
        let after_dune = List.rev_append new_after_dune state.after_dune in
        parse_args {state with after_dune} args
    | arg                           :: _ when is_flag arg    ->
        panic "Invalid command line argument \"%s\"." arg;
    | _ :: _ ->
        usage ~error:true prog_name
    | []                                                     ->
        state

  in
  let {before_dune; after_dune; before_globs; after_globs} = parse_args empty args in
  analyse (Format.formatter_of_out_channel stdout) ~before_dune ~after_dune ~before_globs ~after_globs

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
