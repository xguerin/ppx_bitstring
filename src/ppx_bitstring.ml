(*
 * Copyright (c) 2016 Xavier R. Guérin <copyright@applepine.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Ast_helper
open Ast_mapper
open Asttypes
open Core.Std
open Format
open Lexing
open Longident
open Parsetree
open Printf

(* Type definition *)

module Type = struct
  type t =
    | Int
    | String
    | Bitstring
end

module Sign = struct
  type t =
    | Signed
    | Unsigned
  let to_string = function
    | Signed -> "signed"
    | Unsigned -> "unsigned"
end

module Endian = struct
  type t =
    | Little
    | Big
    | Native
    | Referred of Parsetree.expression
  let to_string = function
    | Little -> "le"
    | Big -> "be"
    | Native -> "ne"
    | Referred _ -> "ee"
end

module Qualifiers = struct
  type t = {
    value_type      : Type.t option;
    sign            : Sign.t option;
    endian          : Endian.t option;
    check           : Parsetree.expression option;
    bind            : Parsetree.expression option;
    map             : Parsetree.expression option;
    save_offset_to  : Parsetree.expression option;
  }
  let empty = {
    value_type      = None;
    sign            = None;
    endian          = None;
    check           = None;
    bind            = None;
    map             = None;
    save_offset_to  = None;
  }
  let default = {
    value_type      = Some Type.Int;
    sign            = Some Sign.Unsigned;
    endian          = Some Endian.Big;
    check           = None;
    bind            = None;
    map             = None;
    save_offset_to  = None;
  }
  let set_defaults v =
    let chk_value q =
      if q.value_type = None then { q with value_type = Some Type.Int }
      else q
    and chk_sign q =
      if q.sign = None then { q with sign = Some Sign.Unsigned }
      else q
    and chk_endian q =
      if q.endian = None then { q with endian = Some Endian.Big }
      else q
    in
    v |> chk_value |> chk_sign |> chk_endian
end

(* Helper functions *)

let mksym =
  let i = ref 1000 in
  fun name ->
    incr i; let i = !i in
    sprintf "__ppxbitstring_%s_%d" name i

let mkpatvar name =
  Ast_convenience.pvar name

let mkident name =
  Ast_convenience.evar name

let rec process_loc ~loc expr =
  match expr with
  | { pexp_desc = Pexp_tuple(ops) } ->
    let fld = List.fold
        ~init:[]
        ~f:(fun acc exp -> acc @ [ process_loc ~loc exp ]) ops
    in { expr with pexp_desc = Pexp_tuple(fld); pexp_loc = loc }
  | { pexp_desc = Pexp_apply(ident, ops) } ->
    let fld = List.fold
        ~init:[]
        ~f:(fun acc (lbl, exp) -> acc @ [ (lbl, (process_loc ~loc exp)) ]) ops
    in { expr with pexp_desc = Pexp_apply(ident, fld); pexp_loc = loc }
  | _ -> { expr with pexp_loc = loc }

let parse_expr expr =
  process_loc ~loc:expr.loc (Parse.expression (Lexing.from_string expr.txt))

let parse_pattern pat =
  { (Parse.pattern (Lexing.from_string pat.txt)) with ppat_loc = pat.loc }

(* Location parser and splitter *)

let find_loc_boundaries ~loc last rem =
  let open Location in
  let { loc_start; loc_end; loc_ghost } = loc in
  let xtr_lines = List.length rem in
  let xtr_char = List.fold_left ~init:xtr_lines ~f:(+) rem in
  let ne = { loc_start with
             pos_lnum = loc_start.pos_lnum + xtr_lines;
             pos_bol  = loc_start.pos_bol + xtr_char;
             pos_cnum = loc_start.pos_cnum + xtr_char + last
           }
  and ns = if xtr_lines = 0
    then { loc_start with
           pos_cnum = loc_start.pos_cnum + xtr_char + last + 1
         }
    else { loc_start with
           pos_lnum = loc_start.pos_lnum + xtr_lines;
           pos_bol  = loc_start.pos_bol + xtr_char;
           pos_cnum = loc_start.pos_cnum + xtr_char
         } in
  let tloc = { loc_start; loc_end = ne; loc_ghost } in
  let nloc = { loc_start = ns; loc_end; loc_ghost } in
  (tloc, nloc)

let rec split_loc_rec ~loc = function
  | [] -> []
  | hd :: tl ->
    let line_list = String.split ~on:'\n' hd
                    |> List.rev
                    |> List.map ~f:String.length in
    begin
      match line_list with
      | [] -> []
      | last::rem ->
        let (tloc, nloc) = find_loc_boundaries ~loc last rem in
        [ tloc ] @ (split_loc_rec ~loc:nloc tl)
    end

let split_loc ~loc lst =
  split_loc_rec ~loc lst
  |> List.map2_exn lst ~f:(fun e loc -> Location.mkloc (StdLabels.Bytes.trim e) loc)

(* Exception *)

let location_exn ~loc msg =
  raise (Location.Error (Location.error ~loc msg))

(* Processing qualifiers *)

let check_map_functor sub =
  match sub with
  | [%expr (fun [%p? _] -> [%e? _])]  -> Some (sub)
  | _                                 -> None

let process_qual state qual =
  let open Qualifiers in
  let loc = qual.pexp_loc in
  match qual with
  | [%expr int] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.Int }
    end
  | [%expr string] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.String }
    end
  | [%expr bitstring] ->
    begin match state.value_type with
      | Some v -> location_exn ~loc "Value type redefined"
      | None -> { state with value_type = Some Type.Bitstring }
    end
  | [%expr signed] ->
    begin match state.sign with
      | Some v -> location_exn ~loc "Signedness redefined"
      | None -> { state with sign = Some Sign.Signed }
    end
  | [%expr unsigned] ->
    begin match state.sign with
      | Some v -> location_exn ~loc "Signedness redefined"
      | None -> { state with sign = Some Sign.Unsigned }
    end
  | [%expr littleendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Little }
    end
  | [%expr bigendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Big }
    end
  | [%expr nativeendian] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some Endian.Native }
    end
  | [%expr endian [%e? sub]] ->
    begin match state.endian with
      | Some v -> location_exn ~loc "Endianness redefined"
      | None -> { state with endian = Some (Endian.Referred sub) }
    end
  | [%expr bind [%e? sub]] ->
    begin match state.bind, state.map with
      | Some b, None   -> location_exn ~loc "Bind expression redefined"
      | None,   Some m -> location_exn ~loc "Map expression already defined"
      | Some b, Some m -> location_exn ~loc "Inconsistent internal state"
      | None,   None   -> { state with bind = Some sub }
    end
  | [%expr map [%e? sub]] ->
    begin match state.bind, state.map with
      | Some b, None   -> location_exn ~loc "Bind expression already defined"
      | None,   Some m -> location_exn ~loc "Map expression redefined"
      | Some b, Some m -> location_exn ~loc "Inconsistent internal state"
      | None,   None   -> begin
          match check_map_functor sub with
          | Some sub  -> { state with map = Some sub }
          | None      -> location_exn ~loc "Invalid map functor"
        end
    end
  | [%expr check [%e? sub]] ->
    begin match state.check with
      | Some v -> location_exn ~loc "Check expression redefined"
      | None -> { state with check = Some sub }
    end
  | [%expr save_offset_to [%e? sub]] ->
    begin match state.save_offset_to with
      | Some v -> location_exn ~loc "Offset expression redefined"
      | None -> { state with save_offset_to = Some sub }
    end
  | _ ->
    let sexp = Pprintast.string_of_expression qual in
    raise (location_exn ~loc ("Invalid qualifier: " ^ sexp))

let parse_quals quals =
  let expr = parse_expr quals in
  let rec process_quals state = function
    | [] -> state
    | hd :: tl -> process_quals (process_qual state hd) tl
  in match expr with
  (* single named qualifiers *)
  | { pexp_desc = Pexp_ident (_) } ->
    process_qual Qualifiers.empty expr
  (* single functional qualifiers *)
  | { pexp_desc = Pexp_apply (_, _) } ->
    process_qual Qualifiers.empty expr
  (* multiple qualifiers *)
  | { pexp_desc = Pexp_tuple (e) } ->
    process_quals Qualifiers.empty e
  (* Unrecognized expression *)
  | expr ->
    let expr_str = Pprintast.string_of_expression expr in
    location_exn ~loc:expr.pexp_loc ("Invalid qualifiers list: " ^ expr_str)

(* Processing expression *)

let rec evaluate_expr = function
  | [%expr [%e? lhs] + [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l + r)
      | _ -> None
    end
  | [%expr [%e? lhs] - [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l - r)
      | _ -> None
    end
  | [%expr [%e? lhs] * [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l * r)
      | _ -> None
    end
  | [%expr [%e? lhs] / [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l / r)
      | _ -> None
    end
  | [%expr [%e? lhs] land [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l land r)
      | _ -> None
    end
  | [%expr [%e? lhs] lor [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lor r)
      | _ -> None
    end
  | [%expr [%e? lhs] lxor [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lxor r)
      | _ -> None
    end
  | [%expr [%e? lhs] lsr [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l lsr r)
      | _ -> None
    end
  | [%expr [%e? lhs] asr [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l asr r)
      | _ -> None
    end
  | [%expr [%e? lhs] mod [%e? rhs]] ->
    begin match evaluate_expr lhs, evaluate_expr rhs with
      | Some l, Some r -> Some (l mod r)
      | _ -> None
    end
  | { pexp_desc = Pexp_constant (const) } ->
    begin match const with
      | Pconst_integer(i, _) -> Some (int_of_string i)
      | _ -> None
    end
  | _ -> None

(* Parsing fields *)

let parse_match_fields str =
  String.split ~on:':' str.txt
  |> split_loc ~loc:str.loc
  |> function
  | [ { txt = "_" ; loc } as pat ] ->
    (parse_pattern pat, None, None)
  | [ pat; len ] ->
    let q = Some Qualifiers.default in
    (parse_pattern pat, Some (parse_expr len), q)
  | [ pat; len; quals ] ->
    let q = Some (Qualifiers.set_defaults (parse_quals quals)) in
    (parse_pattern pat, Some (parse_expr len), q)
  | [ stmt ] ->
    let pat_str = StdLabels.Bytes.to_string stmt.txt in
    location_exn ~loc:stmt.loc ("Invalid statement: '" ^ pat_str ^ "'")
  | _ ->
    location_exn ~loc:str.loc "Invalid number of fields in statement"

let parse_const_fields str =
  let open Qualifiers in
  String.split ~on:':' str.txt
  |> split_loc ~loc:str.loc
  |> function
  | [ vl; len ] ->
    (parse_expr vl, Some (parse_expr len), Some Qualifiers.default)
  | [ vl; len; quals ] ->
    let q = Qualifiers.set_defaults (parse_quals quals) in
    begin match q.bind, q.map, q.check, q.save_offset_to with
      | Some _, _, _, _ ->
        location_exn ~loc:str.loc "Bind meaningless in constructor"
      | _, Some _, _, _ ->
          location_exn ~loc:str.loc "Map meaningless in constructor"
      | _, _, Some _, _ ->
          location_exn ~loc:str.loc "Check meaningless in constructor"
      | _, _, _, Some _ ->
        location_exn ~loc:str.loc "Saving offset  meaningless in constructor"
      | None, None, None, None ->
        (parse_expr vl, Some (parse_expr len), Some (q))
    end
  | [ stmt ] ->
    let pat_str = StdLabels.Bytes.to_string stmt.txt in
    location_exn ~loc:stmt.loc ("Invalid statement: '" ^ pat_str ^ "'")
  | _ ->
    location_exn ~loc:str.loc "Invalid number of fields in statement"

(* Match generators *)

let check_field_len ~loc (l, q) =
  let open Option.Monad_infix in
  match q.Qualifiers.value_type with
  | Some (Type.String) ->
    evaluate_expr l >>= fun v ->
    if v < -1 || (v > 0 && (v mod 8) <> 0) then
      location_exn ~loc "length of string must be > 0 and multiple of 8, or the special value -1"
    else Some v
  | Some (Type.Bitstring) ->
    evaluate_expr l >>= fun v ->
    if v < -1 then location_exn ~loc "length of bitstring must be >= 0 or the special value -1"
    else Some v
  | Some (Type.Int) ->
    evaluate_expr l >>= fun v ->
    if v < 1 || v > 64 then location_exn ~loc "length of int field must be [1..64]"
    else Some v
  | None -> location_exn ~loc "No type to check"

let get_inttype ~loc = function
  | v when v > 8  && v <= 16 -> "int"
  | v when v > 16 && v <= 32 -> "int32"
  | v when v > 32 && v <= 64 -> "int64"
  | _ -> location_exn ~loc "Invalid integer size"

let gen_extractor (dat, off, len) (l, q) loc =
  let open Qualifiers in
  match q.value_type with
  | Some (Type.Bitstring) -> begin
      match (evaluate_expr l) with
      | Some (-1) ->
          [%expr ([%e (mkident dat)], [%e (mkident off)], [%e (mkident len)])]
      | Some (_) | None ->
          [%expr ([%e (mkident dat)], [%e (mkident off)], [%e l])]
    end
  | Some (Type.String) ->
    [%expr (Bitstring.string_of_bitstring ([%e (mkident dat)],
                                           [%e (mkident off)], [%e l]))]
  | Some (Type.Int) ->
    begin match (evaluate_expr l), q.sign, q.endian with
      (* 1-bit type *)
      | Some (size), Some (_), Some (_) when size = 1 ->
        [%expr Bitstring.extract_bit
            [%e (mkident dat)] [%e (mkident off)] [%e (mkident len)] [%e l]]
      (* 8-bit type *)
      | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
        let ex = sprintf "Bitstring.extract_char_%s" (Sign.to_string sign) in
        let op = sprintf "%s %s %s %s %d" ex dat off len size in
        parse_expr (Location.mkloc op loc)
      (* 16|32|64-bit type *)
      | Some (size), Some (sign), Some (Endian.Referred r) ->
        let ss = Sign.to_string sign and it = get_inttype ~loc size in
        let ex = sprintf "Bitstring.extract_%s_ee_%s" it ss in
        let ee = Pprintast.string_of_expression r in
        let op = sprintf "%s (%s) %s %s %s %d" ex ee dat off len size in
        parse_expr (Location.mkloc op loc)
      | Some (size), Some (sign), Some (endian) ->
        let tp = get_inttype ~loc size in
        let en = Endian.to_string endian in
        let sn = Sign.to_string sign in
        let ex = sprintf "Bitstring.extract_%s_%s_%s" tp en sn in
        let op = sprintf "%s %s %s %s %d" ex dat off len size in
        parse_expr (Location.mkloc op loc)
      (* Variable size *)
      | None, Some (sign), Some (Endian.Referred r) ->
        let ss = Sign.to_string sign in
        let ex = sprintf "Bitstring.extract_int64_ee_%s" ss in
        let ee = Pprintast.string_of_expression r in
        let ln = Pprintast.string_of_expression l in
        let op = sprintf "%s (%s) %s %s %s (%s)" ex ee dat off len ln in
        parse_expr (Location.mkloc op loc)
      | None, Some (sign), Some (endian) ->
        let es = Endian.to_string endian and ss = Sign.to_string sign in
        let ex = sprintf "Bitstring.extract_int64_%s_%s" es ss in
        let ln = Pprintast.string_of_expression l in
        let op = sprintf "%s %s %s %s (%s)" ex dat off len ln in
        parse_expr (Location.mkloc op loc)
      (* Invalid type *)
      | _, _, _ ->
        raise (location_exn ~loc "Invalid type")
    end
  | _ -> raise (location_exn ~loc "Invalid type")

let gen_value (dat, off, len) (l, q) loc =
  let open Qualifiers in
  match q.bind, q.map  with
  | Some b, None    -> b
  | None,   Some m  -> [%expr [%e m] [%e (gen_extractor (dat, off, len) (l, q) loc)]]
  | _,      _       -> gen_extractor (dat, off, len) (l, q) loc

let rec gen_next org_off ~loc (dat, off, len) (p, l, q) beh fields =
  match (evaluate_expr l) with
  | Some (-1) ->
    [%expr let [%p (mkpatvar off)] = [%e (mkident off)] + [%e (mkident len)]
      and [%p (mkpatvar len)] = 0 in
      [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]
  | Some (_) | None ->
    [%expr let [%p (mkpatvar off)] = [%e (mkident off)] + [%e l]
      and [%p (mkpatvar len)] = [%e (mkident len)] - [%e l] in
      [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]

and gen_next_all ~loc org_off (dat, off, len) beh fields =
  [%expr let [%p (mkpatvar off)] = [%e (mkident off)] + [%e (mkident len)]
    and [%p (mkpatvar len)] = 0 in
    [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]

and gen_match org_off (dat, off, len) (p, l, q) loc beh fields =
  let open Qualifiers in
  let valN = mksym "value" in
  let m = match q.check with
    | Some chk ->
      [%expr begin match [%e (mkident valN)] with
             | [%p p] when [%e chk] ->
               [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]
             | _ -> () end]
    | None ->
      [%expr begin match [%e (mkident valN)] with
             | [%p p] when true ->
               [%e (gen_fields ~loc org_off (dat, off, len) beh fields)]
             | _ -> () end]
  in
  [%expr let [%p (mkpatvar valN)] = [%e (gen_value (dat, off, len) (l, q) loc)] in
         let [%p (mkpatvar off)] = [%e (mkident off)] + [%e l]
         and [%p (mkpatvar len)] = [%e (mkident len)] - [%e l] in [%e m]]

and gen_offset_saver org_off (dat, off, len) (p, l, q) loc beh =
  let open Qualifiers in
  match q.save_offset_to with
  | Some { pexp_desc = Pexp_ident ({ txt; _ }) } -> [%expr
    let [%p (mkpatvar (Longident.last txt))] =
      [%e (mkident off)] - [%e (mkident org_off)] in [%e beh]]
  | Some _ | None -> beh

and gen_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh fields =
  let open Qualifiers in
  match check_field_len ~loc (l, q), q.value_type with
  | Some (-1), Some (Type.Bitstring | Type.String) ->
    begin match p with
      | { ppat_desc = Ppat_var(_) } ->
        gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          let [%p p] = [%e (gen_value (dat, off, len) (l, q) loc)] in
          [%e (gen_next_all ~loc org_off (dat, off, len) beh fields)]]
      | [%pat? _ ] ->
        gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          [%e (gen_next_all org_off ~loc (dat, off, len) beh fields)]]
      | _ ->
        location_exn ~loc "Unbound string or bitstring can only be assigned to a variable or skipped"
    end
  | (Some (_) | None), Some (Type.Bitstring) ->
    begin match p with
      | { ppat_desc = Ppat_var(_) } ->
        gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          if [%e (mkident len)] >= [%e l] then
            let [%p p] = [%e (gen_value (dat, off, len) (l, q) loc)] in
            [%e (gen_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
          else ()]
      | [%pat? _ ] ->
        gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          if [%e (mkident len)] >= [%e l] then
            [%e (gen_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
          else ()]
      | _ -> location_exn ~loc "Bound bitstring can only be assigned to variables or skipped"
    end
  | (Some (_) | None), Some (Type.String) ->
    gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e (mkident len)] >= [%e l] then
        [%e (gen_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
  | Some (_), Some (Type.Int) ->
    gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e (mkident len)] >= [%e l] then
        [%e (gen_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
  | None, Some (Type.Int) ->
    gen_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e l] >= 1 && [%e l] <= 64 && [%e (mkident len)] >= [%e l] then
        [%e (gen_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
  | _, _ -> location_exn ~loc "No type to generate"

and gen_fields ~loc org_off (dat, off, len) beh fields =
  let open Qualifiers in
  match fields with
  | [] -> beh
  | (p, None, None) :: tl -> beh
  | (p, Some l, Some q) :: tl ->
    gen_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh tl
  | _ -> location_exn ~loc "Wrong pattern type in bitmatch case"

let gen_case ~mapper org_off res (dat, off, len) case =
  let loc = case.pc_lhs.ppat_loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_constant (Pconst_string (value, _)) ->
    let rhs = mapper.Ast_mapper.expr mapper case.pc_rhs in
    let beh = [%expr [%e (mkident res)] := Some ([%e rhs]); raise Exit] in
    String.split ~on:';' value
    |> split_loc ~loc
    |> List.map ~f:(fun e -> parse_match_fields e)
    |> gen_fields ~loc org_off (dat, off, len) beh
  | _ ->
    location_exn ~loc "Wrong pattern type"

let gen_cases ~mapper ident loc cases =
  let open Location in
  let datN = mksym "data" in
  let offNN = mksym "off" and lenNN = mksym "len" in
  let offN = mksym "off" and lenN = mksym "len" in
  let algN = mksym "aligned" and resN = mksym "result" in
  let stmts = List.fold
      ~init:[]
      ~f:(fun acc case -> acc @ [ gen_case ~mapper offN resN (datN, offNN, lenNN) case ])
      cases
  in
  let rec build_seq = function
    | [] -> location_exn ~loc "Empty case list"
    | [hd] -> hd
    | hd :: tl -> Exp.sequence hd (build_seq tl)
  in
  let seq = build_seq stmts in
  let tuple = [%pat? ([%p (mkpatvar datN)],
                      [%p (mkpatvar offN)],
                      [%p (mkpatvar lenN)])] in
  let fname = Exp.constant ~loc (Pconst_string (loc.loc_start.pos_fname, None)) in
  let lpos = Exp.constant ~loc (Pconst_integer (string_of_int loc.loc_start.pos_lnum, None)) in
  let cpos = Exp.constant ~loc (Pconst_integer (string_of_int loc.loc_start.pos_cnum, None)) in
  [%expr
    let [%p tuple] = [%e ident] in
    let [%p (mkpatvar offNN)] = [%e (mkident offN)]
    and [%p (mkpatvar lenNN)] = [%e (mkident lenN)]
    in
    let [%p (mkpatvar algN)] = ([%e (mkident offN)] land 7) = 0 in
    let [%p (mkpatvar resN)] = ref None in
    (try [%e seq]; with | Exit -> ());
    match ![%e (mkident resN)] with
    | Some x -> x
    | None -> raise (Match_failure ([%e fname], [%e lpos], [%e cpos]))]

(* constructor expressions *)

let gen_constructor loc sym = function
  | (l, Some (s), Some(q)) ->
    let open Location in
    let open Qualifiers in
    let exc = Ast_convenience.constr "Bitstring.Construct_failure"
        [ Ast_convenience.str "Bad field value";
          Ast_convenience.str "None";
          Ast_convenience.int loc.loc_start.pos_lnum;
          Ast_convenience.int loc.loc_start.pos_cnum ] in begin
      match q.value_type with
      | Some (Type.Bitstring) ->
        let ex = "Bitstring.construct_bitstring" in
        Ast_convenience.app (Ast_convenience.evar ex)
          [ (Ast_convenience.evar sym); l ]
      | Some (Type.String) ->
        let ex = "Bitstring.construct_string" in
        Ast_convenience.app (Ast_convenience.evar ex)
          [ (Ast_convenience.evar sym); l ]
      | Some (Type.Int) -> begin
          match (evaluate_expr s), q.sign, q.endian with
          (* 1-bit type *)
          | Some (size), Some (_), Some (_) when size = 1 -> begin
              let ex = "Bitstring.construct_bit" in
              let vl = match (evaluate_expr l) with
                | Some (1)        -> Ast_convenience.constr "true" []
                | Some (0)        -> Ast_convenience.constr "false" []
                | Some (_) | None -> l
              in Ast_convenience.app (Ast_convenience.evar ex)
                [ (Ast_convenience.evar sym); vl; (Ast_convenience.int 1); exc ]
            end
          (* 8-bit type *)
          | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
            let sn = Sign.to_string sign in
            let ex = sprintf "Bitstring.construct_char_%s" sn in
            Ast_convenience.app (Ast_convenience.evar ex)
              [ (Ast_convenience.evar sym); l; (Ast_convenience.int size); exc ]
          (* 16|32|64-bit type *)
          | Some (size), Some (sign), Some (Endian.Referred r) ->
            let ss = Sign.to_string sign and it = get_inttype ~loc size in
            let ex = sprintf "Bitstring.construct_%s_ee_%s" it ss in
            Ast_convenience.app (Ast_convenience.evar ex)
              [ r; (Ast_convenience.evar sym); l; (Ast_convenience.int size); exc ]
          | Some (size), Some (sign), Some (endian) ->
            let tp = get_inttype ~loc size in
            let en = Endian.to_string endian in
            let sn = Sign.to_string sign in
            let ex = sprintf "Bitstring.construct_%s_%s_%s" tp en sn in
            Ast_convenience.app (Ast_convenience.evar ex)
              [ (Ast_convenience.evar sym); l; (Ast_convenience.int size); exc ]
          (* Invalid type *)
          | _, _, _ ->
            raise (location_exn ~loc "Invalid type")
        end
      | _ -> raise (location_exn ~loc "Invalid type")
    end
  | _ -> raise (location_exn ~loc "Invalid field format")

let gen_assignment_size_of_field loc = function
  | (_, None, _) -> [%expr 0]
  | (f, Some (s), q) -> begin
      match (evaluate_expr s), Option.bind q (fun q -> q.Qualifiers.value_type) with
      | Some (v), Some (Type.String) ->
         if v = (-1) then
           [%expr (String.length [%e f] * 8)]
         else if v > 0 && (v mod 8) = 0 then
           s
         else
           raise (location_exn ~loc "length of string must be > 0 and multiple of 8, or the special value -1")
      | None, Some (Type.String) -> s
      | Some (v), Some (Type.Bitstring) ->
         if v = (-1) then
           [%expr (Bitstring.bitstring_length [%e f])]
         else if v > 0 then
           s
         else
           raise (location_exn ~loc "length of bitstring must be >= 0 or the special value -1")
      | None, Some (Type.Bitstring) -> s
      | Some (v), _ ->
         if v <= 0 then
           raise (location_exn ~loc "Negative or null field size in constructor")
         else s
      | None, _ -> raise (location_exn ~loc "Invalid field size in constructor")
    end

let rec gen_assignment_size loc = function
  | [] -> [%expr 0]
  | field :: tl ->
     let this = gen_assignment_size_of_field loc field in
     let next = gen_assignment_size loc tl in
     [%expr [%e this] + ([%e next])]

let gen_assignment_behavior loc sym fields =
  let size = gen_assignment_size loc fields in
  let ref = Ast_convenience.evar "Bitstring.Buffer.contents" in
  let res = (Ast_convenience.evar sym) in
  let rep = Ast_convenience.app ref [ res ] in
  let post = match (evaluate_expr size) with
    | Some (v) ->
      let vexpr = Ast_convenience.int v in
      [%expr let _res = [%e rep] in
             if (Bitstring.bitstring_length _res) = [%e vexpr]
             then _res else raise Exit]
    | None ->
      [%expr let _res = [%e rep] in
             if (Bitstring.bitstring_length _res) = [%e size]
             then _res else raise Exit]
  in
  let exprs = List.fold_right
      ~f:(fun fld acc -> [ (gen_constructor loc sym fld) ] @ acc)
      ~init:[post]
      fields in
  let seq = (Ast_convenience.sequence exprs) in
  let ecl = Ast_convenience.evar "Bitstring.Buffer.create" in
  let ini = Ast_convenience.app ecl [ (Ast_convenience.unit ()) ] in
  let res = mkpatvar sym in
  [%expr let [%p res] = [%e ini] in [%e seq]]

let parse_assignment_behavior loc sym value =
  (String.split ~on:';' value)
  |> split_loc ~loc
  |> List.map ~f:(fun flds -> parse_const_fields flds)
  |> gen_assignment_behavior loc sym

let gen_constructor_expr loc value =
  let sym = mksym "constructor" in
  let pat = mkpatvar sym in
  let idt = Ast_convenience.evar sym in
  let fnc = Exp.apply ~loc idt [ (Nolabel, (Ast_convenience.unit ())) ] in
  let beh = parse_assignment_behavior loc sym value in
  [%expr let [%p pat] = fun () -> [%e beh] in [%e fnc] ]

(* transform `let%bitstring foo = {| .. |} in`
   into      `let foo = [%bitstring {| .. |}] in`
*)

let transform_single_let ~mapper loc ast expr =
  match ast.pvb_pat.ppat_desc, ast.pvb_expr.pexp_desc with
  | Parsetree.Ppat_var (s), Pexp_constant (Pconst_string (value, _)) ->
    let pat = mkpatvar s.txt in
    let extension = {Asttypes.txt = "bitstring"; loc} in
    let payload =
      Const.string value
      |> Exp.constant ~loc
      |> Str.eval ~loc
    in
    let constructor_expr = Exp.extension ~loc (extension, PStr [payload]) in
    let expr = [%expr let [%p pat] = [%e constructor_expr] in [%e expr]] in
    mapper.Ast_mapper.expr mapper expr
  | _ -> raise (location_exn ~loc "Invalid pattern type")

let rec transform_let ~mapper loc expr = function
  | [] -> expr
  | hd :: tl ->
     let next = transform_let ~mapper loc expr tl in
     transform_single_let ~mapper loc hd next

(* Mapper *)

let ppx_bitstring_mapper argv = {
  default_mapper with expr = fun mapper expr ->
    match expr with
    (* Is this an extension node? *)
    | { pexp_desc = Pexp_extension ({ txt = "bitstring"; loc }, pstr) } -> begin
        match pstr with
        (* Evaluation of a match expression *)
        | PStr [{
            pstr_desc = Pstr_eval ({
                pexp_loc = loc;
                pexp_desc = Pexp_match (ident, cases)
              }, _)
          }] -> gen_cases ~mapper ident loc cases
        (* Evaluation of a constructor expression *)
        | PStr [{
            pstr_desc = Pstr_eval ({
                pexp_loc = loc;
                pexp_desc = Pexp_constant (Pconst_string (value, _))
              }, _)
          }] -> gen_constructor_expr loc value
        (* Evaluation of a let expression *)
        | PStr [{
            pstr_desc = Pstr_eval ({
                pexp_loc = loc;
                pexp_desc = Pexp_let (Asttypes.Nonrecursive, bindings, expr)
              }, _)
          }] -> transform_let ~mapper loc expr bindings
        | PStr [{
            pstr_desc = Pstr_eval ({
                pexp_loc = loc;
                pexp_desc = Pexp_let (Asttypes.Recursive, bindings, expr)
              }, _)
          }] -> raise (location_exn ~loc "Recursion not supported")
        (* Unsupported expression *)
        | _ -> raise (location_exn ~loc "Unsupported operator")
      end
    (* Delegate to the default mapper. *)
    | x -> default_mapper.expr mapper x;
}

let () = register "ppx_bitstring" ppx_bitstring_mapper
