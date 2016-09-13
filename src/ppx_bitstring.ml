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

(* [Ast_helper] shadows [Str], so we define this first *)
let split_string ~on s =
  Misc.split s on
;;

let option_bind opt f =
  match opt with
  | None   -> None
  | Some v -> f v
;;

open Ast_helper
open Ast_mapper
open Asttypes
open StdLabels
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

  let set_value_type_default q =
    match q.value_type with
    | None  -> { q with value_type = Some Type.Int }
    | _     -> q
  ;;

  let set_sign_default q =
    match q.sign with
    | None  -> { q with sign = Some Sign.Unsigned }
    | _     -> q
  ;;

  let set_endian_default q =
    match q.endian with
    | None  -> { q with endian = Some Endian.Big }
    | _     -> q
  ;;

  let set_defaults v =
    v
    |> set_value_type_default
    |> set_sign_default
    |> set_endian_default
  ;;
end

(* Exception *)

let location_exn ~loc msg =
  Location.Error (Location.error ~loc msg)
  |> raise
;;

(* Helper functions *)

let mksym =
  let i = ref 1000 in
  fun name ->
    incr i; let i = !i in
    sprintf "__ppxbitstring_%s_%d" name i
;;

let mkpvar ~loc name =
  Ast_convenience.pvar ~loc name
;;

let mkevar ~loc name =
  Ast_convenience.evar ~loc name
;;

let rec process_expr_loc ~loc expr =
  match expr with
  | { pexp_desc = Pexp_ident(ident) } ->
    let lident = Location.mkloc ident.txt loc in
    { expr with pexp_desc = Pexp_ident(lident); pexp_loc = loc }
  | { pexp_desc = Pexp_tuple(ops) } ->
    let fld = List.fold_left
        ~init:[]
        ~f:(fun acc exp -> acc @ [ process_expr_loc ~loc exp ]) ops
    in { expr with pexp_desc = Pexp_tuple(fld); pexp_loc = loc }
  | { pexp_desc = Pexp_construct(ident, ops) } ->
    let lident = Location.mkloc ident.txt loc in
    let lops = begin match ops with
      | Some o -> Some (process_expr_loc ~loc o)
      | None    -> None
    end in
    { expr with pexp_desc = Pexp_construct(lident, lops); pexp_loc = loc }
  | { pexp_desc = Pexp_apply(ident, ops) } ->
    let lident = process_expr_loc ~loc ident in
    let fld = List.fold_left
        ~init:[]
        ~f:(fun acc (lbl, exp) -> acc @ [ (lbl, (process_expr_loc ~loc exp)) ]) ops
    in { expr with pexp_desc = Pexp_apply(lident, fld); pexp_loc = loc }
  | { pexp_desc = Pexp_fun(ident, ops,
                           { ppat_desc = Ppat_var(pid); ppat_loc; ppat_attributes },
                           exp) } ->
    let lpid = Location.mkloc pid.txt loc in
    let lpat = { ppat_desc = Ppat_var lpid; ppat_loc = loc; ppat_attributes } in
    let lops = begin match ops with
      | Some o -> Some (process_expr_loc ~loc o)
      | None   -> None
    end in
    let lexp = process_expr_loc ~loc exp in
    { expr with pexp_desc = Pexp_fun(ident, lops, lpat, lexp); pexp_loc = loc }
  | _ ->
    { expr with pexp_loc = loc }
;;

let parse_expr expr =
  try
    process_expr_loc ~loc:expr.loc (Parse.expression (Lexing.from_string expr.txt))
  with
    _ -> location_exn ~loc:expr.loc ("Parse expression error: '" ^ expr.txt ^ "'")
;;

let rec process_pat_loc ~loc pat =
  match pat with
  | { ppat_desc = Ppat_var(ident); ppat_loc; ppat_attributes } ->
    let lident = Location.mkloc ident.txt loc in
    { ppat_desc = Ppat_var(lident); ppat_loc = loc; ppat_attributes }
  | _ ->
    { pat with ppat_loc = loc }
;;

let parse_pattern pat =
  try
    process_pat_loc ~loc:pat.loc (Parse.pattern (Lexing.from_string pat.txt))
  with
    _ -> location_exn ~loc:pat.loc ("Parse pattern error: '" ^ pat.txt ^ "'")
;;

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
;;

let rec split_loc_rec ~loc = function
  | [] -> []
  | hd :: tl ->
    let line_list = split_string ~on:'\n' hd
                    |> List.rev
                    |> List.map ~f:String.length in
    begin
      match line_list with
      | [] -> []
      | last::rem ->
        let (tloc, nloc) = find_loc_boundaries ~loc last rem in
        [ tloc ] @ (split_loc_rec ~loc:nloc tl)
    end
;;

let split_loc ~loc lst =
  split_loc_rec ~loc lst
  |> List.map2 lst ~f:(fun e loc -> Location.mkloc (Bytes.trim e) loc)
;;

(* Processing qualifiers *)

let check_map_functor sub =
  match sub with
  | [%expr (fun [%p? _] -> [%e? _])]  -> Some (sub)
  | _                                 -> None
;;

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
    location_exn ~loc ("Invalid qualifier: " ^ sexp)
;;

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
;;

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
;;

(* Parsing fields *)

let parse_match_fields str =
  split_string ~on:':' str.txt
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
;;

let parse_const_fields str =
  let open Qualifiers in
  split_string ~on:':' str.txt
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
;;

(* Match generators *)

let check_field_len ~loc (l, q) =
  let (>>=) = option_bind in
  match q.Qualifiers.value_type with
  | Some (Type.String) ->
    evaluate_expr l >>= fun v ->
    if v < -1 || (v > 0 && (v mod 8) <> 0) then
      location_exn ~loc "Length of string must be > 0 and multiple of 8, or the special value -1"
    else Some v
  | Some (Type.Bitstring) ->
    evaluate_expr l >>= fun v ->
    if v < -1 then location_exn ~loc "Length of bitstring must be >= 0 or the special value -1"
    else Some v
  | Some (Type.Int) ->
    evaluate_expr l >>= fun v ->
    if v < 1 || v > 64 then location_exn ~loc "Length of int field must be [1..64]"
    else Some v
  | None -> location_exn ~loc "No type to check"
;;

let get_inttype ~loc = function
  | v when v > 8  && v <= 16 -> "int"
  | v when v > 16 && v <= 32 -> "int32"
  | v when v > 32 && v <= 64 -> "int64"
  | _ -> location_exn ~loc "Invalid integer size"
;;

let gen_int_extractor ~loc (dat, off, len) (l, q) edat eoff elen =
  let open Qualifiers in
  match (evaluate_expr l), q.sign, q.endian with
    (* 1-bit type *)
    | Some (size), Some (_), Some (_) when size = 1 ->
      [%expr
        Bitstring.extract_bit [%e edat] [%e eoff] [%e elen] [%e l]]
        [@metaloc loc]
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
      location_exn ~loc "Invalid type"
;;

let gen_extractor ~loc (dat, off, len) (l, q) =
  let open Qualifiers
  in
  let edat = mkevar ~loc dat
  and eoff = mkevar ~loc off
  and elen = mkevar ~loc len
  in
  match q.value_type with
  | Some (Type.Bitstring) -> begin
      match (evaluate_expr l) with
      | Some (-1) ->
        [%expr ([%e edat], [%e eoff], [%e elen])] [@metaloc loc]
      | Some (_) | None ->
        [%expr ([%e edat], [%e eoff], [%e l])] [@metaloc loc]
    end
  | Some (Type.String) ->
    [%expr
      (Bitstring.string_of_bitstring ([%e edat], [%e eoff], [%e l]))]
      [@metaloc loc]
  | Some (Type.Int) ->
    gen_int_extractor ~loc (dat, off, len) (l, q) edat eoff elen
  | _ ->
    location_exn ~loc "Invalid type"
;;

let gen_value ~loc (dat, off, len) (l, q) =
  let open Qualifiers in
  match q.bind, q.map  with
  | Some b, None  -> b
  | None, Some m  ->
    [%expr
      [%e m] [%e (gen_extractor ~loc (dat, off, len) (l, q))]]
      [@metaloc loc]
  | _, _ ->
    gen_extractor ~loc (dat, off, len) (l, q)
;;

let rec gen_next org_off ~loc (dat, off, len) (p, l, q) beh fields =
  let plen = mkpvar ~loc len
  and poff = mkpvar ~loc off
  and elen = mkevar ~loc len
  and eoff = mkevar ~loc off
  in
  evaluate_expr l
  |> function
  | Some (-1) ->
    [%expr
      let [%p poff] = [%e eoff] + [%e elen]
      and [%p plen] = 0 in
      [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]
      [@metaloc loc]
  | Some (_) | None ->
    [%expr
      let [%p poff] = [%e eoff] + [%e l]
      and [%p plen] = [%e elen] - [%e l] in
      [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]
      [@metaloc loc]

and gen_next_all ~loc org_off (dat, off, len) beh fields =
  let plen = mkpvar ~loc len
  and poff = mkpvar ~loc off
  and elen = mkevar ~loc len
  and eoff = mkevar ~loc off
  in
  [%expr
    let [%p poff] = [%e eoff] + [%e elen]
    and [%p plen] = 0 in
    [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]]
    [@metaloc loc]

and gen_match_check ~loc = function
  | Some chk  -> chk
  | None      -> Ast_convenience.constr ~loc "true" []

and gen_match ~loc org_off (dat, off, len) (p, l, q) beh fields =
  let open Qualifiers in
  let valN = mksym "value"
  in
  let pvalN = mkpvar ~loc valN
  and evalN = mkevar ~loc valN
  and poff = mkpvar ~loc off
  and eoff = mkevar ~loc off
  and plen = mkpvar ~loc len
  and elen = mkevar ~loc len
  in
  gen_match_check ~loc q.check
  |> fun g ->
  [%expr
    begin match [%e evalN] with
      | [%p p] when [%e g] ->
        [%e (gen_fields org_off ~loc (dat, off, len) beh fields)]
      | _ -> ()
    end]
    [@metaloc loc]
  |> fun m ->
  [%expr
    let [%p pvalN]  = [%e (gen_value ~loc (dat, off, len) (l, q))]
    and [%p poff]   = [%e eoff] + [%e l]
    and [%p plen]   = [%e elen] - [%e l] in [%e m]]
    [@metaloc loc]

and gen_offset_saver ~loc org_off (dat, off, len) (p, l, q) beh =
  let open Qualifiers in
  match q.save_offset_to with
  | Some { pexp_desc = Pexp_ident ({ txt; _ }) } ->
    let ptxt = mkpvar ~loc (Longident.last txt)
    and eoff = mkevar ~loc off
    and eorg_off = mkevar ~loc org_off in
    [%expr
      let [%p (ptxt)] = [%e eoff] - [%e eorg_off] in [%e beh]]
      [@metaloc loc]
  | Some _ | None -> beh

and gen_unbound_string ~loc org_off (dat, off, len) (l, q) beh fields p =
  match p with
  | { ppat_desc = Ppat_var(_) } ->
    [%expr
      let [%p p] = [%e (gen_value ~loc (dat, off, len) (l, q))] in
      [%e (gen_next_all ~loc org_off (dat, off, len) beh fields)]]
      [@metaloc loc]
  | [%pat? _ ] ->
    [%expr
      [%e (gen_next_all org_off ~loc (dat, off, len) beh fields)]]
      [@metaloc loc]
  | _ ->
    location_exn ~loc "Unbound string or bitstring can only be assigned to a variable or skipped"

and gen_bound_bitstring ~loc org_off (dat, off, len) (l, q) beh fields p =
  let elen = mkevar ~loc len in
  match p with
  | { ppat_desc = Ppat_var(_) } ->
    [%expr
      if [%e elen] >= [%e l] then
        let [%p p] = [%e (gen_value ~loc (dat, off, len) (l, q))] in
        [%e (gen_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
      else ()]
      [@metaloc loc]
  | [%pat? _ ] ->
    [%expr
      if [%e elen] >= [%e l] then
        [%e (gen_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
      else ()]
      [@metaloc loc]
  | _ ->
    location_exn ~loc "Bound bitstring can only be assigned to variables or skipped"

and gen_bound_string ~loc org_off (dat, off, len) (l, q) beh fields p =
  [%expr
    if [%e (mkevar ~loc len)] >= [%e l] then
      [%e (gen_match ~loc org_off (dat, off, len) (p, l, q) beh fields)]
    else ()]
    [@metaloc loc]

and gen_bound_int ~loc org_off (dat, off, len) (l, q) beh fields p =
  [%expr
    if [%e l] >= 1 && [%e l] <= 64 && [%e (mkevar ~loc len)] >= [%e l] then
      [%e (gen_match ~loc org_off (dat, off, len) (p, l, q) beh fields)]
    else ()]
    [@metaloc loc]

and gen_fields_with_quals_by_type ~loc org_off (dat, off, len) (p, l, q) beh fields =
  let open Qualifiers in
  match check_field_len ~loc (l, q), q.value_type with
  | Some (-1), Some (Type.Bitstring | Type.String) ->
    gen_unbound_string ~loc org_off (dat, off, len) (l, q) beh fields p
  | (Some (_) | None), Some (Type.Bitstring) ->
    gen_bound_bitstring ~loc org_off (dat, off, len) (l, q) beh fields p
  | (Some (_) | None), Some (Type.String) ->
    gen_bound_string ~loc org_off (dat, off, len) (l, q) beh fields p
  | Some (_), Some (Type.Int)
  | None, Some (Type.Int) ->
    gen_bound_int ~loc org_off (dat, off, len) (l, q) beh fields p
  | _, _ ->
    location_exn ~loc "No type to generate"

and gen_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh fields =
  gen_fields_with_quals_by_type ~loc org_off (dat, off, len) (p, l, q) beh fields
  |> gen_offset_saver ~loc org_off (dat, off, len) (p, l, q)

and gen_fields ~loc org_off (dat, off, len) beh fields =
  let open Qualifiers in
  match fields with
  | [] -> beh
  | (p, None, None) :: tl -> beh
  | (p, Some l, Some q) :: tl ->
    gen_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh tl
  | _ -> location_exn ~loc "Wrong pattern type in bitmatch case"
;;

let gen_case org_off res (dat, off, len) case =
  let loc = case.pc_lhs.ppat_loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_constant (Pconst_string (value, _)) ->
    let eres = mkevar ~loc res in
    let beh = [%expr [%e eres] := Some ([%e case.pc_rhs]); raise Exit][@metaloc loc]
    in split_string ~on:';' value
    |> split_loc ~loc
    |> List.map ~f:parse_match_fields
    |> gen_fields ~loc org_off (dat, off, len) beh
  | _ ->
    location_exn ~loc "Wrong pattern type"
;;

let rec gen_cases_sequence ~loc = function
  | [] -> location_exn ~loc "Empty case list"
  | [hd] -> hd
  | hd :: tl -> Exp.sequence ~loc hd (gen_cases_sequence ~loc tl)
;;

let gen_cases ident loc cases =
  let open Location in
  let datN = mksym "data"
  and offN = mksym "off"
  and lenN = mksym "len"
  and algN = mksym "aligned"
  and resN = mksym "result"
  and offNN = mksym "off"
  and lenNN = mksym "len"
  in
  let pdatN = mkpvar ~loc datN
  and poffN = mkpvar ~loc offN
  and eoffN = mkevar ~loc offN
  and plenN = mkpvar ~loc lenN
  and elenN = mkevar ~loc lenN
  and palgN = mkpvar ~loc algN
  and presN = mkpvar ~loc resN
  and eresN = mkevar ~loc resN
  and poffNN = mkpvar ~loc offNN
  and plenNN = mkpvar ~loc lenNN
  in
  let tuple = [%pat? ([%p pdatN], [%p poffN], [%p plenN])][@metaloc loc]
  and fname = Ast_convenience.str ~loc loc.loc_start.pos_fname
  and lpos = Ast_convenience.int ~loc loc.loc_start.pos_lnum
  and cpos = Ast_convenience.int ~loc loc.loc_start.pos_cnum
  in
  cases
  |> List.fold_left
    ~init:[]
    ~f:(fun acc case -> acc @ [ gen_case offN resN (datN, offNN, lenNN) case ])
  |> gen_cases_sequence ~loc
  |> fun seq ->
  [%expr
    let [%p tuple] = [%e ident] in
    let [%p poffNN] = [%e eoffN]
    and [%p plenNN] = [%e elenN] in
    let [%p palgN] = ([%e eoffN] land 7) = 0 in
    let [%p presN] = ref None in
    (try [%e seq]; with | Exit -> ());
    match ![%e eresN] with
    | Some x -> x
    | None -> raise (Match_failure ([%e fname], [%e lpos], [%e cpos]))]
    [@metaloc loc]
;;

(* constructor expressions *)

let gen_constructor loc sym = function
  | (l, Some (s), Some(q)) ->
    let open Location in
    let open Qualifiers in
    let exc = Ast_convenience.constr ~loc
        "Bitstring.Construct_failure"
        [ Ast_convenience.str ~loc "Bad field value";
          Ast_convenience.str ~loc "None";
          Ast_convenience.int ~loc loc.loc_start.pos_lnum;
          Ast_convenience.int ~loc loc.loc_start.pos_cnum ]
    in begin match q.value_type with
      | Some (Type.Bitstring) ->
        let ex = "Bitstring.construct_bitstring" in
        Ast_convenience.app ~loc
          (Ast_convenience.evar ~loc ex)
          [ (Ast_convenience.evar ~loc sym); l ]
      | Some (Type.String) ->
        let ex = "Bitstring.construct_string" in
        Ast_convenience.app ~loc
          (Ast_convenience.evar ~loc ex)
          [ (Ast_convenience.evar ~loc sym); l ]
      | Some (Type.Int) -> begin
          match (evaluate_expr s), q.sign, q.endian with
          (* 1-bit type *)
          | Some (size), Some (_), Some (_) when size = 1 -> begin
              let ex = "Bitstring.construct_bit" in
              let vl = match (evaluate_expr l) with
                | Some (1)        -> Ast_convenience.constr ~loc "true" []
                | Some (0)        -> Ast_convenience.constr ~loc "false" []
                | Some (_) | None -> l
              in Ast_convenience.app ~loc
                (Ast_convenience.evar ~loc ex)
                [ (Ast_convenience.evar ~loc sym); vl; (Ast_convenience.int ~loc 1); exc ]
            end
          (* 8-bit type *)
          | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
            let sn = Sign.to_string sign in
            let ex = sprintf "Bitstring.construct_char_%s" sn in
            Ast_convenience.app ~loc
              (Ast_convenience.evar ~loc ex)
              [ (Ast_convenience.evar ~loc sym); l; (Ast_convenience.int ~loc size); exc ]
          (* 16|32|64-bit type *)
          | Some (size), Some (sign), Some (Endian.Referred r) ->
            let ss = Sign.to_string sign and it = get_inttype ~loc size in
            let ex = sprintf "Bitstring.construct_%s_ee_%s" it ss in
            Ast_convenience.app ~loc
              (Ast_convenience.evar ex)
              [ r; (Ast_convenience.evar ~loc sym); l; (Ast_convenience.int ~loc size); exc ]
          | Some (size), Some (sign), Some (endian) ->
            let tp = get_inttype ~loc size in
            let en = Endian.to_string endian in
            let sn = Sign.to_string sign in
            let ex = sprintf "Bitstring.construct_%s_%s_%s" tp en sn in
            Ast_convenience.app ~loc
              (Ast_convenience.evar ~loc ex)
              [ (Ast_convenience.evar ~loc sym); l; (Ast_convenience.int ~loc size); exc ]
          (* Invalid type *)
          | _, _, _ ->
            location_exn ~loc "Invalid type"
        end
      | _ -> location_exn ~loc "Invalid type"
    end
  | _ -> location_exn ~loc "Invalid field format"
;;

let gen_assignment_size_of_field loc = function
  | (_, None, _) -> [%expr 0]
  | (f, Some (s), q) -> begin
      match (evaluate_expr s), option_bind q (fun q -> q.Qualifiers.value_type) with
      | Some (v), Some (Type.String) ->
         if v = (-1) then
           [%expr (String.length [%e f] * 8)]
         else if v > 0 && (v mod 8) = 0 then
           s
         else
           location_exn ~loc "Length of string must be > 0 and multiple of 8, or the special value -1"
      | None, Some (Type.String) -> s
      | Some (v), Some (Type.Bitstring) ->
         if v = (-1) then
           [%expr (Bitstring.bitstring_length [%e f])]
         else if v > 0 then
           s
         else
           location_exn ~loc "Length of bitstring must be >= 0 or the special value -1"
      | None, Some (Type.Bitstring) -> s
      | Some (v), _ ->
         if v <= 0 then
           location_exn ~loc "Negative or null field size in constructor"
         else s
      | None, _ -> location_exn ~loc "Invalid field size in constructor"
    end
;;

let rec gen_assignment_size loc = function
  | [] -> [%expr 0]
  | field :: tl ->
     let this = gen_assignment_size_of_field loc field in
     let next = gen_assignment_size loc tl in
     [%expr [%e this] + ([%e next])][@metaloc loc]
;;

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
  let res = mkpvar ~loc sym in
  [%expr let [%p res] = [%e ini] in [%e seq]][@metaloc loc]
;;

let parse_assignment_behavior loc sym value =
  (split_string ~on:';' value)
  |> split_loc ~loc
  |> List.map ~f:(fun flds -> parse_const_fields flds)
  |> gen_assignment_behavior loc sym
;;

let gen_constructor_expr loc value =
  let sym = mksym "constructor" in
  let pat = mkpvar ~loc sym in
  let idt = Ast_convenience.evar sym in
  let fnc = Exp.apply ~loc idt [ (Nolabel, (Ast_convenience.unit ())) ] in
  let beh = parse_assignment_behavior loc sym value in
  [%expr let [%p pat] = fun () -> [%e beh] in [%e fnc]]
;;

let transform_single_let ~loc ast expr =
  match ast.pvb_pat.ppat_desc, ast.pvb_expr.pexp_desc with
  | Parsetree.Ppat_var (s), Pexp_constant (Pconst_string (value, _)) ->
    let pat = mkpvar ~loc s.txt in
    let constructor_expr = gen_constructor_expr loc value in
    [%expr let [%p pat] = [%e constructor_expr] in [%e expr]]
  | _ -> location_exn ~loc "Invalid pattern type"
;;

(* Mapper *)

open Ppx_core.Std

let extension =
  Extension.V2.declare
    "bitstring"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    (fun ~loc:_ ~path:_ expr ->
      let loc = expr.pexp_loc in
      let expansion =
        match expr.pexp_desc with
        | Pexp_constant (Pconst_string (value, (_ : string option))) ->
           gen_constructor_expr loc value
        | Pexp_let (Nonrecursive, bindings, expr) ->
           List.fold_right bindings ~init:expr ~f:(fun binding expr ->
               transform_single_let ~loc binding expr)
        | Pexp_match (ident, cases) ->
           gen_cases ident loc cases
        | _ ->
           location_exn ~loc
             "'bitstring' can only be used with 'let', 'match', and as '[%bitstring]'"
      in
      { expansion with pexp_attributes = expr.pexp_attributes }
    )
;;

let () =
  Ppx_driver.register_transformation "bitstring" ~extensions:[extension]
;;
