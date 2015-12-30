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
    save_offset_to  : Parsetree.expression option;
  }
  let empty = {
    value_type      = None;
    sign            = None;
    endian          = None;
    check           = None;
    bind            = None;
    save_offset_to  = None;
  }
  let default = {
    value_type      = Some Type.Int;
    sign            = Some Sign.Unsigned;
    endian          = Some Endian.Big;
    check           = None;
    bind            = None;
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

let mkpatvar ~loc name =
  { (Parse.pattern (Lexing.from_string name)) with ppat_loc = loc }

let mkident ~loc name =
  { (Parse.expression (Lexing.from_string name)) with pexp_loc = loc }

let rec process_loc ~loc expr =
  match expr with
  | { pexp_desc = Pexp_tuple(ops) } ->
      let fld = List.fold ~init:[]
        ~f:(fun acc exp -> acc @ [ process_loc ~loc exp ]) ops
      in
      { expr with pexp_desc = Pexp_tuple(fld); pexp_loc = loc }
  | { pexp_desc = Pexp_apply(ident, ops) } ->
      let fld = List.fold ~init:[]
        ~f:(fun acc (lbl, exp) -> acc @ [ (lbl, (process_loc ~loc exp)) ]) ops
      in
      { expr with pexp_desc = Pexp_apply(ident, fld); pexp_loc = loc }
  | { pexp_desc = Pexp_ident(_) }
  | { pexp_desc = Pexp_constant(_) } ->
      { expr with pexp_loc = loc }
  | _ ->
      fprintf stderr "%s\n" (Pprintast.string_of_expression expr);
      expr

let parse_expr ~loc str =
   process_loc ~loc (Parse.expression (Lexing.from_string str))

let parse_pattern ~loc str =
  { (Parse.pattern (Lexing.from_string str)) with ppat_loc = loc }

(* Exception *)

let location_exn ~loc msg =
  raise (Location.Error (Location.error ~loc ("Error: " ^ msg)))

(* Processing qualifiers *)

let process_qual ~loc state q =
  let open Qualifiers in
  match q with
  | [%expr int] ->
      begin match state.value_type with
      | Some v -> location_exn ~loc "Value type can only be defined once"
      | None -> { state with value_type = Some Type.Int }
      end
  | [%expr string] ->
      begin match state.value_type with
      | Some v -> location_exn ~loc  "Value type can only be defined once"
      | None -> { state with value_type = Some Type.String }
      end
  | [%expr bitstring] ->
      begin match state.value_type with
      | Some v -> location_exn ~loc  "Value type can only be defined once"
      | None -> { state with value_type = Some Type.Bitstring }
      end
  | [%expr signed] ->
      begin match state.sign with
      | Some v -> location_exn ~loc  "Signedness can only be defined once"
      | None -> { state with sign = Some Sign.Signed }
      end
  | [%expr unsigned] ->
      begin match state.sign with
      | Some v -> location_exn ~loc  "Signedness can only be defined once"
      | None -> { state with sign = Some Sign.Unsigned }
      end
  | [%expr littleendian] ->
      begin match state.endian with
      | Some v -> location_exn ~loc  "Endianness can only be defined once"
      | None -> { state with endian = Some Endian.Little }
      end
  | [%expr bigendian] ->
      begin match state.endian with
      | Some v -> location_exn ~loc  "Endianness can only be defined once"
      | None -> { state with endian = Some Endian.Big }
      end
  | [%expr nativeendian] ->
      begin match state.endian with
      | Some v -> location_exn ~loc  "Endianness can only be defined once"
      | None -> { state with endian = Some Endian.Native }
      end
  | [%expr endian [%e? sub]] ->
      begin match state.endian with
      | Some v -> location_exn ~loc  "Endianness can only be defined once"
      | None -> { state with endian = Some (Endian.Referred sub) }
      end
  | [%expr bind [%e? sub]] ->
      begin match state.check with
      | Some v -> location_exn ~loc  "Bind expression can only be defined once"
      | None -> { state with bind = Some sub }
      end
  | [%expr check [%e? sub]] ->
      begin match state.bind with
      | Some v -> location_exn ~loc  "Check expression can only be defined once"
      | None -> { state with check = Some sub }
      end
  | [%expr save_offset_to [%e? sub]] ->
      begin match state.save_offset_to with
      | Some v -> location_exn ~loc  "Offset expression can only be defined once"
      | None -> { state with save_offset_to = Some sub }
      end
  | _ -> raise (location_exn ~loc ("Invalid qualifier: " ^ (Pprintast.string_of_expression q)))

let parse_quals ~loc str =
  let expr = parse_expr ~loc str in
  let rec process_quals ~loc state = function
    | [] -> state
    | hd :: tl -> process_quals ~loc (process_qual ~loc state hd) tl
  in match expr with
  (* single named qualifiers *)
  | { pexp_desc = Pexp_ident (_) } -> process_qual ~loc Qualifiers.empty expr
  (* single functional qualifiers *)
  | { pexp_desc = Pexp_apply (_, _) } -> process_qual ~loc Qualifiers.empty expr
  (* multiple qualifiers *)
  | { pexp_desc = Pexp_tuple (elements) } -> process_quals ~loc Qualifiers.empty elements
  | _ -> location_exn ~loc  ("Format error: " ^ str)

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
      | Const_int i -> Some i
      | _ -> None
      end
  | _ -> None

(* Parsing fields *)

let parse_fields ~loc str =
  let e = List.fold_right ~init:[] ~f:(fun e acc -> [StdLabels.Bytes.trim e] @ acc) (String.split ~on:':' str) in
  match e with
  | [ "_" as pat ] ->
      (parse_pattern ~loc pat, None, None)
  | [ pat; len ] ->
      (parse_pattern ~loc pat, Some (parse_expr ~loc len), Some Qualifiers.default)
  | [ pat; len; quals ] ->
      (parse_pattern ~loc pat, Some (parse_expr ~loc len), Some (Qualifiers.set_defaults (parse_quals ~loc quals)))
  | _ -> location_exn ~loc  ("Format error: " ^ str)

(* Generators *)

let check_field_len ~loc (l, q) =
  let open Option.Monad_infix in
  match q.Qualifiers.value_type with
  | Some (Type.String) ->
      evaluate_expr l >>= fun v ->
        if v < -1 || (v > 0 && (v mod 8) <> 0) then
          location_exn ~loc  "length of string must be > 0 and multiple of 8, or the special value -1"
        else Some v
  | Some (Type.Bitstring) ->
      evaluate_expr l >>= fun v ->
        if v < -1 then location_exn ~loc  "length of bitstring must be >= 0 or the special value -1"
        else Some v
  | Some (Type.Int) ->
      evaluate_expr l >>= fun v ->
        if v < 1 || v > 64 then location_exn ~loc  "length of int field must be [1..64]"
        else Some v
  | None -> location_exn ~loc "No type to check"

let get_inttype ~loc = function
  | v when v > 8  && v <= 16 -> "int"
  | v when v > 16 && v <= 32 -> "int32"
  | v when v > 32 && v <= 64 -> "int64"
  | _ -> location_exn ~loc "Invalid integer size"

let generate_extractor (dat, off, len) (l, q) loc =
  let open Qualifiers in
  match q.value_type with
  | Some (Type.Bitstring) ->
      [%expr ([%e (mkident ~loc dat)], [%e (mkident ~loc off)], [%e (mkident ~loc len)])]
      [@metaloc loc]
  | Some (Type.String) ->
      [%expr (Bitstring.string_of_bitstring ([%e (mkident ~loc dat)] [%e (mkident ~loc off)] [%e (mkident ~loc len)]))]
      [@metaloc loc]
  | Some (Type.Int) ->
      begin match (evaluate_expr l), q.sign, q.endian with
      (* 1-bit type *)
      | Some (size), Some (_), Some (_) when size = 1 ->
          [%expr if (Bitstring.extract_bit [%e (mkident ~loc dat)] [%e (mkident ~loc off)]
          [%e (mkident ~loc len)] [%e l]) then 1 else 0]
          [@metaloc loc]
      (* 8-bit type *)
      | Some (size), Some (sign), Some (_) when size >= 2 && size <= 8 ->
          let ex = sprintf "Bitstring.extract_char_%s" (Sign.to_string sign) in
          let op = sprintf "%s %s %s %s %d" ex dat off len size in
          parse_expr ~loc op
      (* 16|32|64-bit type *)
      | Some (size), Some (sign), Some (Endian.Referred r) ->
          let ex = sprintf "Bitstring.extract_%s_ee_%s" (get_inttype ~loc size) (Sign.to_string sign) in
          let ee = Pprintast.string_of_expression r in
          let op = sprintf "%s (%s) %s %s %s %d" ex ee dat off len size in
          parse_expr ~loc op
      | Some (size), Some (sign), Some (endian) ->
          let tp = get_inttype ~loc size in
          let en = Endian.to_string endian in
          let sn = Sign.to_string sign in
          let ex = sprintf "Bitstring.extract_%s_%s_%s" tp en sn in
          let op = sprintf "%s %s %s %s %d" ex dat off len size in
          parse_expr ~loc op
      (* Variable size *)
      | None, Some (sign), Some (Endian.Referred r) ->
          let ex = sprintf "Bitstring.extract_int64_ee_%s" (Sign.to_string sign) in
          let ee = Pprintast.string_of_expression r in
          let ln = Pprintast.string_of_expression l in
          let op = sprintf "%s (%s) %s %s %s (%s)" ex ee dat off len ln in
          parse_expr ~loc op
      | None, Some (sign), Some (endian) ->
          let ex = sprintf "Bitstring.extract_int64_%s_%s" (Endian.to_string endian) (Sign.to_string sign) in
          let ln = Pprintast.string_of_expression l in
          let op = sprintf "%s %s %s %s (%s)" ex dat off len ln in
          parse_expr ~loc op
      (* Invalid type *)
      | _, _, _ ->
          raise (location_exn ~loc "Invalid type")
      end
  | _ -> raise (location_exn ~loc "Invalid type")

let generate_value (dat, off, len) (l, q) loc =
  let open Qualifiers in
  match q.bind with
  | Some b -> b
  | None -> generate_extractor (dat, off, len) (l, q) loc

let rec generate_next org_off ~loc (dat, off, len) (p, l, q) beh fields =
  [%expr let [%p (mkpatvar ~loc off)] = [%e (mkident ~loc off)] + [%e l]
  and [%p (mkpatvar ~loc len)] = [%e (mkident ~loc len)] - [%e l] in
  [%e (generate_fields org_off ~loc (dat, off, len) beh fields)]]
  [@metaloc loc]

and generate_next_all ~loc org_off (dat, off, len) beh fields =
  [%expr let [%p (mkpatvar ~loc off)] = [%e (mkident ~loc off)] + [%e (mkident ~loc len)]
  and [%p (mkpatvar ~loc len)] = 0 in
  [%e (generate_fields org_off ~loc (dat, off, len) beh fields)]]
  [@metaloc loc]

and generate_match org_off (dat, off, len) (p, l, q) loc beh fields =
  let open Qualifiers in
  let valN = mksym "value" in
  let m = match q.check with
  | Some chk ->
      [%expr begin match [%e (mkident ~loc valN)] with
      | [%p p] when [%e chk] -> [%e (generate_fields org_off ~loc (dat, off, len) beh fields)]
      | _ -> () end] [@metaloc loc]
  | None ->
      [%expr begin match [%e (mkident ~loc valN)] with
      | [%p p] when true  -> [%e (generate_fields ~loc org_off (dat, off, len) beh fields)]
      | _ -> () end] [@metaloc loc]
  in
  [%expr let [%p (mkpatvar ~loc valN)] = [%e (generate_value (dat, off, len) (l, q) loc)] in
  let [%p (mkpatvar ~loc off)] = [%e (mkident ~loc off)] + [%e l]
  and [%p (mkpatvar ~loc len)] = [%e (mkident ~loc len)] - [%e l] in [%e m]]
  [@metaloc loc]

and generate_offset_saver org_off (dat, off, len) (p, l, q) loc beh =
  let open Qualifiers in
  match q.save_offset_to with
  | Some { pexp_desc = Pexp_ident ({ txt; _ }) } -> [%expr
      let [%p (mkpatvar ~loc (Longident.last txt))] = [%e (mkident ~loc off)] - [%e (mkident ~loc org_off)]
      in [%e beh]] [@metaloc loc]
  | Some _ | None -> beh

and generate_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh fields =
  let open Qualifiers in
  match check_field_len ~loc (l, q), q.value_type with
  | Some (-1), Some (Type.Bitstring | Type.String) ->
      begin match p with
      | { ppat_desc = Ppat_var(_) } ->
          generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          let [%p p] = [%e (generate_value (dat, off, len) (l, q) loc)] in
          [%e (generate_next_all ~loc org_off (dat, off, len) beh fields)]]
          [@metaloc loc]
        | [%pat? _ ] ->
          generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          [%e (generate_next_all org_off ~loc (dat, off, len) beh fields)]]
          [@metaloc loc]
      | _ ->
          location_exn ~loc  "Unbound string or bitstring can only be assigned to a variable or skipped"
      end
  | (Some (_) | None), Some (Type.Bitstring) ->
      begin match p with
      | { ppat_desc = Ppat_var(_) } ->
          generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          if [%e (mkident ~loc len)] >= [%e l] then
            let [%p p] = [%e (generate_value (dat, off, len) (l, q) loc)] in
            [%e (generate_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
          else ()]
          [@metaloc loc]
      | [%pat? _ ] ->
          generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
          if [%e (mkident ~loc len)] >= [%e l] then
            [%e (generate_next ~loc org_off (dat, off, len) (p, l, q) beh fields)]
          else ()]
          [@metaloc loc]
      | _ -> location_exn ~loc  "Bound bitstring can only be assigned to variables or skipped"
      end
  | (Some (_) | None), Some (Type.String) ->
      generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e (mkident ~loc len)] >= [%e l] then
      [%e (generate_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
      [@metaloc loc]
  | Some (_), Some (Type.Int) ->
      generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e (mkident ~loc len)] >= [%e l] then
      [%e (generate_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
      [@metaloc loc]
  | None, Some (Type.Int) ->
      generate_offset_saver org_off (dat, off, len) (p, l, q) loc [%expr
      if [%e l] >= 1 && [%e l] <= 64 && [%e (mkident ~loc len)] >= [%e l] then
      [%e (generate_match org_off (dat, off, len) (p, l, q) loc beh fields)]
      else ()]
      [@metaloc loc]
  | _, _ -> location_exn ~loc  "No type to generate"

and generate_fields ~loc org_off (dat, off, len) beh fields =
  let open Qualifiers in
  match fields with
  | [] -> beh
  | (p, None, None) :: tl -> beh
  | (p, Some l, Some q) :: tl ->
      generate_fields_with_quals ~loc org_off (dat, off, len) (p, l, q) beh tl
  | _ -> location_exn ~loc  "Wrong pattern type in bitmatch case"

let generate_case org_off res (dat, off, len) case =
  let loc = case.pc_lhs.ppat_loc in
  match case.pc_lhs.ppat_desc with
  | Ppat_constant (Const_string (value, _)) ->
      let beh = [%expr [%e (mkident ~loc res)] := Some ([%e case.pc_rhs]); raise Exit] [@metaloc loc]
      in
      List.map ~f:(fun flds -> parse_fields ~loc flds) (String.split ~on:';' value)
      |> generate_fields ~loc org_off (dat, off, len) beh
    | _ -> location_exn ~loc  "Wrong pattern type in bitmatch case"

let generate_cases ident loc cases =
  let open Location in
  let datN = mksym "data" in
  let offNN = mksym "off" and lenNN = mksym "len" in
  let offN = mksym "off" and lenN = mksym "len" in
  let algN = mksym "aligned" and resN = mksym "result" in
  let stmts = List.fold ~init:[]
    ~f:(fun acc case -> acc @ [ generate_case offN resN (datN, offNN, lenNN) case ])
    cases
  in
  let rec build_seq = function
    | [] -> location_exn ~loc  "Empty case list"
    | [hd] -> hd
    | hd :: tl -> Exp.sequence hd (build_seq tl)
  in
  let seq = build_seq stmts in
  let tuple = [%pat? ([%p (mkpatvar ~loc datN)], [%p (mkpatvar ~loc offN)], [%p (mkpatvar ~loc lenN)])] in
  let fname = Exp.constant ~loc (Const_string (loc.loc_start.pos_fname, None)) in
  let lpos = Exp.constant ~loc (Const_int loc.loc_start.pos_lnum) in
  let cpos = Exp.constant ~loc (Const_int loc.loc_start.pos_cnum) in
  [%expr
    let [%p tuple] = [%e ident] in
    let [%p (mkpatvar ~loc offNN)] = [%e (mkident ~loc offN)]
    and [%p (mkpatvar ~loc lenNN)] = [%e (mkident ~loc lenN)]
    in
    let [%p (mkpatvar ~loc algN)] = ([%e (mkident ~loc offN)] land 7) = 0 in
    let [%p (mkpatvar ~loc resN)] = ref None in
    (try [%e seq];
    with | Exit -> ());
    match ![%e (mkident ~loc resN)] with
    | Some x -> x
    | None -> raise (Match_failure ([%e fname], [%e lpos], [%e cpos]))]
  [@metaloc loc]

let getenv_mapper argv =
  (* Our getenv_mapper only overrides the handling of expressions in the default mapper. *)
  { default_mapper with expr = fun mapper expr ->
    match expr with
    (* Is this an extension node? *)
    | { pexp_desc = Pexp_extension ({ txt = "bitstring"; loc }, pstr) } ->
        begin match pstr with
        (* Should have a single structure item, which is evaluation of a match expression *)
        | PStr [{ pstr_desc = Pstr_eval ( { pexp_loc = loc; pexp_desc =
          Pexp_match (ident, cases) }, _) }] -> generate_cases ident loc cases
        | _ -> raise (location_exn ~loc "[%bitstring] requires a match operator")
        end
    (* Delegate to the default mapper. *)
    | x -> default_mapper.expr mapper x;
  }

let () = register "getenv" getenv_mapper
