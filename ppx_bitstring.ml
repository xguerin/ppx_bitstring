open Ast_helper
open Ast_lifter
open Ast_mapper
open Asttypes
open Core.Std
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
end

module Endian = struct
  type t =
    | Little
    | Big
    | Native
    | Referred of Parsetree.expression
end

type t = {
  value_type    : Type.t option;
  sign          : Sign.t option;
  endian        : Endian.t option;
  check         : Parsetree.expression option;
  bind          : Parsetree.expression option;
  set_offset_at : Parsetree.expression option;
}

let empty = {
  value_type    = None;
  sign          = None;
  endian        = None;
  check         = None;
  bind          = None;
  set_offset_at = None;
}

(* Helper functions *)

let mksym =
  let i = ref 1000 in
  fun name ->
    incr i; let i = !i in
    sprintf "__pabitstring_%s_%d" name i

let mkpatvar name =
  Parse.pattern (Lexing.from_string name)

let mkident name =
  Parse.expression (Lexing.from_string name)

(* Processing qualifiers *)

let process_qual state q =
  match q with
  | [%expr int] ->
      begin match state.value_type with
      | Some v -> Result.Error "Value type can only be defined once"
      | None -> Result.Ok { state with value_type = Some Type.Int }
      end
  | [%expr string] ->
      begin match state.value_type with
      | Some v -> Result.Error "Value type can only be defined once"
      | None -> Result.Ok { state with value_type = Some Type.String }
      end
  | [%expr bitstring] ->
      begin match state.value_type with
      | Some v -> Result.Error "Value type can only be defined once"
      | None -> Result.Ok { state with value_type = Some Type.Bitstring }
      end
  | [%expr signed] ->
      begin match state.sign with
      | Some v -> Result.Error "Signedness can only be defined once"
      | None -> Result.Ok { state with sign = Some Sign.Signed }
      end
  | [%expr unsigned] ->
      begin match state.sign with
      | Some v -> Result.Error "Signedness can only be defined once"
      | None -> Result.Ok { state with sign = Some Sign.Unsigned }
      end
  | [%expr littleendian] ->
      begin match state.endian with
      | Some v -> Result.Error "Endianness can only be defined once"
      | None -> Result.Ok { state with endian = Some Endian.Little }
      end
  | [%expr bigendian] ->
      begin match state.endian with
      | Some v -> Result.Error "Endianness can only be defined once"
      | None -> Result.Ok { state with endian = Some Endian.Big }
      end
  | [%expr nativeendian] ->
      begin match state.endian with
      | Some v -> Result.Error "Endianness can only be defined once"
      | None -> Result.Ok { state with endian = Some Endian.Native }
      end
  | [%expr endian [%e? sub]] ->
      begin match state.endian with
      | Some v -> Result.Error "Endianness can only be defined once"
      | None -> Result.Ok { state with endian = Some (Endian.Referred sub) }
      end
  | [%expr bind [%e? sub]] ->
      begin match state.check with
      | Some v -> Result.Error "Check expression can only be defined once"
      | None -> Result.Ok { state with check = Some sub }
      end
  | [%expr check [%e? sub]] ->
      begin match state.bind with
      | Some v -> Result.Error "Bind expression can only be defined once"
      | None -> Result.Ok { state with bind = Some sub }
      end
  | [%expr set_offset_at [%e? sub]] ->
      begin match state.set_offset_at with
      | Some v -> Result.Error "Offset expression can only be defined once"
      | None -> Result.Ok { state with set_offset_at = Some sub }
      end
  | _ -> Result.Error ("Invalid qualifier: " ^ (Pprintast.string_of_expression q))

let parse_quals str =
  try
    let expr = Parse.expression (Lexing.from_string str) in
    let rec process_quals state = function
      | [] -> Result.Ok state
      | hd :: tl ->
          begin match process_qual state hd with
          | Result.Ok state -> process_quals state tl
          | Result.Error e -> Result.Error e
          end
    in match expr with
    (* single named qualifiers *)
    | { pexp_desc = Pexp_ident (_) } -> process_qual empty expr
    (* single functional qualifiers *)
    | { pexp_desc = Pexp_apply (_, _) } -> process_qual empty expr
    (* multiple qualifiers *)
    | { pexp_desc = Pexp_tuple (elements) } -> process_quals empty elements
    | _ -> Result.Error ("Format error: " ^ str)
  with
  | Syntaxerr.Error _ -> Result.Error ("Syntax error: " ^ str)

(* Processing expression *)

let parse_expr str =
  try
    let expr = Parse.expression (Lexing.from_string str) in
    Result.Ok expr
  with
  | Syntaxerr.Error _ -> Result.Error ("Syntax error: " ^ str)

(* Processing pattern *)

let pattern_lifter =
  object
    inherit [bool] Ast_lifter.lifter as super
    method record (_ : string) x =
      let rec scan_result v = function
        | [] -> v
        | (n, s) :: tl ->
            begin match n with
            | "ppat_attributes" | "ppat_loc" | "txt" | "loc" -> scan_result v tl
            | _ -> scan_result (s && v) tl
            end
     in
      scan_result true x
    method constr (_ : string) (c, args) =
      let rec scan_args v = function
        | [] -> v
        | hd :: tl -> scan_args (v && hd) tl
      in
      match c with
      | "Ppat_extension"  | "Ppat_exception"  | "Ppat_unpack"   | "Ppat_lazy"
      | "Ppat_type"       | "Ppat_constraint" | "Ppat_interval" | "Ppat_tuple" -> false
      | _ -> scan_args true args
    method list x = false
    method tuple x = false
    method string x = true
    method nativeint x = true
    method int x = true
    method int32 x = true
    method int64 x = true
    method char x = false
    method! lift_Location_t l = false
    method! lift_Parsetree_attributes l = false
  end

let parse_pattern str =
  try
    let pat = Parse.pattern (Lexing.from_string str) in
    if pattern_lifter#lift_Parsetree_pattern (pat) then Result.Ok pat
    else Result.Error ("Format error: " ^ str)
  with
  | Syntaxerr.Error _ -> Result.Error ("Syntax error: " ^ str)

(* Parsing fields *)

let parse_fields str =
  let e = List.fold_right ~init:[] ~f:(fun e acc -> [Bytes.trim e] @ acc) (String.split ~on:':' str) in
  match e with
  | [ "_" as pat ] ->
      begin match parse_pattern pat with
      | Result.Ok p -> Result.Ok (p, None, None)
      | Result.Error e -> Result.Error e
      end
  | [ pat; len ] ->
      begin match parse_pattern pat with
      | Result.Ok p ->
          begin match parse_expr len with
          | Result.Ok l -> Result.Ok (p, Some l, None)
          | Result.Error e -> Result.Error e
          end
        | Result.Error e -> Result.Error e
      end
  | [ pat; len; quals ] ->
      begin match parse_pattern pat with
      | Result.Ok p ->
          begin match parse_expr len with
          | Result.Ok l ->
              begin match parse_quals quals with
              | Result.Ok q -> Result.Ok (p, Some l, Some q)
              | Result.Error e -> Result.Error e
              end
          | Result.Error e -> Result.Error e
          end
        | Result.Error e -> Result.Error e
      end
  | _ -> Result.Error ("Format error: " ^ str)

(* Generators *)

let rec generate_fields (dat, off, len) beh = function
  | [] -> Result.Ok beh
  | hd :: tl ->
      begin match parse_fields hd with
      | Result.Ok (p, None, None) ->
          generate_fields (dat, off, len) beh tl
      | Result.Ok (p, Some l, q) ->
          let vl = mksym "value" and offNN = mksym "off" and lenNN = mksym "len" in
          begin match generate_fields (dat, off, len) beh tl with
          | Result.Ok next ->
              Result.Ok [%expr
                if [%e (mkident len)] >= [%e l] then
                  let [%p (mkpatvar vl)] = 0
                  and [%p (mkpatvar offNN)] = [%e (mkident off)] + [%e l]
                  and [%p (mkpatvar lenNN)] = [%e (mkident len)] - [%e l]
                  in match [%e (mkident vl)] with
                  | [%p p] when true -> [%e next]
                  | _ -> ()]
          | Result.Error e -> Result.Error e
          end
      | Result.Ok (_, _, _) -> Result.Error "Invalid format"
      | Result.Error e -> Result.Error e
      end

let generate_case (dat, off, len) case =
  match case.pc_lhs.ppat_desc with
  | Ppat_constant pattern ->
      begin match pattern with
      | Const_string (value, _) ->
          let fields = String.split ~on:';' value in
          generate_fields (dat, off, len) case.pc_rhs fields
      | _ -> Result.Error "Wrong pattern type in bitmatch case"
      end
    | _ -> Result.Error "Wrong pattern type in bitmatch case"

let generate_cases ident cases =
  let datN = mksym "data" and offN = mksym "off" and lenN = mksym "len" in
  let offNN = mksym "off" and lenNN = mksym "len" in
  let stmts = List.fold ~init:[] ~f:(fun acc case ->
    match generate_case (datN, offNN, lenNN) case with
    | Result.Ok v -> acc @ [v]
    | Result.Error r -> failwith r) cases
  in
  let rec build_seq = function
    | [] -> failwith "Empty case list"
    | [hd] -> hd
    | hd :: tl -> Exp.sequence hd (build_seq tl)
  in
  let seq = build_seq stmts in
  let tuple = [%pat? ([%p (mkpatvar datN)], [%p (mkpatvar offN)], [%p (mkpatvar lenN)])] in
  [%expr
    let [%p tuple] = [%e ident] in
    let [%p (mkpatvar offNN)] = [%e (mkident offN)]
    and [%p (mkpatvar lenNN)] = [%e (mkident lenN)]
    in [%e seq]]

let getenv_mapper argv =
  (* Our getenv_mapper only overrides the handling of expressions in the default mapper. *)
  { default_mapper with expr = fun mapper expr ->
    match expr with
    (* Is this an extension node? *)
    | { pexp_desc = Pexp_extension ({ txt = "bitstring"; loc }, pstr) } ->
        begin match pstr with
        (* Should have a single structure item, which is evaluation of a match expression *)
        | PStr [{ pstr_desc = Pstr_eval ( { pexp_loc = loc; pexp_desc =
          Pexp_match (ident, cases) }, _) }] -> generate_cases ident cases
        | _ ->
            raise (Location.Error (
              Location.error ~loc "[%getenv] accepts a string, e.g. [%getenv \"USER\"]"))
        end
    (* Delegate to the default mapper. *)
    | x -> default_mapper.expr mapper x;
  }

let () = register "getenv" getenv_mapper
