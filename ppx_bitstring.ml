open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident
open Printf

let make_symbol =
  let i = ref 1000 in
  fun name ->
    incr i; let i = !i in
    sprintf "__pabitstring_%s_%d" name i

let generate_parse_error loc msg=
  Exp.apply (Exp.ident (Location.mkloc (Longident.parse "raise") loc)) [
    ("", (Exp.construct
      (Location.mkloc (Longident.parse "Bitstring.Construct_failure") loc)
      (Some (Exp.tuple [
        (Exp.constant (Const_string (msg, None)));
        (Exp.constant (Const_string (!Location.input_name, None)));
        (Exp.constant (Const_int 0));
        (Exp.constant (Const_int 0))
      ]
    ))))
  ]

let rec generate_case (dat, off, len) = function
  | [] -> None
  | hd :: tl ->
      let beh = match generate_case (dat, off, len) tl with
      | Some r -> r
      | None -> hd.pc_rhs
      in
      let value = make_symbol "value" in
      let e = Exp.let_ Nonrecursive
      [ Vb.mk
        (Pat.var (Location.mkloc value hd.pc_lhs.ppat_loc))
        (Exp.constant (Const_int 0))
      ]
      (Exp.ifthenelse (Exp.apply (Exp.ident (Location.mkloc (Longident.parse "=") hd.pc_lhs.ppat_loc)) [
        ("", Exp.ident (Location.mkloc (Longident.parse value) hd.pc_lhs.ppat_loc));
        ("", Exp.constant (Const_int 0))
      ]) beh (Some (Exp.constant (Const_int (-1)))))
      in
      Some e

let generate_base ident loc cases =
  let datN = make_symbol "data" and offN = make_symbol "offset" and lenN = make_symbol "len" in
  let content = match generate_case (datN, offN, lenN) cases with
  | Some c -> c
  | None -> raise (Location.Error (Location.error ~loc "[%bitstring] failed parsing bitmatch"))
  in
  Exp.let_ Nonrecursive
  [ Vb.mk
    (Pat.tuple [
      (Pat.var (Location.mkloc datN ident.pexp_loc));
      (Pat.var (Location.mkloc offN ident.pexp_loc));
      (Pat.var (Location.mkloc lenN ident.pexp_loc))
    ]) ident ]
  content

  (*
  [%expr function | [%e ident] -> 0 ]
  *)
  (*
  match cases with
  | []      -> Exp.ident ~loc ident
  | hd::tl  -> Exp.ident ~loc ident
  *)
  (*
  Exp.ident ~loc ident
  *)

let getenv_mapper argv =
  (* Our getenv_mapper only overrides the handling of expressions in the default mapper. *)
  { default_mapper with expr = fun mapper expr ->
    match expr with
    (* Is this an extension node? *)
    | { pexp_desc = Pexp_extension ({ txt = "bitstring"; loc }, pstr) } ->
        begin match pstr with
        (* Should have a single structure item, which is evaluation of a constant string. *)
        | PStr [{ pstr_desc =
          Pstr_eval ( { pexp_loc = loc; pexp_desc =
            Pexp_match (ident, cases) }, _) }] ->
              generate_base ident loc cases
        | _ ->
            raise (Location.Error (
              Location.error ~loc "[%getenv] accepts a string, e.g. [%getenv \"USER\"]"))
        end
    (* Delegate to the default mapper. *)
    | x -> default_mapper.expr mapper x;
  }

let () = register "getenv" getenv_mapper
