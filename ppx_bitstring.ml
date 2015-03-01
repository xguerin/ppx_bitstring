open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident
open Printf

let mksym =
  let i = ref 1000 in
  fun name ->
    incr i; let i = !i in
    sprintf "__pabitstring_%s_%d" name i

let mkpatvar name loc =
  Pat.var (Location.mkloc name loc)

let mkident name loc =
  Exp.ident (Location.mkloc (Longident.parse name) loc)

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
      let loc = hd.pc_lhs.ppat_loc and vl = mksym "value" in
      let pv = mkpatvar vl loc and iv = mkident vl loc in
      Some [%expr let [%p pv] = 0 in if [%e iv] = 0 then [%e beh] else -1]

let generate_base ident loc cases =
  let datN = mksym "data" and offN = mksym "offset" and lenN = mksym "len" in
  let content = match generate_case (datN, offN, lenN) cases with
  | Some c -> c
  | None -> raise (Location.Error (Location.error ~loc "[%bitstring] failed parsing bitmatch"))
  in
  let pa = mkpatvar datN loc and pb = mkpatvar offN loc and pc = mkpatvar lenN loc in
  let tuple = [%pat? ([%p pa], [%p pb], [%p pc])] in
  [%expr let [%p tuple] = [%e ident] in [%e content]]

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
