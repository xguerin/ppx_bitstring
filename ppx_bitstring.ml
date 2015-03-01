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

let get_case_pattern case =
  match case.pc_lhs.ppat_desc with
  | Ppat_constant pattern ->
      begin match pattern with
      | Const_string (value, _) -> value
      | _ -> failwith "Wrong pattern type"
      end
  | _ -> failwith "Wrong pattern type"

let rec generate_case (dat, off, len) = function
  | [] -> failwith "Empty case list"
  | [hd] ->
      printf "%s\n" (get_case_pattern hd);
      hd.pc_rhs
  | hd :: tl ->
      printf "%s\n" (get_case_pattern hd);
      let beh = generate_case (dat, off, len) tl in
      let loc = hd.pc_lhs.ppat_loc and vl = mksym "value" in
      let pv = mkpatvar vl loc and iv = mkident vl loc in
      [%expr let [%p pv] = 0 in if [%e iv] = 0 then [%e hd.pc_rhs] else [%e beh]]

let generate_base ident loc cases =
  let datN = mksym "data" and offN = mksym "offset" and lenN = mksym "len" in
  let content = generate_case (datN, offN, lenN) cases in
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
        (* Should have a single structure item, which is evaluation of a match expression *)
        | PStr [{ pstr_desc = Pstr_eval ( { pexp_loc = loc; pexp_desc =
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
