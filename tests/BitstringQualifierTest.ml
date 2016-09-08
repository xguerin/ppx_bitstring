open OUnit2
open Bitstring

(*
 * Test of the map() qualifier
 *)

let map_parse_test context =
  let source = [%bitstring {| 1 : 16 ; 2 : 16 |}] in
  match%bitstring source with
  | {| value0 : 16 : map (fun v -> v + 1)
     ; value1 : 16 : map (fun v -> Result.Ok (v))
    |} ->
    assert_equal value0 2;
    begin match value1 with
      | Result.Ok v -> assert_equal v 2
      | _           -> assert_bool "Invalid map result" false
    end
  | {| _ |} -> assert_bool "Invalid pattern" false

(*
 * Test suite definition
 *)

let suite = "BitstringQualifierTest" >::: [
    "map_parse"   >:: map_parse_test
  ]

let () = run_test_tt_main suite
