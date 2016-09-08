open OUnit2
open Bitstring

(*
 * Imbricated bitstring test
 *)

let imbricated_bistring_test context =
  let result  = "\xde\xad\xbe\xef\x42\x0a" in
  let magic   = "\xde\xad\xbe\xef" in
  let version = 0x42 in
  let data    = 10 in
  let header  = [%bitstring {| version : 8 |}] in
  let bits    = [%bitstring
    {| magic  : -1 : string
     ; header : -1 : bitstring
     ; data   :  8
     |}] in
  let dump = Bitstring.string_of_bitstring bits in
  assert_equal result dump

(*
 * Constructor style test
 *)

let constructor_style_test context =
  let%bitstring bits1 = {| "GIF87a" : 6*8 : string
                         ; 2145     : 16  : littleendian
                         ; 2145     : 16  : littleendian
                         ; true     : 1
                         ; 7        : 3
                         ; false    : 1
                         ; 7        : 3
                         ; 0        : 8
                         ; 0        : 8
                         |} in
  let bits2 = [%bitstring {| "GIF87a" : 6*8 : string
                           ; 2145     : 16  : littleendian
                           ; 2145     : 16  : littleendian
                           ; true     : 1
                           ; 7        : 3
                           ; false    : 1
                           ; 7        : 3
                           ; 0        : 8
                           ; 0        : 8
                           |}] in
  assert_bool "Bistrings are not equal" (Bitstring.equals bits1 bits2)

(*
 * Swap test
 *)

let swap bs =
  match%bitstring bs with
  | {| a : 1 : bitstring; b : 1 : bitstring|} ->
    [%bitstring {| b : 1 : bitstring; a : 1 : bitstring |}]
  | {| _ |} -> failwith "invalid input"

let swap_test context =
  let one   = [%bitstring {| 1 : 2 |}] in
  let two   = [%bitstring {| 2 : 2 |}] in
  let three = [%bitstring {| 3 : 2 |}] in
  assert_bool "Bitstring swap failed" (Bitstring.equals two   (swap one));
  assert_bool "Bitstring swap failed" (Bitstring.equals one   (swap two));
  assert_bool "Bitstring swap failed" (Bitstring.equals three (swap three))

(*
 * External value test
 *)

let external_value_test context =
  let result = "\x00\x02\x00\x00\x00\x01\xC0" in
  let int16_value = 2 in
  let int32_value = 1_l in
  let bool_value = true in
  let bits = [%bitstring {| int16_value : 16
                          ; int32_value : 32
                          ; 1           : 1
                          ; bool_value  : 1
                          ; 0           : 6
                          |}] in
  let str = Bitstring.string_of_bitstring bits in
  assert_equal str result

(*
 * Test suite definition
 *)

let suite = "BitstringConstructorTest" >::: [
    "imbricated_bistring_test"  >:: imbricated_bistring_test;
    "constructor_style_test"    >:: constructor_style_test;
    "swap_test"                 >:: swap_test;
    "external_value_test"       >:: external_value_test
  ]

let () = run_test_tt_main suite
