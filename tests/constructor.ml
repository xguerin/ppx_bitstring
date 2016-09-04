open Bitstring
open Printf

let a = 0x23
let b = 0x42

let print_input () =
  let%bitstring a = {| a : 8 |}
  and b = {| b : 8 |}
  in
  Bitstring.hexdump_bitstring stdout a;
  Bitstring.hexdump_bitstring stdout b;
;;

let () =
  print_input ();
  let bits1 = [%bitstring {| a : 8 |}] in
  let%bitstring bits2 = {| b : 16 |} in
  Bitstring.hexdump_bitstring stdout bits1;
  Bitstring.hexdump_bitstring stdout bits2
