open Bitstring
open Printf

let a = 0x23
let b = 0x42

let () =
  let bits1 = [%bitstring {| a : 8 |}]  in
  let bits2 = [%bitstring {| b : 16 |}] in
  Bitstring.hexdump_bitstring stdout bits1;
  Bitstring.hexdump_bitstring stdout bits2
