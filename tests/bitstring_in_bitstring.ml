open Bitstring
open Printf

let magic    = "\xde\xad\xbe\xef"
let version  = 0x42
let data     = 10

let () =
  let header = [%bitstring {| version : 8 |}] in
  let bits =
    [%bitstring
      {| magic  : -1 : string
       ; header : -1 : bitstring
       ; data   :  8
       |}]
  in
  Bitstring.hexdump_bitstring stdout bits;
  let bits2 = [%bitstring {| magic : -1 : string |}] in
  Bitstring.hexdump_bitstring stdout bits2
;;
