open Bitstring
open Printf

let magic    = "\xde\xad\xbe\xef"
let version  = 0x42
let data     = 10

let () =
  let header = let%bitstring header = {| version : 8 |} in header in
  let bits =
    let%bitstring bits =
      {| magic  : -1 : string
       ; header : -1 : bitstring
       ; data   :  8
       |}
    in
    bits
  in
  Bitstring.hexdump_bitstring stdout bits;
  let bits2 = let%bitstring bits2 = {| magic : -1 : string |} in bits2 in
  Bitstring.hexdump_bitstring stdout bits2
;;
