open Bitstring
open Printf

let _ =
  let version = 1 in
  let data = 10 in
  let%bitstring bits = {|
    version : 4;
    data : 12
  |} in
  Bitstring.hexdump_bitstring stdout bits
