open Bitstring
open Printf

let swap bs =
  match%bitstring bs with
  | {| a : 1 : bitstring; b : 1 : bitstring|} ->
     [%bitstring {| b : 1 : bitstring; a : 1 : bitstring |}]
  | {| _ |} -> failwith "invalid input"

let one   = [%bitstring {| 1 : 2 |}]
let two   = [%bitstring {| 2 : 2 |}]
let three = [%bitstring {| 3 : 2 |}]

let () =
  assert(Bitstring.equals two (swap one));
  assert(Bitstring.equals one (swap two));
  assert(Bitstring.equals three (swap three));
  printf "PASSED\n"
