open Bitstring
open Core.Std

let decode v =
  printf "hello";
  match%bitstring v with
  | {| 1 : 1;
      (1 | 2)  : 2;
      a : 16 : bigendian, int;
      m : 16 : endian (a), check (m > 10);
      _ : -1 : string;
      p : -1 : bitstring
    |} -> Some p
  | {| a : 16 : bigendian, int;
      b : 16 : endian (a), int;
      _ : 16 : endian (a), int;
      p : -1 : bitstring
    |} -> Some p
  | {| _ |} -> None
