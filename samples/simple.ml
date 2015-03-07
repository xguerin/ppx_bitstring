open Bitstring
open Core.Std

let decode v =
  printf "hello";
  match%bitstring v with
  | {| 1 : 1;
      (1 | 2) as c : 2;
      a : 16 : bigendian, int;
      m : size : endian (a), check (m > 10);
      s : -1 : string, save_offset_to (hello);
      p : -1 : bitstring
    |} -> Some p
  | {| a : 16 : bigendian, int;
      b : 16 : endian (a), int;
      _ : 16 : endian (a), int;
      p : -1 : bitstring
    |} -> Some p
  | {| _ |} -> None
