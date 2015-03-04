open Bitstring
open Core.Std

let decode v =
  printf "hello";
  bitmatch v with
  | { 1 : 1;
      (1 | 2) as c : 2;
      a : 16 : bigendian, int;
      m : 16 : endian (a);
      s : -1 : string;
      p : -1 : bitstring
    } -> Some p
  | { 0 : 1;
      (1 | 2) : 2;
      a : 16 : bigendian, int;
      b : 16 : endian (a), int;
      _ : 16 : endian (a), int;
      p : -1 : bitstring
    } -> Some p
  | { _ } -> None
