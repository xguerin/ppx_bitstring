open Bitstring
open Core.Std

let decode v =
  printf "hello";
  bitmatch v with
  | { 1 : 1;
      (1 | 2) as c : 64;
      a : 16 : bigendian, int;
      b : size : nativeendian, int;
      m : 11 : endian (a), unsigned, check (m > 10);
      s : -1 : string, save_offset_to (hello);
      p : -1 : bitstring
    } -> Some p
  | { a : 16 : bigendian, int;
      b : 16 : endian (a), int;
      _ : 16 : endian (a), int;
      p : -1 : bitstring
    } -> Some p
  | { _ } -> None
