open Bitstring
open Core.Std

let decode v =
  match%bitstring v with
  | {|  1       : 1;
        (1 | 2) : 2;
        a       : 16 : bigendian, int;
        m       : 16 : endian (Bitstring.LittleEndian), check (m > 10);
        _       : -1 : string;
        p       : -1 : bitstring
    |} -> Some p
  | {| a        : 16 : bigendian, int;
        b       : 16 : endian (Bitstring.BigEndian), int;
        _       : 16 : endian (Bitstring.NativeEndian), int;
        p       : -1 : bitstring
    |} -> Some p
  | {| _ |} -> None
