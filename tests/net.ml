open Bitstring
open Printf

let buildUDP src dst len chk =
  let%bitstring udp = {|
    src : 16 : bigendian;
    dst : 16 : bigendian;
    len : 16 : bigendian;
    chk : 16 : bigendian
  |} in udp

let buildIP ihl len proto chk (s0, s1, s2, s3) (d0, d1, d2, d3) pld =
  let%bitstring ipv4 = {|
    4     : 4;
    ihl   : 4;
    0     : 6; (* dscp *)
    2     : 2; (* ecn *)
    len   : 16  : bigendian;
    0     : 16  : bigendian; (* ident *)
    0     : 3; (* flags *)
    0     : 13  : bigendian; (* fragment offset *)
    0     : 8; (* ttl *)
    proto : 8;
    chk   : 16  : bigendian; (* checksum *)
    s0    : 8; s1    : 8; s2    : 8; s3    : 8;
    d0    : 8; d1    : 8; d2    : 8; d3    : 8;
    pld   : (len - ihl * 4) * 8 : bitstring
  |} in ipv4

let () =
  let udp = buildUDP 0x1000 0x1000 0 0 in
  let srcip = (0x0A, 0x00, 0x00, 0x01) in
  let dstip = (0x0A, 0x00, 0x00, 0x02) in
  let ip  = buildIP 5 28 0x11 0 srcip dstip udp in
  Bitstring.hexdump_bitstring stdout ip;
  match%bitstring ip with
  | {| 4    : 4;
       5    : 4;
       0    : 6; (* dscp *)
       2    : 2; (* ecn *)
       28   : 16  : bigendian;
       0    : 16  : bigendian; (* ident *)
       0    : 3; (* flags *)
       0    : 13  : bigendian; (* fragment offset *)
       0    : 8; (* ttl *)
       0x11 : 8;
       0    : 16  : bigendian; (* checksum *)
       0x0A : 8; 0x00 : 8; 0x00 : 8; 0x01 : 8;
       0x0A : 8; 0x00 : 8; 0x00 : 8; 0x02 : 8;
       _    : 64  : bitstring
    |} ->
      Printf.printf "Decoding passed\n"
  | {| _ |} ->
    Printf.printf "Decoding failed\n"

