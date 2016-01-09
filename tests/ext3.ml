open Bitstring
open Printf

let bits = Bitstring.bitstring_of_file "ext3_sb"

let () =
	match%bitstring bits with
	 | {| s_inodes_count : 32 : littleendian;       (* Inodes count *)
			s_blocks_count : 32 : littleendian;       (* Blocks count *)
			s_r_blocks_count : 32 : littleendian;     (* Reserved blocks count *)
			s_free_blocks_count : 32 : littleendian;  (* Free blocks count *)
			s_free_inodes_count : 32 : littleendian;  (* Free inodes count *)
			s_first_data_block : 32 : littleendian;   (* First Data Block *)
			s_log_block_size : 32 : littleendian;     (* Block size *)
			s_log_frag_size : 32 : littleendian;      (* Fragment size *)
			s_blocks_per_group : 32 : littleendian;   (* # Blocks per group *)
			s_frags_per_group : 32 : littleendian;    (* # Fragments per group *)
			s_inodes_per_group : 32 : littleendian;   (* # Inodes per group *)
			s_mtime : 32 : littleendian;              (* Mount time *)
			s_wtime : 32 : littleendian;              (* Write time *)
			s_mnt_count : 16 : littleendian;          (* Mount count *)
			s_max_mnt_count : 16 : littleendian;      (* Maximal mount count *)
			0xef53 : 16 : littleendian |} ->           (* Magic signature *)

		printf "ext3 superblock:\n";
		printf "  s_inodes_count = %ld\n" s_inodes_count;
		printf "  s_blocks_count = %ld\n" s_blocks_count;
		printf "  s_free_inodes_count = %ld\n" s_free_inodes_count;
		printf "  s_free_blocks_count = %ld\n" s_free_blocks_count

	| {| _ |} ->
		eprintf "not an ext3 superblock!\n%!";
		exit 2
