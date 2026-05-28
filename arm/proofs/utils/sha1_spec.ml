(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of SHA-1 (FIPS 180-4).                                      *)
(*                                                                           *)
(* This file is the reference specification: it must agree with FIPS 180-4   *)
(* and with the Cryptol reference at                                         *)
(*   cryptol-specs/Primitive/Keyless/Hash/SHA1/Specification.cry             *)
(* It is intentionally decoupled from arm/proofs/sha1.ml (the ARM HW         *)
(* operator semantics); the bridge is built in arm/proofs/utils/             *)
(* sha1_bridge.ml (Phase 2).                                                 *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* SHA-1 logical functions f_t (FIPS 180-4, Section 4.1.1).                 *)
(*                                                                           *)
(* Ch(x,y,z)     = (x AND y) XOR (NOT x AND z)        [Eq. 4.1]             *)
(* Parity(x,y,z) = x XOR y XOR z                       [Eq. 4.2]             *)
(* Maj(x,y,z)    = (x AND y) XOR (x AND z) XOR (y AND z) [Eq. 4.3]          *)
(* ------------------------------------------------------------------------- *)

let sha1_Ch = new_definition
 `sha1_Ch (x:int32) (y:int32) (z:int32) : int32 =
    word_xor (word_and x y) (word_and (word_not x) z)`;;

let sha1_Parity = new_definition
 `sha1_Parity (x:int32) (y:int32) (z:int32) : int32 =
    word_xor x (word_xor y z)`;;

let sha1_Maj = new_definition
 `sha1_Maj (x:int32) (y:int32) (z:int32) : int32 =
    word_xor (word_and x y) (word_xor (word_and x z) (word_and y z))`;;

(* ------------------------------------------------------------------------- *)
(* Round-function selector (FIPS 180-4, Section 4.1.1, Eq. 4.1-4.4).        *)
(*                                                                           *)
(* For round t = 0..79 the SHA-1 compression uses:                          *)
(*    f_t(b,c,d) = Ch(b,c,d)      0  <= t <= 19                             *)
(*    f_t(b,c,d) = Parity(b,c,d) 20  <= t <= 39                             *)
(*    f_t(b,c,d) = Maj(b,c,d)    40  <= t <= 59                             *)
(*    f_t(b,c,d) = Parity(b,c,d) 60  <= t <= 79                             *)
(* ------------------------------------------------------------------------- *)

let sha1_f = new_definition
 `sha1_f (t:num) (b:int32) (c:int32) (d:int32) : int32 =
    if t < 20 then sha1_Ch b c d
    else if t < 40 then sha1_Parity b c d
    else if t < 60 then sha1_Maj b c d
    else sha1_Parity b c d`;;

(* ------------------------------------------------------------------------- *)
(* Round constants K_t (FIPS 180-4, Section 4.2.1).                          *)
(* ------------------------------------------------------------------------- *)

let sha1_K = new_definition
 `sha1_K (t:num) : int32 =
    if t < 20 then word 0x5a827999
    else if t < 40 then word 0x6ed9eba1
    else if t < 60 then word 0x8f1bbcdc
    else word 0xca62c1d6`;;

(* ------------------------------------------------------------------------- *)
(* Initial hash value H[0..4] (FIPS 180-4, Section 5.3.1).                  *)
(* ------------------------------------------------------------------------- *)

let sha1_init_hash = new_definition
 `sha1_init_hash : int32 list =
   [word 0x67452301; word 0xefcdab89; word 0x98badcfe;
    word 0x10325476; word 0xc3d2e1f0]`;;

(* ------------------------------------------------------------------------- *)
(* Message schedule W_t (FIPS 180-4, Section 6.1.2 step 1).                 *)
(*                                                                           *)
(* Given a 16-word message block M, the schedule extends to 80 words:       *)
(*   W_t = M_t                                       for 0  <= t <= 15      *)
(*   W_t = ROL_1(W_{t-3} XOR W_{t-8} XOR W_{t-14}                          *)
(*               XOR W_{t-16})                       for 16 <= t <= 79      *)
(*                                                                           *)
(* sha1_message_schedule n M produces a list of (n + 16) words; in          *)
(* particular sha1_message_schedule 64 M is the full 80-word schedule.      *)
(* When sha1_message_schedule (n+1) M is reduced, the next-extended index t *)
(* is t = 16 + n, so the recurrence reads                                   *)
(*   W_{16+n} = ROL_1(W_{n+13} XOR W_{n+8} XOR W_{n+2} XOR W_n).            *)
(* ------------------------------------------------------------------------- *)

let sha1_extend_schedule = new_definition
 `sha1_extend_schedule (W:int32 list) (n:num) : int32 list =
    APPEND W
      [word_rol
         (word_xor (EL (n + 13) W)
            (word_xor (EL (n + 8) W)
               (word_xor (EL (n + 2) W) (EL n W))))
         1]`;;

let sha1_message_schedule = define
 `sha1_message_schedule 0 (M:int32 list) = M /\
  sha1_message_schedule (n + 1) M =
    sha1_extend_schedule (sha1_message_schedule n M) n`;;

let sha1_block_message_schedule = new_definition
 `sha1_block_message_schedule (M:int32 list) : int32 list =
    sha1_message_schedule 64 M`;;

(* ------------------------------------------------------------------------- *)
(* Compression function (FIPS 180-4, Section 6.1.2 steps 2-3).              *)
(*                                                                           *)
(* State is [a; b; c; d; e] where a is the first working variable.          *)
(*                                                                           *)
(* Each round computes:                                                      *)
(*    T = ROL_5(a) + f_t(b,c,d) + e + K_t + W_t                             *)
(*    new state = [T; a; ROL_30(b); c; d]                                   *)
(* ------------------------------------------------------------------------- *)

let sha1_compress_round = new_definition
 `sha1_compress_round (t:num) (W_t:int32) (state:int32 list) : int32 list =
    let a = EL 0 state and b = EL 1 state and c = EL 2 state
    and d = EL 3 state and e = EL 4 state in
    let T = word_add (word_rol a 5)
              (word_add (sha1_f t b c d)
                 (word_add e
                    (word_add (sha1_K t) W_t))) in
    [T; a; word_rol b 30; c; d]`;;

let sha1_compress = define
 `sha1_compress 0 W state = state /\
  sha1_compress (n + 1) W state =
    sha1_compress_round n (EL n W) (sha1_compress n W state)`;;

(* ------------------------------------------------------------------------- *)
(* Block processing (FIPS 180-4, Section 6.1.2 step 4).                     *)
(*                                                                           *)
(* Process one 512-bit (16-word) message block:                              *)
(*   1. Compute the 80-word message schedule.                                *)
(*   2. Run 80 rounds of compression.                                        *)
(*   3. Add (mod 2^32) the compressed state to the input hash.              *)
(* ------------------------------------------------------------------------- *)

let sha1_block_compress = new_definition
 `sha1_block_compress (msg_block:int32 list) (hash:int32 list) : int32 list =
    let W = sha1_block_message_schedule msg_block in
    let compressed = sha1_compress 80 W hash in
    MAP2 word_add compressed hash`;;

(* ------------------------------------------------------------------------- *)
(* Multi-block iteration (FIPS 180-4, Section 6.1.2).                       *)
(*                                                                           *)
(*   sha1_hash_blocks 0       blocks H = H                                   *)
(*   sha1_hash_blocks (n + 1) blocks H =                                     *)
(*     sha1_block_compress (EL n blocks) (sha1_hash_blocks n blocks H)       *)
(* ------------------------------------------------------------------------- *)

let sha1_hash_blocks = define
 `sha1_hash_blocks 0 blocks H = H /\
  sha1_hash_blocks (n + 1) blocks H =
    sha1_block_compress (EL n blocks) (sha1_hash_blocks n blocks H)`;;

(* ------------------------------------------------------------------------- *)
(* Byte-level entry point (Phase 9).                                         *)
(*                                                                           *)
(* The HW implementation works on whole 64-byte blocks: it does not pad or   *)
(* length-tag (FIPS one-shot hash padding is the higher-level caller's job). *)
(* This section defines:                                                     *)
(*   - sha1_word_be           : 4 bytes (big-endian) -> int32                *)
(*   - sha1_block_from_bytes  : 64 bytes -> int32 list of length 16          *)
(*   - sha1_blocks_from_bytes : n*64 bytes -> int32 list list of length n    *)
(*   - sha1_hash_bytes        : the public spec                               *)
(*                                                                           *)
(* FIPS 180-4 §6.1.2 reads the 16 message-block words `M_t` as 4 big-endian  *)
(* bytes each; word_bytereverse converts the native little-endian            *)
(* interpretation of `read (memory :> bytes32 _)` to that big-endian form.   *)
(* ------------------------------------------------------------------------- *)

(* sha1_word_be packs 4 bytes (b0,b1,b2,b3) -> b0||b1||b2||b3 as a 32-bit  *)
(* big-endian word: i.e. b0 is the most-significant byte. Equivalent to a   *)
(* word-bytereverse of the natural little-endian num_of_bytelist read.      *)
let sha1_word_be = new_definition
 `sha1_word_be (b0:byte) (b1:byte) (b2:byte) (b3:byte) : int32 =
    word_bytereverse (word(num_of_bytelist [b0;b1;b2;b3]):int32)`;;

(* The j-th block word (j=0..15) of an n*64-byte buffer, in FIPS big-endian  *)
(* form: bytes bs[64*i+4*j..64*i+4*j+3] form one big-endian int32.           *)
let sha1_block_word = new_definition
 `sha1_block_word (i:num) (j:num) (bs:byte list) : int32 =
    sha1_word_be (EL (64*i + 4*j + 0) bs)
                 (EL (64*i + 4*j + 1) bs)
                 (EL (64*i + 4*j + 2) bs)
                 (EL (64*i + 4*j + 3) bs)`;;

(* The 16-word i-th block of an n*64-byte buffer. *)
let sha1_block_from_bytes = new_definition
 `sha1_block_from_bytes (i:num) (bs:byte list) : int32 list =
    [sha1_block_word i  0 bs; sha1_block_word i  1 bs;
     sha1_block_word i  2 bs; sha1_block_word i  3 bs;
     sha1_block_word i  4 bs; sha1_block_word i  5 bs;
     sha1_block_word i  6 bs; sha1_block_word i  7 bs;
     sha1_block_word i  8 bs; sha1_block_word i  9 bs;
     sha1_block_word i 10 bs; sha1_block_word i 11 bs;
     sha1_block_word i 12 bs; sha1_block_word i 13 bs;
     sha1_block_word i 14 bs; sha1_block_word i 15 bs]`;;

(* Iterated multi-block view: split n*64 bytes into n int32-list blocks. *)
let sha1_blocks_from_bytes = define
 `sha1_blocks_from_bytes 0 bs = [] /\
  sha1_blocks_from_bytes (n + 1) bs =
    APPEND (sha1_blocks_from_bytes n bs)
           [sha1_block_from_bytes n bs]`;;

(* Hash an n*64-byte buffer (whole-blocks-only, no padding/length-tagging). *)
let sha1_hash_bytes = new_definition
 `sha1_hash_bytes (num_blocks:num) (bs:byte list) (H:int32 list)
                  : int32 list =
    sha1_hash_blocks num_blocks (sha1_blocks_from_bytes num_blocks bs) H`;;
