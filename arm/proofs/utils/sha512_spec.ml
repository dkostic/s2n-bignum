(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of SHA-512 (FIPS 180-4).                                    *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Round constants K_t for t = 0..79 (FIPS 180-4, Section 4.2.3).           *)
(* First 64 bits of the fractional parts of the cube roots of the first 80  *)
(* prime numbers.                                                            *)
(* ------------------------------------------------------------------------- *)

let sha512_K = define
 `sha512_K : int64 list =
   [word 0x428a2f98d728ae22; word 0x7137449123ef65cd;
    word 0xb5c0fbcfec4d3b2f; word 0xe9b5dba58189dbbc;
    word 0x3956c25bf348b538; word 0x59f111f1b605d019;
    word 0x923f82a4af194f9b; word 0xab1c5ed5da6d8118;
    word 0xd807aa98a3030242; word 0x12835b0145706fbe;
    word 0x243185be4ee4b28c; word 0x550c7dc3d5ffb4e2;
    word 0x72be5d74f27b896f; word 0x80deb1fe3b1696b1;
    word 0x9bdc06a725c71235; word 0xc19bf174cf692694;
    word 0xe49b69c19ef14ad2; word 0xefbe4786384f25e3;
    word 0x0fc19dc68b8cd5b5; word 0x240ca1cc77ac9c65;
    word 0x2de92c6f592b0275; word 0x4a7484aa6ea6e483;
    word 0x5cb0a9dcbd41fbd4; word 0x76f988da831153b5;
    word 0x983e5152ee66dfab; word 0xa831c66d2db43210;
    word 0xb00327c898fb213f; word 0xbf597fc7beef0ee4;
    word 0xc6e00bf33da88fc2; word 0xd5a79147930aa725;
    word 0x06ca6351e003826f; word 0x142929670a0e6e70;
    word 0x27b70a8546d22ffc; word 0x2e1b21385c26c926;
    word 0x4d2c6dfc5ac42aed; word 0x53380d139d95b3df;
    word 0x650a73548baf63de; word 0x766a0abb3c77b2a8;
    word 0x81c2c92e47edaee6; word 0x92722c851482353b;
    word 0xa2bfe8a14cf10364; word 0xa81a664bbc423001;
    word 0xc24b8b70d0f89791; word 0xc76c51a30654be30;
    word 0xd192e819d6ef5218; word 0xd69906245565a910;
    word 0xf40e35855771202a; word 0x106aa07032bbd1b8;
    word 0x19a4c116b8d2d0c8; word 0x1e376c085141ab53;
    word 0x2748774cdf8eeb99; word 0x34b0bcb5e19b48a8;
    word 0x391c0cb3c5c95a63; word 0x4ed8aa4ae3418acb;
    word 0x5b9cca4f7763e373; word 0x682e6ff3d6b2b8a3;
    word 0x748f82ee5defb2fc; word 0x78a5636f43172f60;
    word 0x84c87814a1f0ab72; word 0x8cc702081a6439ec;
    word 0x90befffa23631e28; word 0xa4506cebde82bde9;
    word 0xbef9a3f7b2c67915; word 0xc67178f2e372532b;
    word 0xca273eceea26619c; word 0xd186b8c721c0c207;
    word 0xeada7dd6cde0eb1e; word 0xf57d4f7fee6ed178;
    word 0x06f067aa72176fba; word 0x0a637dc5a2c898a6;
    word 0x113f9804bef90dae; word 0x1b710b35131c471b;
    word 0x28db77f523047d84; word 0x32caab7b40c72493;
    word 0x3c9ebe0a15c9bebc; word 0x431d67c49c100d4c;
    word 0x4cc5d4becb3e42b6; word 0x597f299cfc657e2a;
    word 0x5fcb6fab3ad6faec; word 0x6c44198c4a475817]`;;

(* ------------------------------------------------------------------------- *)
(* Initial hash value H0 (FIPS 180-4, Section 5.3.5).                       *)
(* First 64 bits of the fractional parts of the square roots of the first 8  *)
(* prime numbers.                                                            *)
(* ------------------------------------------------------------------------- *)

let sha512_H0 = define
 `sha512_H0 : int64 list =
   [word 0x6a09e667f3bcc908; word 0xbb67ae8584caa73b;
    word 0x3c6ef372fe94f82b; word 0xa54ff53a5f1d36f1;
    word 0x510e527fade682d1; word 0x9b05688c2b3e6c1f;
    word 0x1f83d9abfb41bd6b; word 0x5be0cd19137e2179]`;;

(* ------------------------------------------------------------------------- *)
(* SHA-512 logical functions (FIPS 180-4, Section 4.1.3).                    *)
(* ------------------------------------------------------------------------- *)

(* Ch(x,y,z) = (x AND y) XOR (NOT x AND z) [Eq. 4.8] *)
let sha512_Ch = new_definition
 `sha512_Ch (x:int64) (y:int64) (z:int64) : int64 =
    word_xor (word_and x y) (word_and (word_not x) z)`;;

(* Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z) [Eq. 4.9] *)
let sha512_Maj = new_definition
 `sha512_Maj (x:int64) (y:int64) (z:int64) : int64 =
    word_xor (word_and x y) (word_xor (word_and x z) (word_and y z))`;;

(* SIGMA_0(x) = ROTR^28(x) XOR ROTR^34(x) XOR ROTR^39(x) [Eq. 4.10] *)
let sha512_Sigma0 = new_definition
 `sha512_Sigma0 (x:int64) : int64 =
    word_xor (word_ror x 28) (word_xor (word_ror x 34) (word_ror x 39))`;;

(* SIGMA_1(x) = ROTR^14(x) XOR ROTR^18(x) XOR ROTR^41(x) [Eq. 4.11] *)
let sha512_Sigma1 = new_definition
 `sha512_Sigma1 (x:int64) : int64 =
    word_xor (word_ror x 14) (word_xor (word_ror x 18) (word_ror x 41))`;;

(* sigma_0(x) = ROTR^1(x) XOR ROTR^8(x) XOR SHR^7(x) [Eq. 4.12] *)
let sha512_sigma0 = new_definition
 `sha512_sigma0 (x:int64) : int64 =
    word_xor (word_ror x 1) (word_xor (word_ror x 8) (word_ushr x 7))`;;

(* sigma_1(x) = ROTR^19(x) XOR ROTR^61(x) XOR SHR^6(x) [Eq. 4.13] *)
let sha512_sigma1 = new_definition
 `sha512_sigma1 (x:int64) : int64 =
    word_xor (word_ror x 19) (word_xor (word_ror x 61) (word_ushr x 6))`;;

(* ------------------------------------------------------------------------- *)
(* Message schedule W_t for t = 0..79 (FIPS 180-4, Section 6.4.2).          *)
(*                                                                           *)
(* Given a 16-word message block M, the schedule extends it to 80 words:     *)
(*   W_t = M_t                                             for 0 <= t <= 15  *)
(*   W_t = sigma_1(W_{t-2}) + W_{t-7} + sigma_0(W_{t-15}) + W_{t-16}       *)
(*                                                         for 16 <= t <= 79 *)
(*                                                                           *)
(* sha512_message_schedule n M produces a list of (n + 16) words:            *)
(*   sha512_message_schedule 0 M = M                    (16 words)           *)
(*   sha512_message_schedule 64 M = full schedule       (80 words)           *)
(* ------------------------------------------------------------------------- *)

let sha512_extend_schedule = new_definition
 `sha512_extend_schedule (W:int64 list) (n:num) : int64 list =
    APPEND W
      [word_add (sha512_sigma1 (EL (n + 14) W))
                (word_add (EL (n + 9) W)
                          (word_add (sha512_sigma0 (EL (n + 1) W))
                                    (EL n W)))]`;;

let sha512_message_schedule = define
 `sha512_message_schedule 0 (M:int64 list) = M /\
  sha512_message_schedule (n + 1) M =
    sha512_extend_schedule (sha512_message_schedule n M) n`;;

(* ------------------------------------------------------------------------- *)
(* Compression function (FIPS 180-4, Section 6.4.2, Steps 2-3).             *)
(*                                                                           *)
(* State is [a; b; c; d; e; f; g; h] where a is the first working variable. *)
(*                                                                           *)
(* Each round computes:                                                      *)
(*   T1 = h + SIGMA_1(e) + Ch(e,f,g) + K_t + W_t                           *)
(*   T2 = SIGMA_0(a) + Maj(a,b,c)                                           *)
(*   new state = [T1+T2; a; b; c; d+T1; e; f; g]                            *)
(* ------------------------------------------------------------------------- *)

let sha512_compress_round = new_definition
 `sha512_compress_round (K_t:int64) (W_t:int64) (state:int64 list) : int64 list =
    let a = EL 0 state and b = EL 1 state and c = EL 2 state and d = EL 3 state
    and e = EL 4 state and f = EL 5 state and g = EL 6 state and h = EL 7 state in
    let T1 = word_add h (word_add (sha512_Sigma1 e)
                                  (word_add (sha512_Ch e f g)
                                            (word_add K_t W_t))) in
    let T2 = word_add (sha512_Sigma0 a) (sha512_Maj a b c) in
    [word_add T1 T2; a; b; c; word_add d T1; e; f; g]`;;

let sha512_compress = define
 `sha512_compress 0 W state = state /\
  sha512_compress (n + 1) W state =
    sha512_compress_round (EL n sha512_K) (EL n W)
                          (sha512_compress n W state)`;;

(* ------------------------------------------------------------------------- *)
(* Block processing (FIPS 180-4, Section 6.4.2, Step 4).                     *)
(*                                                                           *)
(* Process a single 1024-bit message block (16 64-bit words):                *)
(*   1. Compute the 80-word message schedule                                 *)
(*   2. Run 80 rounds of compression                                         *)
(*   3. Add compressed state to input hash                                   *)
(* ------------------------------------------------------------------------- *)

let sha512_block = new_definition
 `sha512_block (msg_block:int64 list) (hash:int64 list) : int64 list =
    let W = sha512_message_schedule 64 msg_block in
    let compressed = sha512_compress 80 W hash in
    MAP2 word_add compressed hash`;;

(* ------------------------------------------------------------------------- *)
(* Multi-block iteration (FIPS 180-4, Section 6.4.2).                        *)
(*                                                                           *)
(* sha512_hash_blocks n blocks H applies sha512_block iteratively:           *)
(*   sha512_hash_blocks 0 blocks H = H                                      *)
(*   sha512_hash_blocks (n+1) blocks H =                                    *)
(*     sha512_block (EL n blocks) (sha512_hash_blocks n blocks H)           *)
(* ------------------------------------------------------------------------- *)

let sha512_hash_blocks = define
 `sha512_hash_blocks 0 blocks H = H /\
  sha512_hash_blocks (n + 1) blocks H =
    sha512_block (EL n blocks) (sha512_hash_blocks n blocks H)`;;
