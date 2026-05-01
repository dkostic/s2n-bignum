(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of SHA-256 (FIPS 180-4).                                    *)
(*                                                                           *)
(* Architecture-agnostic; used by both arm/ and x86/ correctness proofs.     *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Round constants K_t for t = 0..63 (FIPS 180-4, Section 4.2.2).           *)
(* First 32 bits of the fractional parts of the cube roots of the first 64   *)
(* prime numbers.                                                            *)
(* ------------------------------------------------------------------------- *)

let sha256_K = define
 `sha256_K : int32 list =
   [word 0x428a2f98; word 0x71374491; word 0xb5c0fbcf; word 0xe9b5dba5;
    word 0x3956c25b; word 0x59f111f1; word 0x923f82a4; word 0xab1c5ed5;
    word 0xd807aa98; word 0x12835b01; word 0x243185be; word 0x550c7dc3;
    word 0x72be5d74; word 0x80deb1fe; word 0x9bdc06a7; word 0xc19bf174;
    word 0xe49b69c1; word 0xefbe4786; word 0x0fc19dc6; word 0x240ca1cc;
    word 0x2de92c6f; word 0x4a7484aa; word 0x5cb0a9dc; word 0x76f988da;
    word 0x983e5152; word 0xa831c66d; word 0xb00327c8; word 0xbf597fc7;
    word 0xc6e00bf3; word 0xd5a79147; word 0x06ca6351; word 0x14292967;
    word 0x27b70a85; word 0x2e1b2138; word 0x4d2c6dfc; word 0x53380d13;
    word 0x650a7354; word 0x766a0abb; word 0x81c2c92e; word 0x92722c85;
    word 0xa2bfe8a1; word 0xa81a664b; word 0xc24b8b70; word 0xc76c51a3;
    word 0xd192e819; word 0xd6990624; word 0xf40e3585; word 0x106aa070;
    word 0x19a4c116; word 0x1e376c08; word 0x2748774c; word 0x34b0bcb5;
    word 0x391c0cb3; word 0x4ed8aa4a; word 0x5b9cca4f; word 0x682e6ff3;
    word 0x748f82ee; word 0x78a5636f; word 0x84c87814; word 0x8cc70208;
    word 0x90befffa; word 0xa4506ceb; word 0xbef9a3f7; word 0xc67178f2]`;;

(* ------------------------------------------------------------------------- *)
(* Initial hash value H0 (FIPS 180-4, Section 5.3.3).                       *)
(* First 32 bits of the fractional parts of the square roots of the first 8  *)
(* prime numbers.                                                            *)
(* ------------------------------------------------------------------------- *)

let sha256_H0 = define
 `sha256_H0 : int32 list =
   [word 0x6a09e667; word 0xbb67ae85; word 0x3c6ef372; word 0xa54ff53a;
    word 0x510e527f; word 0x9b05688c; word 0x1f83d9ab; word 0x5be0cd19]`;;

(* ------------------------------------------------------------------------- *)
(* SHA-256 logical functions (FIPS 180-4, Section 4.1.2).                    *)
(* ------------------------------------------------------------------------- *)

(* Ch(x,y,z) = (x AND y) XOR (NOT x AND z) [Eq. 4.2] *)
let sha256_Ch = new_definition
 `sha256_Ch (x:int32) (y:int32) (z:int32) : int32 =
    word_xor (word_and x y) (word_and (word_not x) z)`;;

(* Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z) [Eq. 4.3] *)
let sha256_Maj = new_definition
 `sha256_Maj (x:int32) (y:int32) (z:int32) : int32 =
    word_xor (word_and x y) (word_xor (word_and x z) (word_and y z))`;;

(* SIGMA_0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x) [Eq. 4.4] *)
let sha256_Sigma0 = new_definition
 `sha256_Sigma0 (x:int32) : int32 =
    word_xor (word_ror x 2) (word_xor (word_ror x 13) (word_ror x 22))`;;

(* SIGMA_1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) [Eq. 4.5] *)
let sha256_Sigma1 = new_definition
 `sha256_Sigma1 (x:int32) : int32 =
    word_xor (word_ror x 6) (word_xor (word_ror x 11) (word_ror x 25))`;;

(* sigma_0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) [Eq. 4.6] *)
let sha256_sigma0 = new_definition
 `sha256_sigma0 (x:int32) : int32 =
    word_xor (word_ror x 7) (word_xor (word_ror x 18) (word_ushr x 3))`;;

(* sigma_1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) [Eq. 4.7] *)
let sha256_sigma1 = new_definition
 `sha256_sigma1 (x:int32) : int32 =
    word_xor (word_ror x 17) (word_xor (word_ror x 19) (word_ushr x 10))`;;

(* ------------------------------------------------------------------------- *)
(* Message schedule W_t for t = 0..63 (FIPS 180-4, Section 6.2.2).          *)
(*                                                                           *)
(* Given a 16-word message block M, the schedule extends it to 64 words:     *)
(*   W_t = M_t                                             for 0 <= t <= 15  *)
(*   W_t = sigma_1(W_{t-2}) + W_{t-7} + sigma_0(W_{t-15}) + W_{t-16}       *)
(*                                                         for 16 <= t <= 63 *)
(*                                                                           *)
(* sha256_message_schedule n M produces a list of (n + 16) words:            *)
(*   sha256_message_schedule 0 M = M                    (16 words)           *)
(*   sha256_message_schedule 48 M = full schedule       (64 words)           *)
(* ------------------------------------------------------------------------- *)

let sha256_extend_schedule = new_definition
 `sha256_extend_schedule (W:int32 list) (n:num) : int32 list =
    APPEND W
      [word_add (sha256_sigma1 (EL (n + 14) W))
                (word_add (EL (n + 9) W)
                          (word_add (sha256_sigma0 (EL (n + 1) W))
                                    (EL n W)))]`;;

let sha256_message_schedule = define
 `sha256_message_schedule 0 (M:int32 list) = M /\
  sha256_message_schedule (n + 1) M =
    sha256_extend_schedule (sha256_message_schedule n M) n`;;

(* ------------------------------------------------------------------------- *)
(* Compression function (FIPS 180-4, Section 6.2.2, Steps 2-3).             *)
(*                                                                           *)
(* State is [a; b; c; d; e; f; g; h] where a is the first working variable. *)
(*                                                                           *)
(* Each round computes:                                                      *)
(*   T1 = h + SIGMA_1(e) + Ch(e,f,g) + K_t + W_t                           *)
(*   T2 = SIGMA_0(a) + Maj(a,b,c)                                           *)
(*   new state = [T1+T2; a; b; c; d+T1; e; f; g]                            *)
(* ------------------------------------------------------------------------- *)

let sha256_compress_round = new_definition
 `sha256_compress_round (K_t:int32) (W_t:int32) (state:int32 list) : int32 list =
    let a = EL 0 state and b = EL 1 state and c = EL 2 state and d = EL 3 state
    and e = EL 4 state and f = EL 5 state and g = EL 6 state and h = EL 7 state in
    let T1 = word_add h (word_add (sha256_Sigma1 e)
                                  (word_add (sha256_Ch e f g)
                                            (word_add K_t W_t))) in
    let T2 = word_add (sha256_Sigma0 a) (sha256_Maj a b c) in
    [word_add T1 T2; a; b; c; word_add d T1; e; f; g]`;;

let sha256_compress = define
 `sha256_compress 0 W state = state /\
  sha256_compress (n + 1) W state =
    sha256_compress_round (EL n sha256_K) (EL n W)
                          (sha256_compress n W state)`;;

(* ------------------------------------------------------------------------- *)
(* Block processing (FIPS 180-4, Section 6.2.2, Step 4).                     *)
(*                                                                           *)
(* Process a single 512-bit message block (16 words):                        *)
(*   1. Compute the 64-word message schedule                                 *)
(*   2. Run 64 rounds of compression                                         *)
(*   3. Add compressed state to input hash                                   *)
(* ------------------------------------------------------------------------- *)

let sha256_block = new_definition
 `sha256_block (msg_block:int32 list) (hash:int32 list) : int32 list =
    let W = sha256_message_schedule 48 msg_block in
    let compressed = sha256_compress 64 W hash in
    MAP2 word_add compressed hash`;;

(* ------------------------------------------------------------------------- *)
(* Multi-block iteration (FIPS 180-4, Section 6.2.2).                        *)
(*                                                                           *)
(* sha256_hash_blocks n blocks H applies sha256_block iteratively:           *)
(*   sha256_hash_blocks 0 blocks H = H                                      *)
(*   sha256_hash_blocks (n+1) blocks H =                                    *)
(*     sha256_block (EL n blocks) (sha256_hash_blocks n blocks H)           *)
(* ------------------------------------------------------------------------- *)

let sha256_hash_blocks = define
 `sha256_hash_blocks 0 blocks H = H /\
  sha256_hash_blocks (n + 1) blocks H =
    sha256_block (EL n blocks) (sha256_hash_blocks n blocks H)`;;
