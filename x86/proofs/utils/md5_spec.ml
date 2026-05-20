(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of MD5 (RFC 1321).                                          *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Per-round auxiliary functions (RFC 1321, Section 3.4).                    *)
(* ------------------------------------------------------------------------- *)

(* F(x,y,z) = (x AND y) OR (NOT x AND z) *)
let md5_F = new_definition
 `md5_F (x:int32) (y:int32) (z:int32) : int32 =
    word_or (word_and x y) (word_and (word_not x) z)`;;

(* G(x,y,z) = (x AND z) OR (y AND NOT z) *)
let md5_G = new_definition
 `md5_G (x:int32) (y:int32) (z:int32) : int32 =
    word_or (word_and x z) (word_and y (word_not z))`;;

(* H(x,y,z) = x XOR y XOR z *)
let md5_H = new_definition
 `md5_H (x:int32) (y:int32) (z:int32) : int32 =
    word_xor x (word_xor y z)`;;

(* I(x,y,z) = y XOR (x OR NOT z) *)
let md5_I = new_definition
 `md5_I (x:int32) (y:int32) (z:int32) : int32 =
    word_xor y (word_or x (word_not z))`;;

(* ------------------------------------------------------------------------- *)
(* Round constants T[i] for i = 0..63 (RFC 1321, Section 3.4).               *)
(* T[i] = floor(2^32 * abs(sin(i+1))).                                       *)
(* These match the LEA immediates in the aws-lc x86-64 assembly.             *)
(* ------------------------------------------------------------------------- *)

let md5_T = define
 `md5_T : int32 list =
   [word 0xd76aa478; word 0xe8c7b756; word 0x242070db; word 0xc1bdceee;
    word 0xf57c0faf; word 0x4787c62a; word 0xa8304613; word 0xfd469501;
    word 0x698098d8; word 0x8b44f7af; word 0xffff5bb1; word 0x895cd7be;
    word 0x6b901122; word 0xfd987193; word 0xa679438e; word 0x49b40821;
    word 0xf61e2562; word 0xc040b340; word 0x265e5a51; word 0xe9b6c7aa;
    word 0xd62f105d; word 0x02441453; word 0xd8a1e681; word 0xe7d3fbc8;
    word 0x21e1cde6; word 0xc33707d6; word 0xf4d50d87; word 0x455a14ed;
    word 0xa9e3e905; word 0xfcefa3f8; word 0x676f02d9; word 0x8d2a4c8a;
    word 0xfffa3942; word 0x8771f681; word 0x6d9d6122; word 0xfde5380c;
    word 0xa4beea44; word 0x4bdecfa9; word 0xf6bb4b60; word 0xbebfbc70;
    word 0x289b7ec6; word 0xeaa127fa; word 0xd4ef3085; word 0x04881d05;
    word 0xd9d4d039; word 0xe6db99e5; word 0x1fa27cf8; word 0xc4ac5665;
    word 0xf4292244; word 0x432aff97; word 0xab9423a7; word 0xfc93a039;
    word 0x655b59c3; word 0x8f0ccc92; word 0xffeff47d; word 0x85845dd1;
    word 0x6fa87e4f; word 0xfe2ce6e0; word 0xa3014314; word 0x4e0811a1;
    word 0xf7537e82; word 0xbd3af235; word 0x2ad7d2bb; word 0xeb86d391]`;;

(* ------------------------------------------------------------------------- *)
(* Per-round rotation amounts S[i] (RFC 1321, Section 3.4).                  *)
(* Round 1: [7;12;17;22] cycling, Round 2: [5;9;14;20],                       *)
(* Round 3: [4;11;16;23],          Round 4: [6;10;15;21].                     *)
(* ------------------------------------------------------------------------- *)

let md5_S = new_definition
 `md5_S (i:num) : num =
    if i < 16 then EL (i MOD 4) [7; 12; 17; 22]
    else if i < 32 then EL (i MOD 4) [5; 9; 14; 20]
    else if i < 48 then EL (i MOD 4) [4; 11; 16; 23]
    else EL (i MOD 4) [6; 10; 15; 21]`;;

(* ------------------------------------------------------------------------- *)
(* Per-round message-word permutation K[i] (RFC 1321, Section 3.4).          *)
(* Round 1: K[i] = i,                 Round 2: K[i] = (5i + 1) mod 16,        *)
(* Round 3: K[i] = (3i + 5) mod 16,   Round 4: K[i] = (7i)     mod 16.        *)
(* ------------------------------------------------------------------------- *)

let md5_K = new_definition
 `md5_K (i:num) : num =
    if i < 16 then i
    else if i < 32 then (5 * i + 1) MOD 16
    else if i < 48 then (3 * i + 5) MOD 16
    else (7 * i) MOD 16`;;

(* ------------------------------------------------------------------------- *)
(* Round function selector: applies F/G/H/I depending on the quarter.        *)
(* ------------------------------------------------------------------------- *)

let md5_round_function = new_definition
 `md5_round_function (i:num) (x:int32) (y:int32) (z:int32) : int32 =
    if i < 16 then md5_F x y z
    else if i < 32 then md5_G x y z
    else if i < 48 then md5_H x y z
    else md5_I x y z`;;

(* ------------------------------------------------------------------------- *)
(* MD5 compression round (RFC 1321, Section 3.4, single iteration).          *)
(*                                                                           *)
(* State is [a; b; c; d]. One round of MD5 computes:                          *)
(*   new_a = b + ROL_S[i] (a + Func(b,c,d) + W[K[i]] + T[i])                  *)
(* and rotates the role assignment so that (a,b,c,d) cycle with each step.    *)
(*                                                                           *)
(* In the standard "cyclic" view, each step replaces a (the leftmost role)   *)
(* with new_a and then rotates the list so that the new value moves into the *)
(* "b" position next time. Concretely [a;b;c;d] -> [d; new_a; b; c].          *)
(* This matches the aws-lc asm where successive steps assign to              *)
(* RAX, RDX, RCX, RBX, RAX, ... and the role of "b" in step i+1 is the value *)
(* freshly computed in step i.                                                *)
(* ------------------------------------------------------------------------- *)

let md5_compress_round = new_definition
 `md5_compress_round (i:num) (W:int32 list) (state:int32 list) : int32 list =
    let a = EL 0 state and b = EL 1 state
    and c = EL 2 state and d = EL 3 state in
    let new_a =
      word_add b
        (word_rol
           (word_add a
              (word_add (md5_round_function i b c d)
                 (word_add (EL (md5_K i) W) (EL i md5_T))))
           (md5_S i)) in
    [d; new_a; b; c]`;;

(* ------------------------------------------------------------------------- *)
(* Iterated compression: md5_compress n W state runs n rounds.                *)
(* md5_compress 64 W [a;b;c;d] = full 64-round compression on block W.        *)
(* Cut-point access at every round.                                           *)
(* ------------------------------------------------------------------------- *)

let md5_compress = define
 `md5_compress 0 W state = state /\
  md5_compress (n + 1) W state =
    md5_compress_round n W (md5_compress n W state)`;;

(* ------------------------------------------------------------------------- *)
(* Single-block update: 64 rounds of compression then add-back of the        *)
(* original state. After 64 cyclic rotations the list has rotated by 64 mod 4*)
(* = 0 positions, so the order is preserved and add-back is positionwise.    *)
(* ------------------------------------------------------------------------- *)

let md5_block = new_definition
 `md5_block (W:int32 list) (state:int32 list) : int32 list =
    let compressed = md5_compress 64 W state in
    MAP2 word_add compressed state`;;

(* ------------------------------------------------------------------------- *)
(* Multi-block iteration. md5_hash_blocks n blocks state applies              *)
(* md5_block to the first n blocks in sequence.                                *)
(* ------------------------------------------------------------------------- *)

let md5_hash_blocks = define
 `md5_hash_blocks 0 blocks state = state /\
  md5_hash_blocks (n + 1) blocks state =
    md5_block (EL n blocks) (md5_hash_blocks n blocks state)`;;

(* ------------------------------------------------------------------------- *)
(* Initial chaining state H0 (RFC 1321, Section 3.3).                         *)
(* ------------------------------------------------------------------------- *)

let md5_H0 = define
 `md5_H0 : int32 list =
   [word 0x67452301; word 0xefcdab89; word 0x98badcfe; word 0x10325476]`;;

(* ------------------------------------------------------------------------- *)
(* Length-preservation lemmas. All transformations preserve LENGTH 4.        *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MD5_COMPRESS_ROUND = prove
 (`!i W state. LENGTH state = 4
               ==> LENGTH (md5_compress_round i W state) = 4`,
  REWRITE_TAC[md5_compress_round; LET_DEF; LET_END_DEF; LENGTH] THEN
  ARITH_TAC);;

let LENGTH_MD5_COMPRESS = prove
 (`!n W state. LENGTH state = 4 ==> LENGTH (md5_compress n W state) = 4`,
  INDUCT_TAC THEN REWRITE_TAC[md5_compress] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = n + 1`] THEN
  ASM_MESON_TAC[md5_compress; LENGTH_MD5_COMPRESS_ROUND]);;

let LENGTH_MD5_BLOCK = prove
 (`!W state. LENGTH state = 4 ==> LENGTH (md5_block W state) = 4`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[md5_block; LET_DEF; LET_END_DEF] THEN
  ASM_MESON_TAC[LENGTH_MD5_COMPRESS; LENGTH_MAP2]);;

let LENGTH_MD5_HASH_BLOCKS = prove
 (`!n blocks state.
       LENGTH state = 4 ==> LENGTH (md5_hash_blocks n blocks state) = 4`,
  INDUCT_TAC THEN REWRITE_TAC[md5_hash_blocks] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = n + 1`] THEN
  ASM_MESON_TAC[md5_hash_blocks; LENGTH_MD5_BLOCK]);;
