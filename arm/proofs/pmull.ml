(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "Library/words.ml";;

(* ========================================================================= *)
(* Polynomial (carry-less) multiplication for PMULL/PMULL2 instructions.     *)
(* ========================================================================= *)

(* Carry-less multiplication of two 8-bit values (zero-extended to 16-bit).
   Implements the PolynomialMult pseudocode from the Arm A64 ISA:
     result = Zeros(16);
     extended_b = ZeroExtend(b, 16);
     for i = 0 to 7
       if a<i> == '1' then result = result EOR (extended_b << i);
     return result;
   The inputs a and b are expected to be zero-extended 8-bit values
   in 16-bit words. Only the lower 8 bits of a are iterated over. *)

let pmull8 = define
 `pmull8 (a:(16)word) (b:(16)word) : (16)word =
    let r0:(16)word = (if bit 0 a then b else word 0) in
    let r1:(16)word = word_xor r0 (if bit 1 a then word_shl b 1 else word 0) in
    let r2:(16)word = word_xor r1 (if bit 2 a then word_shl b 2 else word 0) in
    let r3:(16)word = word_xor r2 (if bit 3 a then word_shl b 3 else word 0) in
    let r4:(16)word = word_xor r3 (if bit 4 a then word_shl b 4 else word 0) in
    let r5:(16)word = word_xor r4 (if bit 5 a then word_shl b 5 else word 0) in
    let r6:(16)word = word_xor r5 (if bit 6 a then word_shl b 6 else word 0) in
    let r7:(16)word = word_xor r6 (if bit 7 a then word_shl b 7 else word 0) in
    r7`;;

(* Carry-less multiplication of two 64-bit values producing a 128-bit result.
   Implements the PolynomialMult pseudocode from the Arm A64 ISA:
     result = Zeros(128);
     extended_b = ZeroExtend(b, 128);
     for i = 0 to 63
       if a<i> == '1' then result = result EOR (extended_b << i);
     return result; *)

let pmull64 = define
 `pmull64 (a:int64) (b:int64) : int128 =
    let b':(128)word = word_zx b in
    let r0:(128)word = (if bit 0 a then b' else word 0) in
    let r1:(128)word = word_xor r0 (if bit 1 a then word_shl b' 1 else word 0) in
    let r2:(128)word = word_xor r1 (if bit 2 a then word_shl b' 2 else word 0) in
    let r3:(128)word = word_xor r2 (if bit 3 a then word_shl b' 3 else word 0) in
    let r4:(128)word = word_xor r3 (if bit 4 a then word_shl b' 4 else word 0) in
    let r5:(128)word = word_xor r4 (if bit 5 a then word_shl b' 5 else word 0) in
    let r6:(128)word = word_xor r5 (if bit 6 a then word_shl b' 6 else word 0) in
    let r7:(128)word = word_xor r6 (if bit 7 a then word_shl b' 7 else word 0) in
    let r8:(128)word = word_xor r7 (if bit 8 a then word_shl b' 8 else word 0) in
    let r9:(128)word = word_xor r8 (if bit 9 a then word_shl b' 9 else word 0) in
    let r10:(128)word = word_xor r9 (if bit 10 a then word_shl b' 10 else word 0) in
    let r11:(128)word = word_xor r10 (if bit 11 a then word_shl b' 11 else word 0) in
    let r12:(128)word = word_xor r11 (if bit 12 a then word_shl b' 12 else word 0) in
    let r13:(128)word = word_xor r12 (if bit 13 a then word_shl b' 13 else word 0) in
    let r14:(128)word = word_xor r13 (if bit 14 a then word_shl b' 14 else word 0) in
    let r15:(128)word = word_xor r14 (if bit 15 a then word_shl b' 15 else word 0) in
    let r16:(128)word = word_xor r15 (if bit 16 a then word_shl b' 16 else word 0) in
    let r17:(128)word = word_xor r16 (if bit 17 a then word_shl b' 17 else word 0) in
    let r18:(128)word = word_xor r17 (if bit 18 a then word_shl b' 18 else word 0) in
    let r19:(128)word = word_xor r18 (if bit 19 a then word_shl b' 19 else word 0) in
    let r20:(128)word = word_xor r19 (if bit 20 a then word_shl b' 20 else word 0) in
    let r21:(128)word = word_xor r20 (if bit 21 a then word_shl b' 21 else word 0) in
    let r22:(128)word = word_xor r21 (if bit 22 a then word_shl b' 22 else word 0) in
    let r23:(128)word = word_xor r22 (if bit 23 a then word_shl b' 23 else word 0) in
    let r24:(128)word = word_xor r23 (if bit 24 a then word_shl b' 24 else word 0) in
    let r25:(128)word = word_xor r24 (if bit 25 a then word_shl b' 25 else word 0) in
    let r26:(128)word = word_xor r25 (if bit 26 a then word_shl b' 26 else word 0) in
    let r27:(128)word = word_xor r26 (if bit 27 a then word_shl b' 27 else word 0) in
    let r28:(128)word = word_xor r27 (if bit 28 a then word_shl b' 28 else word 0) in
    let r29:(128)word = word_xor r28 (if bit 29 a then word_shl b' 29 else word 0) in
    let r30:(128)word = word_xor r29 (if bit 30 a then word_shl b' 30 else word 0) in
    let r31:(128)word = word_xor r30 (if bit 31 a then word_shl b' 31 else word 0) in
    let r32:(128)word = word_xor r31 (if bit 32 a then word_shl b' 32 else word 0) in
    let r33:(128)word = word_xor r32 (if bit 33 a then word_shl b' 33 else word 0) in
    let r34:(128)word = word_xor r33 (if bit 34 a then word_shl b' 34 else word 0) in
    let r35:(128)word = word_xor r34 (if bit 35 a then word_shl b' 35 else word 0) in
    let r36:(128)word = word_xor r35 (if bit 36 a then word_shl b' 36 else word 0) in
    let r37:(128)word = word_xor r36 (if bit 37 a then word_shl b' 37 else word 0) in
    let r38:(128)word = word_xor r37 (if bit 38 a then word_shl b' 38 else word 0) in
    let r39:(128)word = word_xor r38 (if bit 39 a then word_shl b' 39 else word 0) in
    let r40:(128)word = word_xor r39 (if bit 40 a then word_shl b' 40 else word 0) in
    let r41:(128)word = word_xor r40 (if bit 41 a then word_shl b' 41 else word 0) in
    let r42:(128)word = word_xor r41 (if bit 42 a then word_shl b' 42 else word 0) in
    let r43:(128)word = word_xor r42 (if bit 43 a then word_shl b' 43 else word 0) in
    let r44:(128)word = word_xor r43 (if bit 44 a then word_shl b' 44 else word 0) in
    let r45:(128)word = word_xor r44 (if bit 45 a then word_shl b' 45 else word 0) in
    let r46:(128)word = word_xor r45 (if bit 46 a then word_shl b' 46 else word 0) in
    let r47:(128)word = word_xor r46 (if bit 47 a then word_shl b' 47 else word 0) in
    let r48:(128)word = word_xor r47 (if bit 48 a then word_shl b' 48 else word 0) in
    let r49:(128)word = word_xor r48 (if bit 49 a then word_shl b' 49 else word 0) in
    let r50:(128)word = word_xor r49 (if bit 50 a then word_shl b' 50 else word 0) in
    let r51:(128)word = word_xor r50 (if bit 51 a then word_shl b' 51 else word 0) in
    let r52:(128)word = word_xor r51 (if bit 52 a then word_shl b' 52 else word 0) in
    let r53:(128)word = word_xor r52 (if bit 53 a then word_shl b' 53 else word 0) in
    let r54:(128)word = word_xor r53 (if bit 54 a then word_shl b' 54 else word 0) in
    let r55:(128)word = word_xor r54 (if bit 55 a then word_shl b' 55 else word 0) in
    let r56:(128)word = word_xor r55 (if bit 56 a then word_shl b' 56 else word 0) in
    let r57:(128)word = word_xor r56 (if bit 57 a then word_shl b' 57 else word 0) in
    let r58:(128)word = word_xor r57 (if bit 58 a then word_shl b' 58 else word 0) in
    let r59:(128)word = word_xor r58 (if bit 59 a then word_shl b' 59 else word 0) in
    let r60:(128)word = word_xor r59 (if bit 60 a then word_shl b' 60 else word 0) in
    let r61:(128)word = word_xor r60 (if bit 61 a then word_shl b' 61 else word 0) in
    let r62:(128)word = word_xor r61 (if bit 62 a then word_shl b' 62 else word 0) in
    let r63:(128)word = word_xor r62 (if bit 63 a then word_shl b' 63 else word 0) in
    r63`;;

(************************************************)
(**  CONVERSIONS                               **)
(************************************************)

let PMULL8_RED_CONV =
  REWR_CONV pmull8 THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;;

let PMULL8_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("pmull8",_),
         Comb(Const("word",_),a)),
         Comb(Const("word",_),b))
    when is_numeral a && is_numeral b -> PMULL8_RED_CONV tm
  | _ -> failwith "PMULL8_REDUCE_CONV: inapplicable";;

let PMULL64_RED_CONV =
  REWR_CONV pmull64 THENC
  DEPTH_CONV (let_CONV) THENC
  WORD_REDUCE_CONV;;

let PMULL64_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("pmull64",_),
         Comb(Const("word",_),a)),
         Comb(Const("word",_),b))
    when is_numeral a && is_numeral b -> PMULL64_RED_CONV tm
  | _ -> failwith "PMULL64_REDUCE_CONV: inapplicable";;
