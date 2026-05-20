(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting MD5 algorithmic spec to the encodings used by   *)
(* the aws-lc x86-64 assembly. Pure word-level identities, no asm reasoning.  *)
(*                                                                           *)
(* Depends on:                                                               *)
(*   - x86/proofs/utils/md5_spec.ml   (algorithmic spec)                     *)
(* ========================================================================= *)

needs "x86/proofs/utils/md5_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Round 1 (F).                                                              *)
(*                                                                           *)
(* The aws-lc asm encodes F(b,c,d) using the 4-instruction chain             *)
(*   r11 = d                                                                 *)
(*   r11 ^= c        // r11 = c XOR d                                        *)
(*   r11 &= b        // r11 = b AND (c XOR d)                                *)
(*   r11 ^= d        // r11 = (b AND (c XOR d)) XOR d                        *)
(* which equals (b AND c) OR (NOT b AND d) = md5_F b c d. The lemma below    *)
(* is stated in the form the simulator emits: y plays the role of b (the     *)
(* selector), z plays c, w plays d.                                          *)
(* ------------------------------------------------------------------------- *)

let MD5_F_XOR_AND_FORM = prove
 (`!y z w:int32.
       word_xor (word_and y (word_xor z w)) w = md5_F y z w`,
  REWRITE_TAC[md5_F] THEN CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Round 2 (G).                                                              *)
(*                                                                           *)
(* The aws-lc asm encodes G(b,c,d) by computing (b AND d) and (c AND NOT d)  *)
(* into separate temporaries and then adding them with two ADDL/LEAL         *)
(* instructions, rather than using OR. This is sound because the two AND     *)
(* terms are bitwise disjoint: (b AND d) AND (c AND NOT d) = 0, so           *)
(* word_add equals word_or on this pair.                                     *)
(*                                                                           *)
(* Stating the lemma in the spec's argument order (md5_G x y z) matches      *)
(* md5_G b c d when (x,y,z) = (b,c,d): md5_G b c d = (b AND d) OR (c AND     *)
(* NOT d), which is exactly the spec definition.                             *)
(* ------------------------------------------------------------------------- *)

let MD5_G_DISJOINT_ADD = prove
 (`!x y z:int32.
       word_add (word_and x z) (word_and y (word_not z)) = md5_G x y z`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `word_or (word_and (x:int32) z) (word_and y (word_not z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WORD_ADD_OR THEN CONV_TAC WORD_BITWISE_RULE;
    REWRITE_TAC[md5_G]]);;
