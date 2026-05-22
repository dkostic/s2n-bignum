(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of CRC32C (Castagnoli polynomial 0x1EDC6F41 / reflected     *)
(* 0x82F63B78), as used by IETF SCTP / iSCSI / btrfs / many other systems.   *)
(* This is the kernel-level spec: a pure functional definition over byte     *)
(* lists, independent of any hardware. The hardware-instruction model in     *)
(* arm/proofs/instruction.ml (crc32c_bit / crc32c_hw_step) is bridged to     *)
(* this spec in arm/proofs/utils/crc32c_bridge.ml.                            *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Reflected polynomial constant.                                            *)
(*                                                                           *)
(* CRC32C uses the Castagnoli polynomial x^32 + x^28 + x^27 + x^26 + x^25 +  *)
(* x^23 + x^22 + x^20 + x^19 + x^18 + x^14 + x^13 + x^11 + x^10 + x^9 +      *)
(* x^8 + x^6 + 1 (= 0x1EDC6F41 in normal form).                              *)
(* The bit-reflected form 0x82F63B78 is used by all reflected (LSB-first)    *)
(* implementations including the ARM CRC32C{B,H,W,X} instructions.           *)
(* ------------------------------------------------------------------------- *)

let crc32c_poly_refl = new_definition
 `crc32c_poly_refl:int32 = word 0x82F63B78`;;

(* ------------------------------------------------------------------------- *)
(* Single-bit reflected polynomial step:                                     *)
(*   acc' = (acc >> 1) XOR ( (bit0(acc) XOR b) ? 0x82F63B78 : 0 )            *)
(*                                                                           *)
(* This is the bit-by-bit primitive shared by every CRC32C definition,       *)
(* including the C reference in tests/test.c (reference_crc32c) and the      *)
(* hardware-instruction model crc32c_bit in arm/proofs/instruction.ml.       *)
(* The two are intentionally definitionally equal so the byte-step bridge    *)
(* in Phase 4 collapses by REWRITE alone.                                    *)
(* ------------------------------------------------------------------------- *)

let crc32c_step = new_definition
 `crc32c_step (acc:int32) (b:bool) =
    let acc' = word_ushr acc 1 in
    if ~(bit 0 acc <=> b)
    then word_xor acc' crc32c_poly_refl
    else acc'`;;

(* ------------------------------------------------------------------------- *)
(* Single-byte step: 8 bit-steps over the bits of the byte, LSB-first.       *)
(*                                                                           *)
(* This mirrors the structure of crc32c_hw_step in instruction.ml so that    *)
(* CRC32CB_BRIDGE (Phase 4) holds by REWRITE_TAC alone.                      *)
(* ------------------------------------------------------------------------- *)

let crc32c_byte = new_definition
 `crc32c_byte (acc:int32) (b:byte) =
    crc32c_step
     (crc32c_step
      (crc32c_step
       (crc32c_step
        (crc32c_step
         (crc32c_step
          (crc32c_step
           (crc32c_step acc (bit 0 b))
                       (bit 1 b))
            (bit 2 b)) (bit 3 b))
             (bit 4 b)) (bit 5 b))
              (bit 6 b)) (bit 7 b)`;;

(* ------------------------------------------------------------------------- *)
(* Byte-list fold: feed bytes left-to-right, init-on-the-left.               *)
(* ------------------------------------------------------------------------- *)

let crc32c_bytes = define
 `crc32c_bytes (acc:int32) [] = acc /\
  crc32c_bytes (acc:int32) (CONS (b:byte) bs) =
    crc32c_bytes (crc32c_byte acc b) bs`;;

(* ------------------------------------------------------------------------- *)
(* Full kernel-level CRC32C: init = 0xFFFFFFFF, feed bytes, finalise by NOT. *)
(* This matches the IETF / RFC 3720 convention used by reference_crc32c in   *)
(* tests/test.c.                                                             *)
(* ------------------------------------------------------------------------- *)

let crc32c_buffer = new_definition
 `crc32c_buffer (bytes:byte list) : int32 =
    word_not (crc32c_bytes (word 0xFFFFFFFF) bytes)`;;

(* ------------------------------------------------------------------------- *)
(* Structural lemmas. crc32c_bytes_NIL is just the first conjunct of         *)
(* crc32c_bytes; we name it for ease of citation. crc32c_bytes_APPEND        *)
(* establishes the standard fold-over-append identity, which the multi-      *)
(* iteration loop proof in Phase 8 will rely on.                             *)
(* ------------------------------------------------------------------------- *)

let crc32c_bytes_NIL = prove
 (`!acc:int32. crc32c_bytes acc [] = acc`,
  REWRITE_TAC[crc32c_bytes]);;

let crc32c_bytes_APPEND = prove
 (`!xs (acc:int32) ys.
        crc32c_bytes acc (APPEND xs ys) =
        crc32c_bytes (crc32c_bytes acc xs) ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; crc32c_bytes]);;

(* ------------------------------------------------------------------------- *)
(* Computational reduction.                                                  *)
(*                                                                           *)
(* Naive REWRITE_TAC on the byte/step/poly definitions diverges (the inner   *)
(* branch structure cannot be reduced incrementally because each conditional *)
(* has not been resolved). Instead we provide CRC32C_BYTE_CONV, which        *)
(* unfolds one byte step and then evaluates the bit lookups, words, and      *)
(* conditionals together via a single DEPTH_CONV mixing word, num, and       *)
(* boolean primitives. This reduces a single byte step in well under a       *)
(* second; CRC32C_BYTES_CONV iterates it across a concrete byte list.        *)
(* ------------------------------------------------------------------------- *)

let CRC32C_BYTE_CONV =
  REWR_CONV crc32c_byte THENC
  REWRITE_CONV[crc32c_step; crc32c_poly_refl] THENC
  DEPTH_CONV
   (let_CONV ORELSEC
    WORD_RED_CONV ORELSEC
    NUM_RED_CONV ORELSEC
    GEN_REWRITE_CONV I [COND_CLAUSES; NOT_CLAUSES; EQ_CLAUSES]);;

let CRC32C_BYTES_CONV =
  let CRC32C_BYTES_NIL_CONV = REWR_CONV(CONJUNCT1 crc32c_bytes)
  and CRC32C_BYTES_CONS_CONV = REWR_CONV(CONJUNCT2 crc32c_bytes) in
  let one_step =
    CRC32C_BYTES_CONS_CONV THENC RATOR_CONV(RAND_CONV CRC32C_BYTE_CONV) in
  REPEATC one_step THENC CRC32C_BYTES_NIL_CONV;;

(* ------------------------------------------------------------------------- *)
(* IETF KAT: crc32c_buffer "123456789" = 0xE3069283.                         *)
(* This is the same constant the C reference + the kernel were KAT-gated on  *)
(* in Phase 2; passing here aligns the HOL spec with the executable C twin.  *)
(* ------------------------------------------------------------------------- *)

let CRC32C_BUFFER_KAT = prove
 (`crc32c_buffer
     [word 0x31; word 0x32; word 0x33; word 0x34;
      word 0x35; word 0x36; word 0x37; word 0x38; word 0x39] =
   word 0xE3069283`,
  REWRITE_TAC[crc32c_buffer] THEN
  CONV_TAC(LAND_CONV(RAND_CONV CRC32C_BYTES_CONV THENC WORD_REDUCE_CONV)) THEN
  REFL_TAC);;
