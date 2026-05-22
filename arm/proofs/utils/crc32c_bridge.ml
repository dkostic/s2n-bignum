(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridging lemmas connecting the kernel-level CRC32C specification          *)
(* (arm/proofs/utils/crc32c_spec.ml) to the ARM hardware-instruction model   *)
(* (arm/proofs/instruction.ml).                                              *)
(*                                                                           *)
(* The spec-side definitions `crc32c_step` and `crc32c_byte` are             *)
(* structurally identical to the hardware-side `crc32c_bit` and              *)
(* `crc32c_hw_step` (modulo the `crc32c_poly_refl` constant), so the load-   *)
(* bearing single-byte bridge collapses by REWRITE.                          *)
(*                                                                           *)
(* The 2/4/8-byte bridges express the chain of `crc32c_hw_step` applications *)
(* produced by `arm_CRC32C{H,W,X}` as a `crc32c_bytes` fold over the         *)
(* little-endian byte decomposition of the source operand. This is the form  *)
(* Phase 5 onwards consumes: after `ARM_STEPS_TAC`, the state contains the   *)
(* nested `crc32c_hw_step` chain on the LHS, which the bridge rewrites to    *)
(* `crc32c_bytes acc [byte_0; byte_1; ...]` on the RHS — matching the        *)
(* spec-level fold.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/crc32c_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Step bridge: the spec's bit-level step equals the hardware's bit-level    *)
(* step. This holds by definition modulo `crc32c_poly_refl`.                 *)
(* ------------------------------------------------------------------------- *)

let CRC32C_STEP_BRIDGE = prove
 (`!acc:int32 b. crc32c_step acc b = crc32c_bit acc b`,
  REWRITE_TAC[crc32c_step; crc32c_bit; crc32c_poly_refl]);;

(* ------------------------------------------------------------------------- *)
(* Single-byte bridge: the spec's `crc32c_byte` equals the hardware's        *)
(* `crc32c_hw_step` (8 bit-steps over the byte, LSB-first).                  *)
(* ------------------------------------------------------------------------- *)

let CRC32CB_BRIDGE = prove
 (`!acc:int32 b:byte. crc32c_hw_step acc b = crc32c_byte acc b`,
  REWRITE_TAC[crc32c_hw_step; crc32c_byte; CRC32C_STEP_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Two-byte bridge: the chain of two `crc32c_hw_step` applications produced  *)
(* by `arm_CRC32CH` equals the `crc32c_bytes` fold over the little-endian    *)
(* byte decomposition of the 16-bit source.                                  *)
(* ------------------------------------------------------------------------- *)

let CRC32CH_BRIDGE = prove
 (`!acc:int32 m:int32.
        crc32c_hw_step
         (crc32c_hw_step acc (word_subword m (0,8):byte))
         (word_subword m (8,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Four-byte bridge: as CRC32CH_BRIDGE but for `arm_CRC32CW`.                 *)
(* ------------------------------------------------------------------------- *)

let CRC32CW_BRIDGE = prove
 (`!acc:int32 m:int32.
        crc32c_hw_step
         (crc32c_hw_step
          (crc32c_hw_step
           (crc32c_hw_step acc (word_subword m (0,8):byte))
           (word_subword m (8,8):byte))
          (word_subword m (16,8):byte))
         (word_subword m (24,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte;
          word_subword m (16,8):byte; word_subword m (24,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;

(* ------------------------------------------------------------------------- *)
(* Eight-byte bridge: as CRC32CH_BRIDGE but for `arm_CRC32CX`. The source     *)
(* operand is an int64 here (mirroring `arm_CRC32CX`).                       *)
(* ------------------------------------------------------------------------- *)

let CRC32CX_BRIDGE = prove
 (`!acc:int32 m:int64.
        crc32c_hw_step
         (crc32c_hw_step
          (crc32c_hw_step
           (crc32c_hw_step
            (crc32c_hw_step
             (crc32c_hw_step
              (crc32c_hw_step
               (crc32c_hw_step acc (word_subword m (0,8):byte))
                              (word_subword m (8,8):byte))
                             (word_subword m (16,8):byte))
                            (word_subword m (24,8):byte))
                           (word_subword m (32,8):byte))
                          (word_subword m (40,8):byte))
                         (word_subword m (48,8):byte))
                        (word_subword m (56,8):byte) =
        crc32c_bytes acc
         [word_subword m (0,8):byte; word_subword m (8,8):byte;
          word_subword m (16,8):byte; word_subword m (24,8):byte;
          word_subword m (32,8):byte; word_subword m (40,8):byte;
          word_subword m (48,8):byte; word_subword m (56,8):byte]`,
  REWRITE_TAC[crc32c_bytes; CRC32CB_BRIDGE]);;
