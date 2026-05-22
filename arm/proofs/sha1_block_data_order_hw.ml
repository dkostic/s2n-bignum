(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correctness proof for sha1_block_data_order_hw (Phase 5 pilot).           *)
(*                                                                           *)
(* This file holds the machine-code constant for the full                    *)
(* sha1_block_data_order_hw routine, plus a register-only ensures theorem    *)
(* over the very first SHA1H + SHA1C instruction pair (rounds 0..3) of the   *)
(* compression loop. It mirrors the SHA-256 pilot's `sha256_4rounds_reg`     *)
(* shape: no memory traffic, no K-loading, no loop entry; the inputs and    *)
(* outputs are vector registers, and the bridge lemmas SHA1H_BRIDGE and     *)
(* SHA1C_BRIDGE in arm/proofs/utils/sha1_bridge.ml discharge the postconds. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/sha1_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* The full sha1_block_data_order_hw machine-code constant.                  *)
(* ------------------------------------------------------------------------- *)

let sha1_block_data_order_hw_mc = define_assert_from_elf "sha1_block_data_order_hw_mc"
  (file_on_path !load_path "arm/sha1/sha1_block_data_order_hw.o")
[
  0x3dc00000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  0xb9401004;       (* arm_LDR W4 X0 (Immediate_Offset (word 16)) *)
  0x4e041c81;       (* arm_INS_GEN Q1 W4 0 32 *)
  0x3dc00070;       (* arm_LDR Q16 X3 (Immediate_Offset (word 0)) *)
  0x3dc00471;       (* arm_LDR Q17 X3 (Immediate_Offset (word 16)) *)
  0x3dc00872;       (* arm_LDR Q18 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c73;       (* arm_LDR Q19 X3 (Immediate_Offset (word 48)) *)
  0x3dc00024;       (* arm_LDR Q4 X1 (Immediate_Offset (word 0)) *)
  0x3dc00425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 16)) *)
  0x3dc00826;       (* arm_LDR Q6 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 48)) *)
  0x91010021;       (* arm_ADD X1 X1 (rvalue (word 64)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x6e200884;       (* arm_REV32_VEC Q4 Q4 8 *)
  0x6e2008a5;       (* arm_REV32_VEC Q5 Q5 8 *)
  0x6e2008c6;       (* arm_REV32_VEC Q6 Q6 8 *)
  0x6e2008e7;       (* arm_REV32_VEC Q7 Q7 8 *)
  0x4ea01c16;       (* arm_MOV_VEC Q22 Q0 128 *)
  0x4ea48614;       (* arm_ADD_VEC Q20 Q16 Q4 32 128 *)
  0x4ea58615;       (* arm_ADD_VEC Q21 Q16 Q5 32 128 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e140020;       (* arm_SHA1C Q0 (SREG' (word 1)) Q20 *)
  0x4ea68614;       (* arm_ADD_VEC Q20 Q16 Q6 32 128 *)
  0x5e0630a4;       (* arm_SHA1SU0 Q4 Q5 Q6 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e150060;       (* arm_SHA1C Q0 (SREG' (word 3)) Q21 *)
  0x4ea78615;       (* arm_ADD_VEC Q21 Q16 Q7 32 128 *)
  0x5e2818e4;       (* arm_SHA1SU1 Q4 Q7 *)
  0x5e0730c5;       (* arm_SHA1SU0 Q5 Q6 Q7 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e140040;       (* arm_SHA1C Q0 (SREG' (word 2)) Q20 *)
  0x4ea48614;       (* arm_ADD_VEC Q20 Q16 Q4 32 128 *)
  0x5e281885;       (* arm_SHA1SU1 Q5 Q4 *)
  0x5e0430e6;       (* arm_SHA1SU0 Q6 Q7 Q4 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e150060;       (* arm_SHA1C Q0 (SREG' (word 3)) Q21 *)
  0x4ea58635;       (* arm_ADD_VEC Q21 Q17 Q5 32 128 *)
  0x5e2818a6;       (* arm_SHA1SU1 Q6 Q5 *)
  0x5e053087;       (* arm_SHA1SU0 Q7 Q4 Q5 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e140040;       (* arm_SHA1C Q0 (SREG' (word 2)) Q20 *)
  0x4ea68634;       (* arm_ADD_VEC Q20 Q17 Q6 32 128 *)
  0x5e2818c7;       (* arm_SHA1SU1 Q7 Q6 *)
  0x5e0630a4;       (* arm_SHA1SU0 Q4 Q5 Q6 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea78635;       (* arm_ADD_VEC Q21 Q17 Q7 32 128 *)
  0x5e2818e4;       (* arm_SHA1SU1 Q4 Q7 *)
  0x5e0730c5;       (* arm_SHA1SU0 Q5 Q6 Q7 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e141040;       (* arm_SHA1P Q0 (SREG' (word 2)) Q20 *)
  0x4ea48634;       (* arm_ADD_VEC Q20 Q17 Q4 32 128 *)
  0x5e281885;       (* arm_SHA1SU1 Q5 Q4 *)
  0x5e0430e6;       (* arm_SHA1SU0 Q6 Q7 Q4 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea58635;       (* arm_ADD_VEC Q21 Q17 Q5 32 128 *)
  0x5e2818a6;       (* arm_SHA1SU1 Q6 Q5 *)
  0x5e053087;       (* arm_SHA1SU0 Q7 Q4 Q5 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e141040;       (* arm_SHA1P Q0 (SREG' (word 2)) Q20 *)
  0x4ea68654;       (* arm_ADD_VEC Q20 Q18 Q6 32 128 *)
  0x5e2818c7;       (* arm_SHA1SU1 Q7 Q6 *)
  0x5e0630a4;       (* arm_SHA1SU0 Q4 Q5 Q6 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea78655;       (* arm_ADD_VEC Q21 Q18 Q7 32 128 *)
  0x5e2818e4;       (* arm_SHA1SU1 Q4 Q7 *)
  0x5e0730c5;       (* arm_SHA1SU0 Q5 Q6 Q7 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e142040;       (* arm_SHA1M Q0 (SREG' (word 2)) Q20 *)
  0x4ea48654;       (* arm_ADD_VEC Q20 Q18 Q4 32 128 *)
  0x5e281885;       (* arm_SHA1SU1 Q5 Q4 *)
  0x5e0430e6;       (* arm_SHA1SU0 Q6 Q7 Q4 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e152060;       (* arm_SHA1M Q0 (SREG' (word 3)) Q21 *)
  0x4ea58655;       (* arm_ADD_VEC Q21 Q18 Q5 32 128 *)
  0x5e2818a6;       (* arm_SHA1SU1 Q6 Q5 *)
  0x5e053087;       (* arm_SHA1SU0 Q7 Q4 Q5 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e142040;       (* arm_SHA1M Q0 (SREG' (word 2)) Q20 *)
  0x4ea68654;       (* arm_ADD_VEC Q20 Q18 Q6 32 128 *)
  0x5e2818c7;       (* arm_SHA1SU1 Q7 Q6 *)
  0x5e0630a4;       (* arm_SHA1SU0 Q4 Q5 Q6 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e152060;       (* arm_SHA1M Q0 (SREG' (word 3)) Q21 *)
  0x4ea78675;       (* arm_ADD_VEC Q21 Q19 Q7 32 128 *)
  0x5e2818e4;       (* arm_SHA1SU1 Q4 Q7 *)
  0x5e0730c5;       (* arm_SHA1SU0 Q5 Q6 Q7 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e142040;       (* arm_SHA1M Q0 (SREG' (word 2)) Q20 *)
  0x4ea48674;       (* arm_ADD_VEC Q20 Q19 Q4 32 128 *)
  0x5e281885;       (* arm_SHA1SU1 Q5 Q4 *)
  0x5e0430e6;       (* arm_SHA1SU0 Q6 Q7 Q4 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea58675;       (* arm_ADD_VEC Q21 Q19 Q5 32 128 *)
  0x5e2818a6;       (* arm_SHA1SU1 Q6 Q5 *)
  0x5e053087;       (* arm_SHA1SU0 Q7 Q4 Q5 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e141040;       (* arm_SHA1P Q0 (SREG' (word 2)) Q20 *)
  0x4ea68674;       (* arm_ADD_VEC Q20 Q19 Q6 32 128 *)
  0x5e2818c7;       (* arm_SHA1SU1 Q7 Q6 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea78675;       (* arm_ADD_VEC Q21 Q19 Q7 32 128 *)
  0x5e280803;       (* arm_SHA1H Q3 Q0 *)
  0x5e141040;       (* arm_SHA1P Q0 (SREG' (word 2)) Q20 *)
  0x5e280802;       (* arm_SHA1H Q2 Q0 *)
  0x5e151060;       (* arm_SHA1P Q0 (SREG' (word 3)) Q21 *)
  0x4ea28421;       (* arm_ADD_VEC Q1 Q1 Q2 32 128 *)
  0x4eb68400;       (* arm_ADD_VEC Q0 Q0 Q22 32 128 *)
  0xb5fff2e2;       (* arm_CBNZ X2 (word 2096732) *)
  0x3d800000;       (* arm_STR Q0 X0 (Immediate_Offset (word 0)) *)
  0x0e043c24;       (* arm_UMOV W4 Q1 0 4 *)
  0xb9001004;       (* arm_STR W4 X0 (Immediate_Offset (word 16)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SHA1_BLOCK_DATA_ORDER_HW_EXEC = ARM_MK_EXEC_RULE sha1_block_data_order_hw_mc;;

(* ------------------------------------------------------------------------- *)
(* Pilot ensures theorem.                                                    *)
(*                                                                           *)
(* The slice covers the first SHA1H + SHA1C pair of the block-compression   *)
(*   loop, at byte offsets 0x50 (instruction index 20) and 0x54              *)
(*   (instruction index 21):                                                 *)
(*                                                                           *)
(*       sha1h   s3, s0          (* Q3 := SHA1H Q0    *)                    *)
(*       sha1c   q0, s1, v20.4s  (* Q0 := SHA1C Q0 Q1 Q20 *)                *)
(*                                                                           *)
(* Inputs:                                                                   *)
(*   Q0   = word_join4 a b c d       (the four-lane abcd state)              *)
(*   Q1   = e   (int128 holding `e` in low 32 bits per ARM ARM SHA1C Sn)    *)
(*   Q20  = word_join4 kw0 kw1 kw2 kw3  (the four pre-summed kw values)     *)
(*                                                                           *)
(* Outputs:                                                                  *)
(*   Q3 = (word_rol a 30, 0, 0, 0)                                           *)
(*   Q0 = SHA1C result, expressed via four sha1_compress_round_pre 0 steps. *)
(* ------------------------------------------------------------------------- *)

let SHA1_4ROUNDS_REG_CORRECT = prove
 (`!(a:int32) (b:int32) (c:int32) (d:int32) (e:int128)
    (kw0:int32) (kw1:int32) (kw2:int32) (kw3:int32)
    pc.
    ensures arm
     (\s. aligned_bytes_loaded s (word pc) sha1_block_data_order_hw_mc /\
          read PC s = word (pc + 0x50) /\
          read Q0 s = word_join4 a b c d /\
          read Q1 s = e /\
          read Q20 s = word_join4 kw0 kw1 kw2 kw3)
     (\s. read PC s = word (pc + 0x58) /\
          read Q3 s = word_join4 (word_rol a 30) (word 0) (word 0) (word 0) /\
          read Q0 s =
            (let s0 = [a;b;c;d;(word_subword e (0,32):int32)] in
             let s1 = sha1_compress_round_pre 0 kw0 s0 in
             let s2 = sha1_compress_round_pre 0 kw1 s1 in
             let s3 = sha1_compress_round_pre 0 kw2 s2 in
             let s4 = sha1_compress_round_pre 0 kw3 s3 in
             word_join4 (EL 0 s4) (EL 1 s4) (EL 2 s4) (EL 3 s4)))
     (MAYCHANGE [PC] ,, MAYCHANGE [Q0; Q3] ,, MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC SHA1_BLOCK_DATA_ORDER_HW_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1H_BRIDGE;
              CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA1C_BRIDGE]);;
