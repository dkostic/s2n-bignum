(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-256 single-block with memory load/store + REV32 byte-swap.            *)
(*                                                                           *)
(* Extends sha256_block_core with:                                           *)
(*   - LDR Q for state and message data from memory                          *)
(*   - REV32 byte-swap (little-endian memory -> big-endian SHA-256 words)    *)
(*   - STR Q to write result back to state memory                            *)
(*                                                                           *)
(* Inputs (in memory):                                                       *)
(*   x0 = pointer to state (32 bytes: 8 x uint32, read and written)         *)
(*   x1 = pointer to message data (64 bytes, read-only)                     *)
(*   x2 = pointer to K constant table (256 bytes, read-only)                *)
(*                                                                           *)
(* The postcondition expresses the result in terms of sha256_block applied   *)
(* to byte-reversed message words (converting LE memory to BE SHA-256).      *)
(* ========================================================================= *)

needs "arm/proofs/sha256_block_core.ml";;

(* Load machine code *)
let sha256_block_simple_mc = define_from_elf "sha256_block_simple_mc"
  (file_on_path !load_path "arm/sha2/sha256_block_simple.o");;

let SIMPLE_EXEC = ARM_MK_EXEC_RULE sha256_block_simple_mc;;

(* ========================================================================= *)
(* Correctness theorem.                                                      *)
(* ========================================================================= *)

(* The precondition uses word_join4 for 128-bit memory reads.                *)
(* State: word_join4 a b c d and word_join4 e f g h at state_ptr.            *)
(* Message: word_join4 m0 m1 m2 m3 etc. at data_ptr (raw LE bytes).         *)
(* The message words used by sha256_block are word_bytereverse m_i.          *)

let SHA256_BLOCK_SIMPLE_CORRECT = prove(
 `!(a:int32) b c d (e:int32) f g h
   (m0:int32) m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
   state_ptr data_ptr kptr pc ret_pc.
   ALL (nonoverlapping (state_ptr, 32))
       [(word pc, 488); (data_ptr, 64); (kptr, 256)] /\
   nonoverlapping (data_ptr, 64) (word pc, 488) /\
   nonoverlapping (kptr, 256) (word pc, 488)
   ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) sha256_block_simple_mc /\
         read PC s = word pc /\
         read X30 s = word ret_pc /\
         read X0 s = state_ptr /\
         read X1 s = data_ptr /\
         read X2 s = kptr /\
         (* State in memory *)
         read (memory :> bytes128 state_ptr) s = word_join4 a b c d /\
         read (memory :> bytes128 (word_add state_ptr (word 16))) s =
           word_join4 e f g h /\
         (* Message data in memory (raw little-endian) *)
         read (memory :> bytes128 data_ptr) s = word_join4 m0 m1 m2 m3 /\
         read (memory :> bytes128 (word_add data_ptr (word 16))) s =
           word_join4 m4 m5 m6 m7 /\
         read (memory :> bytes128 (word_add data_ptr (word 32))) s =
           word_join4 m8 m9 m10 m11 /\
         read (memory :> bytes128 (word_add data_ptr (word 48))) s =
           word_join4 m12 m13 m14 m15 /\
         (* K constant table in memory *)
         (!i. i < 16 ==>
           read (memory :> bytes128 (word_add kptr (word(16 * i)))) s =
           word_join4 (EL (4*i) sha256_K) (EL (4*i+1) sha256_K)
                      (EL (4*i+2) sha256_K) (EL (4*i+3) sha256_K)))
    (\s. read PC s = word ret_pc /\
         (let M = [word_bytereverse m0; word_bytereverse m1;
                   word_bytereverse m2; word_bytereverse m3;
                   word_bytereverse m4; word_bytereverse m5;
                   word_bytereverse m6; word_bytereverse m7;
                   word_bytereverse m8; word_bytereverse m9;
                   word_bytereverse m10; word_bytereverse m11;
                   word_bytereverse m12; word_bytereverse m13;
                   word_bytereverse m14; word_bytereverse m15] in
          let H = [a;b;c;d;e;f;g;h] in
          let result = sha256_block M H in
          read (memory :> bytes128 state_ptr) s =
            word_join4 (EL 0 result) (EL 1 result)
                       (EL 2 result) (EL 3 result) /\
          read (memory :> bytes128 (word_add state_ptr (word 16))) s =
            word_join4 (EL 4 result) (EL 5 result)
                       (EL 6 result) (EL 7 result)))
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q18; Q19] ,,
     MAYCHANGE [memory :> bytes(state_ptr, 32)] ,,
     MAYCHANGE [events])`,

  (* TODO: Proof follows the same cut-point structure as sha256_block_core,
     with additional steps for memory loads (1-6), REV32 (7-10),
     MOV x1,x2 (11), stores (121-122), and RET (123).
     The REV32 byte-swap is handled by word_bytereverse in the postcondition.
     Memory nonoverlapping conditions ensure loads/stores don't interfere. *)
  CHEAT_TAC);;
