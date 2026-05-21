(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load basic background needed for the ARM bignum proofs.                   *)
(* ========================================================================= *)

loads "update_database.ml";;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some background theory from the standard libraries.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
loadt "Library/records.ml";;

(* ------------------------------------------------------------------------- *)
(* common ARM-x86 proof infrastructure.                                      *)
(* ------------------------------------------------------------------------- *)

loadt "common/overlap.ml";;
loadt "common/for_hollight.ml";;
loadt "common/words2.ml";;
loadt "common/misc.ml";;
loadt "common/components.ml";;
loadt "common/alignment.ml";;
loadt "common/relational.ml";;
loadt "common/interval.ml";;
loadt "common/elf.ml";;
loadt "common/safety.ml";;

(* ------------------------------------------------------------------------- *)
(* Support for additional SHA intrinsics (from Carl Kwan)                    *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/sha256.ml";;
loadt "arm/proofs/sha512.ml";;
(* Adding extra conversions for SHA intrinsics *)
extra_word_CONV :=
        [SHA256H_REDUCE_CONV;
         SHA256H2_REDUCE_CONV;
         SHA256SU0_REDUCE_CONV;
         SHA256SU1_REDUCE_CONV;
         SHA512H_REDUCE_CONV;
         SHA512H2_REDUCE_CONV;
         SHA512SU0_REDUCE_CONV;
         SHA512SU1_REDUCE_CONV]
        @ (!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* Additional Cryptographic AES intrinsics                                   *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/utils/aes.ml";;

extra_word_CONV := [AESE_REDUCE_CONV; AESMC_REDUCE_CONV;
                    AESD_REDUCE_CONV; AESIMC_REDUCE_CONV]
                    @ (!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* SHA-1 cryptographic-extension semantics. Loaded BEFORE instruction.ml so  *)
(* the arm_SHA1* constructors there can reference sha1{c,p,m,h,su0,su1}.     *)
(* (sha256.ml and sha512.ml are loaded above, before this point, and so      *)
(* play the same role for their respective constructors.)                    *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/sha1.ml";;
extra_word_CONV :=
        [SHA1C_REDUCE_CONV;
         SHA1P_REDUCE_CONV;
         SHA1M_REDUCE_CONV;
         SHA1H_REDUCE_CONV;
         SHA1SU0_REDUCE_CONV;
         SHA1SU1_REDUCE_CONV]
        @ (!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* The main ARM model.                                                       *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/instruction.ml";;
loadt "arm/proofs/decode.ml";;
loadt "arm/proofs/arm.ml";;

(* ------------------------------------------------------------------------- *)
(* Bignum material and standard overloading                                  *)
(* ------------------------------------------------------------------------- *)

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/bignum.ml";;
