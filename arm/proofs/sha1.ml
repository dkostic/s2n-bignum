(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(** ARM SHA1 cryptographic-extension instruction semantics in HOL Light **)

needs "Library/words.ml";;

(****************************************************)
(**                                                **)
(**  COMMONLY USED FUNCTIONS FOR SHA1 INTRINSICS   **)
(**                                                **)
(****************************************************)

(** Ch(x,y,z) = (x AND y) XOR ((NOT x) AND z)  -- FIPS 180-4 Sec 4.1.1.    **)
let sha1_choose = new_definition
  `sha1_choose (x:int32) (y:int32) (z:int32) : int32 =
          word_xor (word_and (word_xor y z) x) z`;;

(** Parity(x,y,z) = x XOR y XOR z  -- FIPS 180-4 Sec 4.1.1.                **)
let sha1_parity = new_definition
  `sha1_parity (x:int32) (y:int32) (z:int32) : int32 =
          word_xor (word_xor x y) z`;;

(** Maj(x,y,z) = (x AND y) XOR (x AND z) XOR (y AND z)  -- FIPS 180-4 4.1.1**)
let sha1_majority = new_definition
  `sha1_majority (x:int32) (y:int32) (z:int32) : int32 =
          word_or (word_and x y) (word_and (word_or x y) z)`;;

(** elem grabs a slice of fixed size out of a larger word.                 **)
let sha1_elem = new_definition
  `sha1_elem (w:M word) (e:num) (size:num) : size word =
          word_subword w (e*size, size)`;;

(**
 ** sha1_funct dispatches the round-function based on the encoding selector
 ** ft \in {0,1,2}: 0 -> Ch, 1 -> Parity, 2 -> Maj.
 ** SHA1C uses ft=0 (rounds 0..19), SHA1P uses ft=1 (rounds 20..39 or 60..79),
 ** SHA1M uses ft=2 (rounds 40..59).  A single-byte selector is enough; the
 ** loop index t below is per-round (0..3) within one instruction.
 **)
let sha1_funct = new_definition
  `sha1_funct (ft:num) (b:int32) (c:int32) (d:int32) : int32 =
          if ft = 0 then sha1_choose b c d
          else if ft = 1 then sha1_parity b c d
          else sha1_majority b c d`;;

(**
 **  ARM pseudocode shape for SHA1C / SHA1P / SHA1M (per ARMv8 reference):
 **
 **  bits(128) SHA1hashUpdateChoose(bits(128) X, bits(32) Y, bits(128) W)
 **      bits(32) t;
 **      for e = 0 to 3
 **          t = SHAchoose(X<63:32>, X<95:64>, X<127:96>);
 **          Y = Y + ROL(X<31:0>, 5);
 **          Y = Y + t + Elem[W, e, 32];
 **          X<63:32> = ROL(X<63:32>, 30);   // (a)  rotates b -> c slot
 **          // Rotate full state down by one lane and put new word on top:
 **          //   <X, Y> = ROL(<X, Y>, 32)
 **          // i.e. new X = (Y, X<127:32>),  new Y = X<31:0>
 **      return X;
 **
 **  We implement one round of this loop.  Given x:int128 packing the four
 **  state words (a in <31:0>, b in <63:32>, c in <95:64>, d in <127:96>) and
 **  y:int32 holding the e word, we compute the next (x', y') such that the
 **  new x' has fields (T, a, ROL30(b), c) and the new y' = d. The instruction
 **  variants differ only in which f-function is used, captured by ft.
 **
 **  This matches the Cryptol mixOne semantics 1-for-1: after one round we
 **  have (a', b', c', d', e') = (T, a, ROL30(b), c, d).  After 4 rounds in
 **  one ARM SHA1{C,P,M} instruction the X register holds (T_3, T_2, ROL30(T_1),
 **  ROL30(T_0)), i.e. exactly the new (a,b,c,d) per FIPS 180-4 sequencing,
 **  while the new e = ROL30(a_old) is supplied by the preceding SHA1H
 **  instruction.
 **)
let sha1hash_loop = new_definition
  `sha1hash_loop (ft:num) (e:num) (x:int128) (y:int32) (w:int128) : 160 word =
          let a:int32 = word_subword x (0,32) in
          let b:int32 = word_subword x (32,32) in
          let c:int32 = word_subword x (64,32) in
          let d:int32 = word_subword x (96,32) in
          let f:int32 = sha1_funct ft b c d in
          let t:int32 = word_add y
                          (word_add (word_rol a 5)
                            (word_add f (sha1_elem w e 32))) in
          let new_a:int32 = t in
          let new_b:int32 = a in
          let new_c:int32 = word_rol b 30 in
          let new_d:int32 = c in
          let new_e:int32 = d in
          let new_x:int128 =
            (word_join:int32->96 word->int128) new_d
              ((word_join:int32->64 word->96 word) new_c
                ((word_join:int32->int32->64 word) new_b new_a)) in
          (word_join:int32->int128->160 word) new_e new_x`;;

(**
 ** Apply 4 rounds of the SHA1 mix-step driven by ft.  Returns the post-loop
 ** 160-bit packed (e:x).
 **)
let sha1hash = new_definition
  `sha1hash (ft:num) (x:int128) (y:int32) (w:int128) : 160 word =
          let xy0:160 word = sha1hash_loop ft 0 x y w in
          let x:int128 = word_subword xy0 (0,128) in
          let y:int32  = word_subword xy0 (128,32) in

          let xy1:160 word = sha1hash_loop ft 1 x y w in
          let x:int128 = word_subword xy1 (0,128) in
          let y:int32  = word_subword xy1 (128,32) in

          let xy2:160 word = sha1hash_loop ft 2 x y w in
          let x:int128 = word_subword xy2 (0,128) in
          let y:int32  = word_subword xy2 (128,32) in

          let xy3:160 word = sha1hash_loop ft 3 x y w in
          xy3`;;


(*************************)
(**                     **)
(**  SHA1 INTRINSICS    **)
(**                     **)
(*************************)

(**
 ** SHA1C Vd.4S, Sn, Vm.4S
 **
 ** d : 128-bit destination = (a, b, c, d) packed words
 ** n : 32-bit  scalar (e in lane 0)
 ** m : 128-bit input W (4 message words pre-summed with K)
 ** Result : new 128-bit state (a, b, c, d) after 4 rounds with f = Ch.
 **)
let sha1c = define
  `sha1c (d:int128) (n:int32) (m:int128) : int128 =
          word_subword (sha1hash 0 d n m) (0,128)`;;

(** SHA1P : same as SHA1C but f = Parity.                                  **)
let sha1p = define
  `sha1p (d:int128) (n:int32) (m:int128) : int128 =
          word_subword (sha1hash 1 d n m) (0,128)`;;

(** SHA1M : same as SHA1C but f = Majority.                                **)
let sha1m = define
  `sha1m (d:int128) (n:int32) (m:int128) : int128 =
          word_subword (sha1hash 2 d n m) (0,128)`;;

(**
 ** SHA1H  Sd, Sn
 **
 ** Performs ROL(Sn<31:0>, 30) and writes it to Sd<31:0>.  The upper 96 bits
 ** of the destination Q register are zeroed (per ARMv8 Q-register
 ** architectural rule for 32-bit SIMD ops).  We model the instruction as
 ** taking an int128 (Vn) and producing an int128 (Vd) so it composes with
 ** the rest of the SHA1 vector pipeline.
 **)
let sha1h = define
  `sha1h (d:int128) : int128 =
          (word_join:96 word->int32->int128)
            (word 0)
            (word_rol (word_subword d (0,32):int32) 30)`;;

(**
 ** SHA1SU0 Vd.4S, Vn.4S, Vm.4S  -- Schedule Update 0
 **
 **  Operation
 **    bits(128) operand1 = V[d];      // current four W-words
 **    bits(128) operand2 = V[n];      // next four W-words
 **    bits(128) operand3 = V[m];      // following four W-words
 **    bits(128) result;
 **    bits(128) T = operand2<31:0> : operand1<127:32>;  // shift in by 32
 **    result = T EOR operand1 EOR operand3;
 **    V[d] = result;
 **
 **  Equivalently, T is the byte-extract of (operand1 || operand2) at offset
 **  4 bytes (this is the EXT instruction semantics with imm=8 in bytes).
 **)
let sha1su0 = define
  `sha1su0 (d:int128) (n:int128) (m:int128) : int128 =
          let t:int128 =
            (word_join:int32->96 word->int128)
              (word_subword n (0,32))
              (word_subword d (32,96)) in
          word_xor t (word_xor d m)`;;

(**
 ** SHA1SU1 Vd.4S, Vn.4S  -- Schedule Update 1
 **
 **  Operation
 **    bits(128) operand1 = V[d];     // partial schedule from SHA1SU0
 **    bits(128) operand2 = V[n];     // last four W-words
 **    bits(128) result;
 **    bits(128) T0  = operand1 EOR ((operand2<127:32>) : 0<31:0>);
 **    // T0 lanes are the four pre-rotation candidates W[i-3]^W[i-8]^...
 **    // Then ROL each lane by 1, except the top lane also XORs ROL2 of
 **    // the bottom lane (because the top lane's W[i-3] hasn't been
 **    // computed yet -- ARM uses W[i-3] = ROL1(low lane T0) = ROL1(W[i-3]
 **    // candidate) and so the contribution is ROL1(ROL1(low T0)) = ROL2.
 **    Elem[result, 0, 32] = ROL(Elem[T0, 0, 32], 1);
 **    Elem[result, 1, 32] = ROL(Elem[T0, 1, 32], 1);
 **    Elem[result, 2, 32] = ROL(Elem[T0, 2, 32], 1);
 **    Elem[result, 3, 32] = ROL(Elem[T0, 3, 32], 1) EOR
 **                          ROL(Elem[T0, 0, 32], 2);
 **    V[d] = result;
 **)
let sha1su1 = define
  `sha1su1 (d:int128) (n:int128) : int128 =
          let t0_0:int32 = word_subword d (0,32) in
          let t0_1:int32 = word_subword d (32,32) in
          let t0_2:int32 = word_subword d (64,32) in
          let t0_3:int32 = word_xor (word_subword d (96,32))
                                    (word_subword n (32,32):int32) in
          let r0:int32 = word_rol t0_0 1 in
          let r1:int32 = word_rol t0_1 1 in
          let r2:int32 = word_rol t0_2 1 in
          let r3:int32 = word_xor (word_rol t0_3 1) (word_rol t0_0 2) in
          (word_join:int32->96 word->int128) r3
            ((word_join:int32->64 word->96 word) r2
               ((word_join:int32->int32->64 word) r1 r0))`;;


(************************************************)
(**                                            **)
(**  CONVERSIONS FOR REDUCING SHA1 INTRINSICS  **)
(**                                            **)
(************************************************)

(** Reduce template for common functions **)
let SHA1_COMMON_REDUCE func =
        REWR_CONV func THENC
        DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let SHA1_CHOOSE_REDUCE = SHA1_COMMON_REDUCE sha1_choose;;
let SHA1_PARITY_REDUCE = SHA1_COMMON_REDUCE sha1_parity;;
let SHA1_MAJ_REDUCE    = SHA1_COMMON_REDUCE sha1_majority;;
let SHA1_FUNCT_REDUCE  =
        REWR_CONV sha1_funct THENC
        DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
        ONCE_REWRITE_CONV
          [TAUT `(if T then a else b) = a`; TAUT `(if F then a else b) = b`] THENC
        TRY_CONV (SHA1_COMMON_REDUCE sha1_choose) THENC
        TRY_CONV (SHA1_COMMON_REDUCE sha1_parity) THENC
        TRY_CONV (SHA1_COMMON_REDUCE sha1_majority);;
let SHA1_ELEM_REDUCE   = SHA1_COMMON_REDUCE sha1_elem;;

let SHA1_BASE_REDUCE =
        SHA1_CHOOSE_REDUCE ORELSEC
        SHA1_PARITY_REDUCE ORELSEC
        SHA1_MAJ_REDUCE ORELSEC
        SHA1_FUNCT_REDUCE ORELSEC
        SHA1_ELEM_REDUCE;;

(** Reduce a single sha1hash_loop application. **)
let SHA1_REDUCE_LOOP =
    REWR_CONV sha1hash_loop THENC
    DEPTH_CONV (let_CONV ORELSEC SHA1_BASE_REDUCE ORELSEC NUM_RED_CONV) THENC
    WORD_REDUCE_CONV;;

(** Reduce "let x = e in f" by first reducing "e" via conv and then
    expanding the let-term (assuming a single bound variable in the let). **)
let SHA1_REDUCE_SUBLET_CONV conv tm =
  if is_let tm then (RAND_CONV conv THENC let_CONV) tm
  else failwith "SHA1_REDUCE_SUBLET_CONV: not a toplevel let-term";;

let SHA1_HASH_REDUCE =
    REWR_CONV sha1hash THENC
    REPEATC (SHA1_REDUCE_SUBLET_CONV
               (SHA1_REDUCE_LOOP ORELSEC WORD_RED_CONV ORELSEC
                SHA1_BASE_REDUCE)) THENC
    ONCE_SIMP_CONV [];;

(** For sha1{c,p,m}: unfold sha1{c,p,m} once, then expand the inner
    sha1hash via SHA1_HASH_REDUCE applied at the right depth (it sits
    underneath word_subword). **)
let SHA1C_RED_CONV =
        REWR_CONV sha1c THENC
        ONCE_DEPTH_CONV SHA1_HASH_REDUCE THENC
        WORD_REDUCE_CONV;;

let SHA1C_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha1c",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA1C_RED_CONV tm
    | _ -> failwith "SHA1C_REDUCE_CONV: inapplicable";;

let SHA1P_RED_CONV =
        REWR_CONV sha1p THENC
        ONCE_DEPTH_CONV SHA1_HASH_REDUCE THENC
        WORD_REDUCE_CONV;;

let SHA1P_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha1p",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA1P_RED_CONV tm
    | _ -> failwith "SHA1P_REDUCE_CONV: inapplicable";;

let SHA1M_RED_CONV =
        REWR_CONV sha1m THENC
        ONCE_DEPTH_CONV SHA1_HASH_REDUCE THENC
        WORD_REDUCE_CONV;;

let SHA1M_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha1m",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA1M_RED_CONV tm
    | _ -> failwith "SHA1M_REDUCE_CONV: inapplicable";;

let SHA1H_RED_CONV =
        REWR_CONV sha1h THENC
        DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA1H_REDUCE_CONV tm =
      match tm with
        Comb(Const("sha1h",_),Comb(Const("word",_),d))
      when is_numeral d -> SHA1H_RED_CONV tm
    | _ -> failwith "SHA1H_REDUCE_CONV: inapplicable";;

let SHA1SU0_RED_CONV =
        REWR_CONV sha1su0 THENC
        DEPTH_CONV (let_CONV ORELSEC WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA1SU0_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Comb(Const("sha1su0",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n)),
                  Comb(Const("word",_),m))
      when is_numeral d && is_numeral n && is_numeral m -> SHA1SU0_RED_CONV tm
    | _ -> failwith "SHA1SU0_REDUCE_CONV: inapplicable";;

let SHA1SU1_RED_CONV =
        REWR_CONV sha1su1 THENC
        DEPTH_CONV (let_CONV ORELSEC WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
        WORD_REDUCE_CONV;;

let SHA1SU1_REDUCE_CONV tm =
      match tm with
        Comb(Comb(Const("sha1su1",_),
                  Comb(Const("word",_),d)),
                  Comb(Const("word",_),n))
      when is_numeral d && is_numeral n -> SHA1SU1_RED_CONV tm
    | _ -> failwith "SHA1SU1_REDUCE_CONV: inapplicable";;
