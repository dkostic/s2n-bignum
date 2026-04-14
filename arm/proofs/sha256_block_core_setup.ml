(* Setup for interactive sha256_block_core proof *)
needs "arm/proofs/utils/sha256_bridge.ml";;

let sha256_block_core_mc = define_from_elf "sha256_block_core_mc"
  "/home/ubuntu/workspace/whole-crypto/s2n-bignum/arm/sha2/sha256_block_core.o";;
let EXEC = ARM_MK_EXEC_RULE sha256_block_core_mc;;
let ADD_SIMP_RULE = REWRITE_RULE[WORD_JOIN4_SUBWORD; WORD_JOIN_4x32];;

let SHA256_COMPRESS_ROUND_PREADD_SYM = prove(
  `!W_t K_t state. sha256_compress_round (word_add W_t K_t) (word 0:int32) state =
                   sha256_compress_round K_t W_t state`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_RULE `word_add (W:int32) K = word_add K W`] THEN
  REWRITE_TAC[SHA256_COMPRESS_ROUND_PREADD]);;

let SHA256H_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_BRIDGE;;
let SHA256H2_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H2_BRIDGE;;

(* Only bridge assumptions containing sha256h or sha256h2 *)
let bridge_Q0Q1 th =
  let c = concl th in
  if can (find_term (fun t -> try fst(dest_const t) = "sha256h" with _ -> false)) c
  then
    let th1 = REWRITE_RULE[SHA256H_BRIDGE_FLAT; SHA256H2_BRIDGE_FLAT] th in
    REWRITE_RULE[SHA256_COMPRESS_ROUND_PREADD_SYM] th1
  else th;;

let rec SHA256_COMPRESS_UNROLL_CONV tm =
  let n_tm = rand(rator(rator tm)) in
  if n_tm = `0` then REWRITE_CONV[sha256_compress] tm
  else
    let n = dest_small_numeral n_tm in
    let arith_th = ARITH_RULE
      (mk_eq(n_tm, mk_comb(mk_comb(`(+)`, mk_small_numeral(n-1)), `1`))) in
    let step1 = ONCE_REWRITE_CONV[arith_th] tm in
    let step2 = CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[sha256_compress])) step1 in
    CONV_RULE(RAND_CONV(RAND_CONV SHA256_COMPRESS_UNROLL_CONV)) step2;;

(* Incremental fold4: fold 4 compress_round calls on top of sha256_compress(4*i) *)
let COMPRESS_FOLD4 =
  let mk i =
    let base = 4 * i and target = 4 * (i + 1) in
    let target_tm = mk_small_numeral target and base_tm = mk_small_numeral base in
    let target_term = list_mk_comb(`sha256_compress`,
      [target_tm; `W:int32 list`; `state:int32 list`]) in
    let full_unroll = SHA256_COMPRESS_UNROLL_CONV target_term in
    if i = 0 then GSYM full_unroll
    else
      let base_unroll = SHA256_COMPRESS_UNROLL_CONV
        (list_mk_comb(`sha256_compress`, [base_tm; `W:int32 list`; `state:int32 list`])) in
      GSYM(CONV_RULE(RAND_CONV(ONCE_REWRITE_CONV[GSYM base_unroll])) full_unroll) in
  Array.init 16 mk;;
