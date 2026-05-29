(* ========================================================================= *)
(* Decoder gap re-probe for the AES-128 fork of aes_gcm_enc_kernel.           *)
(*                                                                           *)
(* Phase 0a (session 001) found two decoder gaps: scalar `mov d, v.d[idx]`   *)
(* (Gap 1, 14 occurrences) and scalar `shl d, d, #amt` (Gap 2, 4             *)
(* occurrences). Phase 0b (session 002) added rows for both. This script     *)
(* re-runs `decode_all` on the full 613-instruction byte list and a          *)
(* per-opcode `DECODE_CONV` pass and checks that every instruction decodes   *)
(* successfully.                                                              *)
(*                                                                           *)
(* Usage (from a fresh `holctl` session at `/home/ubuntu/whole-proofs/       *)
(* s2n-bignum`, with `arm/proofs/base.ml` already loaded):                   *)
(*                                                                           *)
(*   loadt "arm/aes-gcm/probe_decoder.ml";;                                  *)
(*                                                                           *)
(* Success criterion: `OK: 613, FAIL: 0`. Any FAIL means the decoder is     *)
(* incomplete; the failure message identifies the rejected opcode.          *)
(* ========================================================================= *)

let probe_aes_gcm_enc_kernel_aes128 () =
  let bs = load_elf_contents_arm "arm/aes-gcm/aes_gcm_enc_kernel_aes128.o" in
  let bt = term_of_bytes bs in
  (* Strict total-decode check: decode_all fails on the first decoder
     rejection. *)
  (try
    let asts = decode_all bt in
    Format.printf "decode_all: OK, %d instructions@."
                  (List.length asts)
  with Failure msg ->
    Format.printf "decode_all: FAIL: %s@." msg);
  (* Per-opcode probe: continues past failures so we get the full FAIL
     list in one pass. *)
  let rec word_of_4bytes = function
    | a :: b :: c :: d :: tl ->
        let bl = mk_list ([a; b; c; d], `:byte`) in
        let th = READ_WORD_CONV (mk_comb (`read_int32`, bl)) in
        let w = fst (dest_pair (rand (rhs (concl th)))) in
        w :: word_of_4bytes tl
    | [] -> []
    | _ -> failwith "byte list not multiple of 4"
  in
  let words = word_of_4bytes (dest_list bt) in
  let ok = ref 0 in
  let fail = ref 0 in
  let fail_opcodes = ref [] in
  List.iter (fun w ->
    let tm = mk_comb (`decode`, w) in
    try
      let _ = DECODE_CONV tm in
      incr ok
    with Failure _ ->
      incr fail;
      fail_opcodes := (string_of_term w) :: !fail_opcodes
  ) words;
  Format.printf "per-opcode: OK %d / FAIL %d (total %d)@."
                !ok !fail (!ok + !fail);
  if !fail > 0 then
    Format.printf "  failing opcodes: %s@."
      (String.concat ", " (List.rev !fail_opcodes));;

probe_aes_gcm_enc_kernel_aes128 ();;
