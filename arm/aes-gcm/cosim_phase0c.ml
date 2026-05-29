(* ========================================================================= *)
(* Phase 0c — focused cosim test for the two new instruction classes.         *)
(*                                                                           *)
(* Tests the 7 distinct opcodes the AES-128 fork emits for the two ISA gaps  *)
(* added in Phase 0b: 6 DUP-from-element scalar (Gap 1) and 1 scalar SHL     *)
(* D-form (Gap 2). Each opcode is run against the hardware (via              *)
(* `arm/proofs/armsimulate`) and the s2n-bignum model 3 times with random   *)
(* register state; PASS = all 3 agree.                                       *)
(*                                                                           *)
(* Usage (from a fresh `holctl` session at /home/ubuntu/whole-proofs/        *)
(* s2n-bignum):                                                              *)
(*                                                                           *)
(*   loadt "arm/proofs/base.ml";;                                            *)
(*   loadt "arm/proofs/simulator_iclasses.ml";;                              *)
(*   loadt "arm/proofs/simulator.ml";;     (* runs random inventory test;    *)
(*                                            interrupt with Ctrl-C after    *)
(*                                            it confirms the iclass cover-  *)
(*                                            age and starts random sim    *)
(*                                            iterations                  *) *)
(*   loadt "arm/aes-gcm/cosim_phase0c.ml";;                                  *)
(*                                                                           *)
(* Success criterion: SUMMARY line reads "PASS 7 / FAIL 0".                  *)
(* ========================================================================= *)

let test_opcodes = [
  ("mov d10, v17.d[1]", Num.num_of_int 0x5e18062a);
  ("mov d8, v4.d[1]",   Num.num_of_int 0x5e180488);
  ("mov d4, v5.d[1]",   Num.num_of_int 0x5e1804a4);
  ("mov d8, v6.d[1]",   Num.num_of_int 0x5e1804c8);
  ("mov d4, v7.d[1]",   Num.num_of_int 0x5e1804e4);
  ("mov d22, v4.d[1]",  Num.num_of_int 0x5e180496);
  ("shl d8, d8, #56",   Num.num_of_int 0x5f785508);
];;

let cosim_pass = ref 0 and cosim_fail = ref 0 in
List.iter (fun (label, opcode) ->
  Format.printf "Testing %s@." label;
  let attempts = ref 0 and ok_count = ref 0 in
  while !attempts < 3 do
    incr attempts;
    let _, result = cosimulate_instructions None [opcode] in
    if result then incr ok_count
  done;
  if !ok_count = 3 then begin
    Format.printf "  PASS (3/3)@."; incr cosim_pass
  end else begin
    Format.printf "  FAIL (%d/3)@." !ok_count; incr cosim_fail
  end
) test_opcodes;
Format.printf "@.SUMMARY: PASS %d / FAIL %d@." !cosim_pass !cosim_fail;;
