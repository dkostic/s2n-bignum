(* Compose bridges step by step: sha256_compress 64 -> sha256h^16 chain *)
(* Each step converts exactly one sha256_compress(4*i) pair into sha256h/sha256h2 *)

(* Apply bridges 14 down to 0 (top-down: expand outermost first) *)
let compose_full_bridge start_bridge =
  List.fold_left (fun th i ->
    let gsym_h_i =
      GSYM(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H.(i))) in
    let gsym_h2_i =
      GSYM(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H2.(i))) in
    CONV_RULE(RAND_CONV(
      ONCE_DEPTH_CONV(REWR_CONV gsym_h_i) THENC
      ONCE_DEPTH_CONV(REWR_CONV gsym_h2_i))) th)
    start_bridge (List.rev (0--14));;

let start_h = CONV_RULE(TOP_DEPTH_CONV let_CONV)
  (SPEC_ALL GROUP_BRIDGE_H.(15));;

let FULL_COMPRESS_H = time compose_full_bridge start_h;;

let () =
  let c = concl FULL_COMPRESS_H in
  Printf.printf "LHS: %d chars, RHS: %d chars\n%!"
    (String.length(string_of_term(lhand c)))
    (String.length(string_of_term(rand c)));;

(* Also compose for H2 half *)
let start_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV)
  (SPEC_ALL GROUP_BRIDGE_H2.(15));;

let FULL_COMPRESS_H2 = time compose_full_bridge start_h2;;

let () =
  let c = concl FULL_COMPRESS_H2 in
  Printf.printf "H2 LHS: %d chars, H2 RHS: %d chars\n%!"
    (String.length(string_of_term(lhand c)))
    (String.length(string_of_term(rand c)));;
