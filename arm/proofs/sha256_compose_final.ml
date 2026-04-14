(* Final composition: use FORWARD bridges to expand sha256_compress -> sha256h *)

let fwd_bridges_h = Array.init 16 (fun i ->
  CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H.(i)));;

let fwd_bridges_h2 = Array.init 16 (fun i ->
  CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H2.(i)));;

(* Compose: expand sha256_compress 60 -> sha256h(compress 56), then
   compress 56 -> sha256h(compress 52), etc. down to compress 0 = H *)
let compose_full start =
  List.fold_left (fun th i ->
    CONV_RULE(RAND_CONV(
      ONCE_REWRITE_CONV[fwd_bridges_h.(i); fwd_bridges_h2.(i)])) th)
    start (List.rev (0--14));;

let start_h = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H.(15));;
let start_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H2.(15));;

let FULL_COMPRESS_H = time compose_full start_h;;
let FULL_COMPRESS_H2 = time compose_full start_h2;;

let () =
  let c1 = concl FULL_COMPRESS_H and c2 = concl FULL_COMPRESS_H2 in
  Printf.printf "H:  LHS=%d RHS=%d\nH2: LHS=%d RHS=%d\n%!"
    (String.length(string_of_term(lhand c1)))
    (String.length(string_of_term(rand c1)))
    (String.length(string_of_term(lhand c2)))
    (String.length(string_of_term(rand c2)));;
