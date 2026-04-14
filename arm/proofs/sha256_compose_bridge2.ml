(* Full composition: sha256_compress 64 = sha256h^16 chain *)
(* Apply all GSYM bridges simultaneously *)

let all_gsym_h = List.map (fun i ->
  GSYM(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H.(i)))) (0--15);;
let all_gsym_h2 = List.map (fun i ->
  GSYM(CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H2.(i)))) (0--15);;

(* Start from group 15 bridge, rewrite all intermediate sha256_compress terms *)
let start_h = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H.(15));;
let FULL_COMPRESS_H = time (REWRITE_RULE (all_gsym_h @ all_gsym_h2)) start_h;;

let () = Printf.printf "FULL_COMPRESS_H RHS length: %d\n%!"
  (String.length(string_of_term(rand(concl FULL_COMPRESS_H))));;

(* Same for H2 half *)
let start_h2 = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL GROUP_BRIDGE_H2.(15));;
let FULL_COMPRESS_H2 = time (REWRITE_RULE (all_gsym_h @ all_gsym_h2)) start_h2;;

let () = Printf.printf "FULL_COMPRESS_H2 RHS length: %d\n%!"
  (String.length(string_of_term(rand(concl FULL_COMPRESS_H2))));;
