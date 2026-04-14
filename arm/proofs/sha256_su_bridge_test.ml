(* Test: apply SHA256SU_BRIDGE to schedule register assumptions *)
let SHA256SU_BRIDGE_FLAT = CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU_BRIDGE;;

(* Rewrite sha256su1 assumptions using SHA256SU_BRIDGE *)
let SU_BRIDGE_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t ->
        try fst(dest_const t) = "sha256su1" with _ -> false)) (concl th)
    then REWRITE_RULE[SHA256SU_BRIDGE_FLAT] th
    else th);;

e(SU_BRIDGE_ASSUM_TAC);;
