(* Simplify REV32 results in Q4-Q7 using BITBLAST *)
(* After LDR + REV32, Q4 should equal word_join4 of word_bytereverse *)

(* Strategy: prove a general lemma about REV32 on word_join4 *)
(* Then rewrite the Q4-Q7 assumptions *)

let REV32_WORD_JOIN4 = prove(
 `!a b c d:int32.
    word_join4
     (word_join
       (word_subword (word_subword (word_subword (word_join4 a b c d) (0,64)) (0,32)) (0,16))
       (word_subword (word_subword (word_subword (word_join4 a b c d) (0,64)) (0,32)) (16,16)))
     (word_join
       (word_subword (word_subword (word_subword (word_join4 a b c d) (0,64)) (32,32)) (0,16))
       (word_subword (word_subword (word_subword (word_join4 a b c d) (0,64)) (32,32)) (16,16)))
     (word_join
       (word_subword (word_subword (word_subword (word_join4 a b c d) (64,64)) (0,32)) (0,16))
       (word_subword (word_subword (word_subword (word_join4 a b c d) (64,64)) (0,32)) (16,16)))
     (word_join
       (word_subword (word_subword (word_subword (word_join4 a b c d) (64,64)) (32,32)) (0,16))
       (word_subword (word_subword (word_subword (word_join4 a b c d) (64,64)) (32,32)) (16,16)))
   = word_join4 (word_bytereverse a) (word_bytereverse b)
                (word_bytereverse c) (word_bytereverse d)`,
  REWRITE_TAC[word_join4; word_bytereverse] THEN
  REPEAT GEN_TAC THEN
  BITBLAST_THEN (K ALL_TAC) THEN CONV_TAC TAUT);;

let () = Printf.printf "REV32_WORD_JOIN4 proved!\n%!";;
