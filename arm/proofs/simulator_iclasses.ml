(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* The iclasses to simulate.                                                 *)
(* ------------------------------------------------------------------------- *)

let iclasses =
 [
  (*** PMULL, size=00 (8-bit elements) ***)
  "00001110001xxxxx111000xxxxxxxxxx";

  (*** PMULL, size=11 (64-bit elements) ***)
  "00001110111xxxxx111000xxxxxxxxxx";

  (*** PMULL2, size=00 (8-bit elements) ***)
  "01001110001xxxxx111000xxxxxxxxxx";

  (*** PMULL2, size=11 (64-bit elements) ***)
  "01001110111xxxxx111000xxxxxxxxxx";
];;


let match_bitpattern =
  let idxs = List.init 32 (fun x->x) in
  fun (opcode:int) (bitpat:string) ->
    List.for_all (fun i ->
        let bitpat = bitpat.[31 - i] and
            bit = (opcode lsr i) land 1 in
        bitpat = 'x' ||
        (bit = 1 && bitpat = '1') ||
        (bit = 0 && bitpat = '0'))
      idxs;;

(* Check that assembly instructions in s2n-bignum object files appear at
   iclasses. *)

let check_insns () =
  (* These commands are not going to be simulated. *)
  let skipping_iclasses = [
    (*** adr ***)
    "0xx10000xxxxxxxxxxxxxxxxxxxxxxxx";

    (*** adrp ***)
    "1xx10000xxxxxxxxxxxxxxxxxxxxxxxx";

    (*** b ***)
    "000101xxxxxxxxxxxxxxxxxxxxxxxxxx";

    (*** bl ***)
    "100101xxxxxxxxxxxxxxxxxxxxxxxxxx";

    (*** b.cond ***)
    "01010100xxxxxxxxxxxxxxxxxxx0xxxx";

    (*** cbz, cbnz ***)
    "10110100xxxxxxxxxxxxxxxxxxxxxxxx";
    "10110101xxxxxxxxxxxxxxxxxxxxxxxx";

    (*** ldp ***)
    "x010100x1xxxxxxxxxxxxxxxxxxxxxxx"; (* Preimmediate_Offset or Postimmediate_Offset *)
    "x01010010xxxxxxxxxxxxxxxxxxxxxxx"; (* Immediate_Offset *)

    (*** ldp (SIMD & FP) ***)
    "xx10110011xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110111xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (immediate ofs) ***)
    "1x111000010xxxxxxxxx01xxxxxxxxxx";
    "1x111000010xxxxxxxxx11xxxxxxxxxx";
    "1x11100101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (immediate ofs, SIMD & FP) ***)
    "xx111100x10xxxxxxxxx01xxxxxxxxxx";
    "xx111100x10xxxxxxxxx11xxxxxxxxxx";
    "xx111101x1xxxxxxxxxxxxxxxxxxxxxx";

    (*** ldr (register ofs) ***)
    "1x111000011xxxxxxxxx10xxxxxxxxxx";

    (*** ldr / str, shifted register, size 128 no extensions ***)
    "001111001x1xxxxx011x10xxxxxxxxxx";

    (*** ldrb (immediate ofs) ***)
    "00111000010xxxxxxxxx01xxxxxxxxxx";
    "00111000010xxxxxxxxx11xxxxxxxxxx";
    "0011100101xxxxxxxxxxxxxxxxxxxxxx";

    (*** ld1 (1 register, Post-immediate offset) ***)
    "0x001100110111110111xxxxxxxxxxxx";

    (*** st1 (1 register, Post-immediate offset) ***)
    "0x001100100111110111xxxxxxxxxxxx";

    (*** ld1 (1 register, Post-register offset) ***)
    "0x001100110xxxxx0111xxxxxxxxxxxx";

    (*** st1 (1 register, Post-register offset) ***)
    "0x001100100xxxxx0111xxxxxxxxxxxx";

    (*** ld1 (1 register, no Post-immediate offset) ***)
    "0x001100010000000111xxxxxxxxxxxx";

    (*** st1 (1 register, no Post-immediate offset) ***)
    "0x001100000000000111xxxxxxxxxxxx";

    (*** ld1 (2 registers, Post-immediate offset) 128-bit ***)
    "01001100110111111010xxxxxxxxxxxx";

    (*** st1 (2 registers, Post-immediate offset) 128-bit ***)
    "01001100100111111010xxxxxxxxxxxx";

    (*** ld2 (2 register, Post-immediate offset) ***)
    "0x001100110111111000xxxxxxxxxxxx";

    (*** st2 (2 register, Post-immediate offset) ***)
    "0x001100100111111000xxxxxxxxxxxx";

    (*** ld1r (post immediate ofs) ***)
    "0x001101110111111100xxxxxxxxxxxx";

    (*** ldur / stur, immediate, size 128 only ***)
    "001111001x0xxxxxxxxx00xxxxxxxxxx";

    (*** ld3 / st3, multiple structures, 3 reg, post-imm and register ***)
    "0x0011001x0xxxxx0100xxxxxxxxxxxx";

    (*** stp ***)
    "x010100010xxxxxxxxxxxxxxxxxxxxxx";
    "x010100110xxxxxxxxxxxxxxxxxxxxxx";
    "x010100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** stp (SIMD & FP) ***)
    "xx10110010xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110110xxxxxxxxxxxxxxxxxxxxxx";
    "xx10110100xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (immediate ofs) ***)
    "1x111000000xxxxxxxxx01xxxxxxxxxx";
    "1x111000000xxxxxxxxx11xxxxxxxxxx";
    "1x11100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (immediate ofs, SIMD & FP) ***)
    "xx111100x00xxxxxxxxx01xxxxxxxxxx";
    "xx111100x00xxxxxxxxx11xxxxxxxxxx";
    "xx111101x0xxxxxxxxxxxxxxxxxxxxxx";

    (*** str (register) ***)
    "1x111000001xxxxxxxxx10xxxxxxxxxx";

    (*** strb (immediate ofs) ***)
    "00111000000xxxxxxxxx01xxxxxxxxxx";
    "00111000000xxxxxxxxx11xxxxxxxxxx";
    "0011100100xxxxxxxxxxxxxxxxxxxxxx";

    (*** sub/add with sp regs ***)
    "xx0100010xxxxxxxxxxxxxxxxxx11111";
    "xx0100010xxxxxxxxxxxxx11111xxxxx";
    "11001011001xxxxxxxxxxx11111xxxxx";

    (*** ret ***)
    "1101011001011111000000xxxxx00000";
  ] in

  (* Check that iclasses and skipping_iclasses has no overlapping bitpattern. *)
  if let char_overlap c1 c2 = c1 = c2 || c1 = 'x' || c2 = 'x' in
      List.exists (fun bitpat1 ->
        List.exists (fun bitpat2 ->
            let range = List.init 32 (fun x->x) in
            if List.for_all (fun i -> char_overlap bitpat1.[i] bitpat2.[i]) range
            then begin
              Printf.eprintf "iclasses and skipping_iclasses overlap!!\n";
              Printf.eprintf "- iclass entry: %s\n" bitpat1;
              Printf.eprintf "- skipping_iclasses entry: %s\n%!" bitpat2;
              true
            end else false)
          skipping_iclasses)
        iclasses
  then failwith "check_insns" else

  let rec traverse_objs dirpath (checkfn:string->unit):unit =
    let dirs = Sys.readdir dirpath in
    Array.iter (fun p ->
        let p = (Filename.concat dirpath p) in
        if Sys.is_directory p then
          traverse_objs p checkfn
        else if Filename.extension p = ".o" && p <> "arm/proofs/simulator.o" then
          checkfn p
        else ()
      ) dirs in

  (* Check whether l (a line of objdump output) is an assembly instruction
     covered by iclasses. *)
  let check_asmline (l:string):bool =
    match String.index_opt l ':' with
    | None -> true
    | Some idx ->
      let l = String.sub l (idx+1) (String.length l - idx - 1) in
      let l = String.trim l in
      match String.index_opt l ' ' with
      | None -> true (* defines label *)
      | Some idx ->
        let hexcode = "0x" ^ (String.sub l 0 idx) in
        let desc = String.trim (String.sub l (idx+1) (String.length l - idx - 1)) in
        if String.starts_with ~prefix:".word" desc then true (* defines a constant *)
        else
          try
            let opcode = int_of_string hexcode in
            if List.exists (match_bitpattern opcode) skipping_iclasses then
              true (* Check passes *)
            else
              List.exists (match_bitpattern opcode) iclasses
          with _ -> false
    in

  let tmppath = Filename.temp_file "objdump" ".txt" in
  let checkfn objpath =
    let cmd = "objdump -d \"" ^ objpath ^ "\" -j .text >" ^ tmppath in
    let exitcode = Sys.command cmd in
    if exitcode <> 0 then begin
      Printf.eprintf "Cannot objdump %s\n%!" objpath;
      failwith "check_insns"
    end else
      (* Read the lines of objdump *)
      let fin = open_in tmppath in
      try
        (* Pass first 6 lines *)
        let count = ref 0 in
        while true; do
          let l = input_line fin in
          count := !count + 1;
          if !count >= 6 then
            if not (check_asmline l) then begin
              Printf.eprintf "Found an assembly that is not covered by iclasses!\n";
              Printf.eprintf "  File: %s\n" objpath;
              Printf.eprintf "  objdump line: %s\n%!" l;
              failwith "check_insns"
            end
        done;
      with End_of_file -> begin
        Printf.printf "Passed: %s\n%!" objpath;
        close_in fin
      end in
  (* Makefile will run this script from the root dir of s2n-bignum/. *)
  traverse_objs "arm/" checkfn;;
