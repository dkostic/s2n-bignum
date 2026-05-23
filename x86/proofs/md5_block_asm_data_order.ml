(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MD5 inner block-compression routine (RFC 1321), x86-64 scalar.            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/md5_spec.ml";;
needs "x86/proofs/utils/md5_bridge.ml";;

(**** print_literal_from_elf "x86/md5/md5_block_asm_data_order.o";;
****)

let md5_block_asm_data_order_mc = define_assert_from_elf
  "md5_block_asm_data_order_mc" "x86/md5/md5_block_asm_data_order.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xfd;        (* MOV (% rbp) (% rdi) *)
  0x48; 0xc1; 0xe2; 0x06;  (* SHL (% rdx) (Imm8 (word 6)) *)
  0x48; 0x8d; 0x3c; 0x16;  (* LEA (% rdi) (%%% (rsi,0,rdx)) *)
  0x8b; 0x45; 0x00;        (* MOV (% eax) (Memop Doubleword (%% (rbp,0))) *)
  0x8b; 0x5d; 0x04;        (* MOV (% ebx) (Memop Doubleword (%% (rbp,4))) *)
  0x8b; 0x4d; 0x08;        (* MOV (% ecx) (Memop Doubleword (%% (rbp,8))) *)
  0x8b; 0x55; 0x0c;        (* MOV (% edx) (Memop Doubleword (%% (rbp,12))) *)
  0x48; 0x39; 0xfe;        (* CMP (% rsi) (% rdi) *)
  0x0f; 0x84; 0xa2; 0x08; 0x00; 0x00;
                           (* JE (Imm32 (word 2210)) *)
  0x41; 0x89; 0xc0;        (* MOV (% r8d) (% eax) *)
  0x41; 0x89; 0xd9;        (* MOV (% r9d) (% ebx) *)
  0x41; 0x89; 0xce;        (* MOV (% r14d) (% ecx) *)
  0x41; 0x89; 0xd7;        (* MOV (% r15d) (% edx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x78; 0xa4; 0x6a; 0xd7;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &680876936)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x56; 0xb7; 0xc7; 0xe8;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &389564586)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xdb; 0x70; 0x20; 0x24;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&606105819)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xee; 0xce; 0xbd; 0xc1;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1044525330)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xaf; 0x0f; 0x7c; 0xf5;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &176418897)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x2a; 0xc6; 0x87; 0x47;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1200080426)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x13; 0x46; 0x30; 0xa8;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1473231341)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x01; 0x95; 0x46; 0xfd;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &45705983)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xd8; 0x98; 0x80; 0x69;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1770035416)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xaf; 0xf7; 0x44; 0x8b;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1958414417)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xb1; 0x5b; 0xff; 0xff;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &42063)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xbe; 0xd7; 0x5c; 0x89;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1990404162)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x22; 0x11; 0x90; 0x6b;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1804603682)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x93; 0x71; 0x98; 0xfd;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &40341101)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x8e; 0x43; 0x79; 0xa6;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1502002290)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x21; 0x08; 0xb4; 0x49;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1236535329)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x62; 0x25; 0x1e; 0xf6;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &165796510)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0x40; 0xb3; 0x40; 0xc0;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1069501632)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x51; 0x5a; 0x5e; 0x26;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&643717713)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xaa; 0xc7; 0xb6; 0xe9;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &373897302)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x5d; 0x10; 0x2f; 0xd6;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &701558691)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0x53; 0x14; 0x44; 0x02;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&38016083)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x81; 0xe6; 0xa1; 0xd8;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &660478335)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xc8; 0xfb; 0xd3; 0xe7;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &405537848)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0xe6; 0xcd; 0xe1; 0x21;
                           (* LEA (% eax) (%%%% (rax,0,r10,&568446438)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0xd6; 0x07; 0x37; 0xc3;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1019803690)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x87; 0x0d; 0xd5; 0xf4;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &187363961)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xed; 0x14; 0x5a; 0x45;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1163531501)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x05; 0xe9; 0xe3; 0xa9;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &1444681467)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0xf8; 0xa3; 0xef; 0xfc;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &51403784)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0xd9; 0x02; 0x6f; 0x67;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&1735328473)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0x8a; 0x4c; 0x2a; 0x8d;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1926607734)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x42; 0x39; 0xfa; 0xff;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &378558)) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x81; 0xf6; 0x71; 0x87;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &2022574463)) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x22; 0x61; 0x9d; 0x6d;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&1839030562)) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x0c; 0x38; 0xe5; 0xfd;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &35309556)) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x44; 0xea; 0xbe; 0xa4;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &1530992060)) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xa9; 0xcf; 0xde; 0x4b;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1272893353)) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x60; 0x4b; 0xbb; 0xf6;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &155497632)) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x70; 0xbc; 0xbf; 0xbe;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1094730640)) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xc6; 0x7e; 0x9b; 0x28;
                           (* LEA (% eax) (%%%% (rax,0,r10,&681279174)) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xfa; 0x27; 0xa1; 0xea;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &358537222)) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x85; 0x30; 0xef; 0xd4;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &722521979)) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x05; 0x1d; 0x88; 0x04;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&76029189)) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x39; 0xd0; 0xd4; 0xd9;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &640364487)) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xe5; 0x99; 0xdb; 0xe6;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &421815835)) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xf8; 0x7c; 0xa2; 0x1f;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&530742520)) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x65; 0x56; 0xac; 0xc4;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &995338651)) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x84; 0x10; 0x44; 0x22; 0x29; 0xf4;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &198630844)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x97; 0xff; 0x2a; 0x43;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1126891415)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xa7; 0x23; 0x94; 0xab;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1416354905)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x39; 0xa0; 0x93; 0xfc;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &57434055)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xc3; 0x59; 0x5b; 0x65;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1700485571)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x92; 0xcc; 0x0c; 0x8f;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1894986606)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x7d; 0xf4; 0xef; 0xff;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1051523)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xd1; 0x5d; 0x84; 0x85;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &2054922799)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x4f; 0x7e; 0xa8; 0x6f;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1873313359)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xe0; 0xe6; 0x2c; 0xfe;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &30611744)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x14; 0x43; 0x01; 0xa3;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1560198380)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xa1; 0x11; 0x08; 0x4e;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1309151649)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x82; 0x7e; 0x53; 0xf7;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &145523070)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x35; 0xf2; 0x3a; 0xbd;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1120210379)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xbb; 0xd2; 0xd7; 0x2a;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&718787259)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x91; 0xd3; 0x86; 0xeb;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &343485551)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x01; 0xc0;        (* ADD (% eax) (% r8d) *)
  0x44; 0x01; 0xcb;        (* ADD (% ebx) (% r9d) *)
  0x44; 0x01; 0xf1;        (* ADD (% ecx) (% r14d) *)
  0x44; 0x01; 0xfa;        (* ADD (% edx) (% r15d) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x39; 0xfe;        (* CMP (% rsi) (% rdi) *)
  0x0f; 0x82; 0x5e; 0xf7; 0xff; 0xff;
                           (* JB (Imm32 (word 4294965086)) *)
  0x89; 0x45; 0x00;        (* MOV (Memop Doubleword (%% (rbp,0))) (% eax) *)
  0x89; 0x5d; 0x04;        (* MOV (Memop Doubleword (%% (rbp,4))) (% ebx) *)
  0x89; 0x4d; 0x08;        (* MOV (Memop Doubleword (%% (rbp,8))) (% ecx) *)
  0x89; 0x55; 0x0c;        (* MOV (Memop Doubleword (%% (rbp,12))) (% edx) *)
  0x4c; 0x8b; 0x3c; 0x24;  (* MOV (% r15) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x08;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x10;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x83; 0xc4; 0x28;  (* ADD (% rsp) (Imm8 (word 40)) *)
  0xc3                     (* RET *)
];;

let md5_block_asm_data_order_tmc = define_trimmed "md5_block_asm_data_order_tmc" md5_block_asm_data_order_mc;;

let MD5_BLOCK_ASM_DATA_ORDER_EXEC = X86_MK_CORE_EXEC_RULE md5_block_asm_data_order_tmc;;

(* ------------------------------------------------------------------------- *)
(* LEA truncation helper.                                                    *)
(*                                                                           *)
(* The aws-lc asm uses LEA with a sign-extended 32-bit displacement to add   *)
(* the round constant T[i] to the running accumulator. After the simulator   *)
(* applies WORD_SX_ZX to peel the sign-extension, the surviving form is      *)
(*   word_zx (word_add (word_zx a:int64)                                     *)
(*                     (word (1 * val (word_zx w:int64) + n))) :int32        *)
(* where n is the int64-encoded immediate (= T[i] for positive immediates,   *)
(* or 2^64 - |T[i]_signed| for negative ones). This collapses to the natural *)
(* 32-bit sum word_add a (word_add w (word n:int32)) because the int32       *)
(* truncation absorbs the high 32 bits of n.                                 *)
(*                                                                           *)
(* This generic shape recurs once per round-1..4 step (and hence 64 times in *)
(* the full block). Proven once, used everywhere via REWRITE_TAC.            *)
(* ------------------------------------------------------------------------- *)

let LEA_TRUNC_LEMMA = prove
 (`!(a:int32) (w:int32) (n:num).
       word_zx ((word_add (word_zx a:int64)
                          (word (1 * val (word_zx w:int64) + n):int64)):int64) :int32
       = word_add a (word_add w (word n:int32))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
              DIMINDEX_32; DIMINDEX_64; ARITH_RULE `1 * x = x`] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 32 = 32`]);;

(* ------------------------------------------------------------------------- *)
(* Phase 4: correctness of the first round-1 step (instructions at           *)
(* offset 52..89 in the trimmed code), computing                             *)
(*   new_a = b + ROL_7(a + F(b,c,d) + W[0] + T[0]).                          *)
(*                                                                           *)
(* Cut-point convention (locked for Phases 5..8): each round-step k's PC     *)
(* range is [pc + step_k_start, pc + step_(k+1)_start), i.e. the step ends   *)
(* one byte before the next step's first instruction begins. For step 0 the  *)
(* range is [pc+52, pc+90); subsequent steps cover 9 instructions each.      *)
(* This convention composes cleanly under ENSURES_SEQUENCE_TAC.              *)
(* ------------------------------------------------------------------------- *)

let MD5_1STEP_CORRECT = prove
 (`!pc data_ptr a b c d w0:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 52) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read (memory :> bytes32 data_ptr) s = w0)
              (\s. read RIP s = word(pc + 90) /\
                   read RAX s =
                     word_zx (word_add b (word_rol (word_add (word_add a (md5_F b c d))
                                                             (word_add w0 (EL 0 md5_T)))
                                                   7)) /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor d c) (b:int32)) d =
    word_xor (word_and b (word_xor c d)) d`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Composition stepping-stone: round-1 steps 0+1 over [pc+52, pc+122).        *)
(* The end PC is step-1's first byte of step 2 (i.e. the cut-point convention *)
(* extends: step k spans [pc + step_k_start, pc + step_(k+1)_start)).         *)
(*                                                                           *)
(* Computes:                                                                 *)
(*   new_a = b + ROL_7(a + md5_F b c d + W[0] + T[0])                        *)
(*   new_d = new_a + ROL_12(d + md5_F new_a b c + W[1] + T[1])               *)
(* RBX/RCX unchanged.                                                        *)
(* ------------------------------------------------------------------------- *)

let MD5_2STEP_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 52) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s =
                     w1)
              (\s. read RIP s = word(pc + 122) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_F b c d))
                                                  (word_add w0 (EL 0 md5_T)))
                                        7)) /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s =
                     word_zx
                       (let new_a =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w0 (EL 0 md5_T)))
                                       7) in
                        word_add new_a
                         (word_rol (word_add (word_add d (md5_F new_a b c))
                                             (word_add w1 (EL 1 md5_T)))
                                   12)))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w0 (word 3614090360))) Fxor =
      word_add (word_add a Fxor) (word_add w0 (word 3614090360))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w0 (word 3614090360))) 7` THEN
    SUBGOAL_THEN `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w1 (word 3905402710))) Xform =
      word_add (word_add d Xform) (word_add w1 (word 3905402710))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Phase 5: full round-1 correctness over [pc+52, pc+569).                    *)
(*                                                                           *)
(* After 146 instructions of round-1 (steps 0..15, F round) the four         *)
(* registers hold the entries of (md5_compress 16 W [a;b;c;d]):              *)
(*   RAX = EL 0 (md5_compress 16 W [a;b;c;d]) = n_12                          *)
(*   RBX = EL 1 (md5_compress 16 W [a;b;c;d]) = n_15                          *)
(*   RCX = EL 2 (md5_compress 16 W [a;b;c;d]) = n_14                          *)
(*   RDX = EL 3 (md5_compress 16 W [a;b;c;d]) = n_13                          *)
(* where n_k = step k's freshly-computed value; the asm cycles writes among  *)
(* RAX (steps 0,4,8,12), RDX (1,5,9,13), RCX (2,6,10,14), RBX (3,7,11,15).   *)
(* ------------------------------------------------------------------------- *)

(* Linear unfold: md5_compress 16 W [a;b;c;d] as a 16-deep nest of           *)
(* md5_compress_round applications, no LET expansion (term size linear).     *)
let MD5_COMPRESS_16_LINEAR_UNFOLD = prove
 (`!(W:int32 list) (a:int32) b c d.
       md5_compress 16 W [a;b;c;d] =
       md5_compress_round 15 W
        (md5_compress_round 14 W
         (md5_compress_round 13 W
          (md5_compress_round 12 W
           (md5_compress_round 11 W
            (md5_compress_round 10 W
             (md5_compress_round 9 W
              (md5_compress_round 8 W
               (md5_compress_round 7 W
                (md5_compress_round 6 W
                 (md5_compress_round 5 W
                  (md5_compress_round 4 W
                   (md5_compress_round 3 W
                    (md5_compress_round 2 W
                     (md5_compress_round 1 W
                      (md5_compress_round 0 W [a;b;c;d])))))))))))))))`,
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  REFL_TAC);;

(* Single round-step reduction on a concrete 4-element list. Rewrites       *)
(* `md5_compress_round k W [a;b;c;d]` to its 4-list cycling form, parametric *)
(* in k (so `md5_K`/`md5_S`/`md5_round_function` ifs are not unfolded).      *)
let MD5_COMPRESS_ROUND_4LIST = prove
 (`!(W:int32 list) (k:num) (a:int32) b c d.
       md5_compress_round k W [a;b;c;d] =
       [d;
        word_add b
          (word_rol
             (word_add a
                (word_add (md5_round_function k b c d)
                   (word_add (EL (md5_K k) W) (EL k md5_T))))
             (md5_S k));
        b; c]`,
  REWRITE_TAC[md5_compress_round; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REPEAT GEN_TAC THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Spec-form sanity check (Phase 5 — gates the per-quarter spec conversion). *)
(*                                                                           *)
(* Validates that md5_compress 4 W [a;b;c;d] reduces to a clean 4-list of    *)
(* the per-step results na0/nd1/nc2/nb3 in the order [na0; nb3; nc2; nd1].    *)
(* The list ordering reflects the [d; new_a; b; c] cycling of                *)
(* md5_compress_round: after 4 rounds, EL 0 = na0 (step 0), EL 1 = nb3       *)
(* (step 3), EL 2 = nc2 (step 2), EL 3 = nd1 (step 1). This matches the      *)
(* asm's writeback assignment RAX/RBX/RCX/RDX = step 0/3/2/1 respectively.   *)
(*                                                                           *)
(* Strategy: linear unfold md5_compress 4 to a 4-deep nest of                *)
(* md5_compress_round, then per-round MD5_COMPRESS_ROUND_4LIST + numerical   *)
(* reduction of md5_round_function/md5_K/md5_S, normalize the inner add via  *)
(* WORD_RULE, and fold the per-step nai with UNDISCH_THEN. Bottom-up         *)
(* per-round reduction keeps term size linear; a one-shot LET_DEF unfold     *)
(* on the goal's RHS would blow up exponentially.                            *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_4_F_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d w0 w1 w2 w3 na0 nd1 nc2 nb3.
        LENGTH W = 16 /\
        w0 = EL 0 W /\ w1 = EL 1 W /\ w2 = EL 2 W /\ w3 = EL 3 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T)))
                         7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T)))
                         12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T)))
                         17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T)))
                         22)
        ==> md5_compress 4 W [a;b;c;d] = [na0; nb3; nc2; nd1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  (* Round 0 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (a:int32)
             (word_add (md5_F b c d) (word_add (EL 0 W) (EL 0 md5_T))) =
    word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na0:int32 =
    word_add b
     (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 1 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (d:int32)
             (word_add (md5_F na0 b c) (word_add (EL 1 W) (EL 1 md5_T))) =
    word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd1:int32 =
    word_add na0
     (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 2 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (c:int32)
             (word_add (md5_F nd1 na0 b) (word_add (EL 2 W) (EL 2 md5_T))) =
    word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc2:int32 =
    word_add nd1
     (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 3 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (b:int32)
             (word_add (md5_F nc2 nd1 na0) (word_add (EL 3 W) (EL 3 md5_T))) =
    word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb3:int32 =
    word_add nc2
     (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* MD5_QUARTER1_CORRECT: round-1 quarter-1 (steps 0..3, 38 instructions).    *)
(*                                                                           *)
(* Direct 38-step symbolic execution from pc+52 to pc+186. Subsumes the      *)
(* per-step lemmas MD5_1STEP_CORRECT_STRONG / MD5_R1_STEP{1,2,3}_CORRECT     *)
(* that were intermediate stepping stones during Phase 5 development; those  *)
(* per-step lemmas are deleted (recoverable from git history) since they    *)
(* are no longer used downstream.                                            *)
(*                                                                           *)
(* The four register-result conjuncts (RAX, RDX, RCX, RBX) are closed by    *)
(* extending the MD5_2STEP_CORRECT proof template with successive ABBREV    *)
(* layers: na0 = step-0 result, nd1 = step-1 result, nc2 = step-2 result.   *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER1_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w2 w3 w4:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 52) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s =
                     w1 /\
                   read (memory :> bytes32 (word_add data_ptr (word 8))) s =
                     w2 /\
                   read (memory :> bytes32 (word_add data_ptr (word 12))) s =
                     w3 /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s =
                     w4)
              (\s. read RIP s = word(pc + 186) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_F b c d))
                                                  (word_add w0 (EL 0 md5_T)))
                                        7)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w0 (EL 0 md5_T)))
                                       7) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_F na0 b c))
                                             (word_add w1 (EL 1 md5_T)))
                                   12)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w0 (EL 0 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w1 (EL 1 md5_T)))
                                       12) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                             (word_add w2 (EL 2 md5_T)))
                                   17)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w0 (EL 0 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w1 (EL 1 md5_T)))
                                       12) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                 (word_add w2 (EL 2 md5_T)))
                                       17) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                             (word_add w3 (EL 3 md5_T)))
                                   22)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w4 /\
                   read R11 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-0 result *)
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-1 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w0 (word 3614090360))) Fxor =
      word_add (word_add a Fxor) (word_add w0 (word 3614090360))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w0 (word 3614090360))) 7` THEN
    SUBGOAL_THEN `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w1 (word 3905402710))) Xform =
      word_add (word_add d Xform) (word_add w1 (word 3905402710))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-2 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w0 (word 3614090360))) Fxor =
      word_add (word_add a Fxor) (word_add w0 (word 3614090360))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w0 (word 3614090360))) 7` THEN
    SUBGOAL_THEN
     `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (b:int32) (word_add b Rrol7) = word_xor (word_add b Rrol7) b`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w1 (word 3905402710))) Xform =
      word_add (word_add d Xform) (word_add w1 (word 3905402710))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol12:int32 = word_rol
                      (word_add (word_add (d:int32) Xform)
                                (word_add w1 (word 3905402710))) 12` THEN
    ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
    SUBGOAL_THEN
     `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_xor (na0:int32) b) (word_add na0 Rrol12) =
      word_and (word_add na0 Rrol12) (word_xor na0 b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                       (word_xor na0 b)) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w2 (word 606105819))) Yform =
      word_add (word_add c Yform) (word_add w2 (word 606105819))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol17:int32 = word_rol
                      (word_add (word_add (c:int32) Yform)
                                (word_add w2 (word 606105819))) 17` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-3 result *)
  REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor d c) (b:int32)) d =
    word_xor (word_and b (word_xor c d)) d`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
  ABBREV_TAC
   `Rrol7:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w0 (word 3614090360)))
                             Fxor) 7` THEN
  SUBGOAL_THEN
   `word_add (Rrol7:int32) b = word_add b Rrol7`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                     (word_xor b c)) c` THEN
  ABBREV_TAC
   `Rrol12:int32 = word_rol
                    (word_add (word_add (d:int32) (word_add w1 (word 3905402710)))
                              Xform) 12` THEN
  ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
  SUBGOAL_THEN
   `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor b (na0:int32)) u =
              word_and u (word_xor na0 b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                     (word_xor na0 b)) b` THEN
  ABBREV_TAC
   `Rrol17:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w2 (word 606105819)))
                              Yform) 17` THEN
  ABBREV_TAC `nd1:int32 = word_add (na0:int32) Rrol12` THEN
  SUBGOAL_THEN
   `word_add Rrol17 (nd1:int32) = word_add nd1 Rrol17`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `nc2:int32 = word_add (nd1:int32) Rrol17` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) Fxor) (word_add w0 (word 3614090360)) =
    word_add (word_add a (word_add w0 (word 3614090360))) Fxor`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) Xform) (word_add w1 (word 3905402710)) =
    word_add (word_add d (word_add w1 (word 3905402710))) Xform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) Yform) (word_add w2 (word 606105819)) =
    word_add (word_add c (word_add w2 (word 606105819))) Yform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor (na0:int32) nd1) nc2) na0 =
    word_xor (word_and nc2 (word_xor nd1 na0)) na0`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w3 (word 3250441966)))
             (word_xor (word_and nc2 (word_xor nd1 na0)) na0) =
    word_add (word_add b (word_xor (word_and nc2 (word_xor nd1 na0)) na0))
             (word_add w3 (word 3250441966))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* MD5_QUARTER2_CORRECT: round-1 quarter-2 (steps 4..7, 36 instructions).    *)
(*                                                                           *)
(* Direct 36-step symbolic execution from pc+186 to pc+314. Mirrors Q1's    *)
(* template, with inputs (a,b,c,d) standing for the post-Q1 register layout *)
(* (i.e. the renamed na0/nb3/nc2/nd1), message words w4..w7, T[4..7], and   *)
(* the same per-step rotations [7;12;17;22] (still in round 1, F function). *)
(*                                                                           *)
(* Pre-state pins R11 = word_zx (word_zx d) — the asm at line 115 of      *)
(* md5_block_asm_data_order.S (`movl %edx,%r11d`) leaves R11 holding the   *)
(* int32-zx of EDX = d (Q2's d is what was nd1 in Q1). Q2 step 4's first   *)
(* instruction (`xorl %ecx,%r11d`) reads R11 to start the F-machinery.     *)
(* Q1's post exports `read R11 s = read RDX s`, which under composition    *)
(* d := nd1 reduces to `word_zx (word_zx d):int64` modulo WORD_ZX_TRIVIAL. *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER2_CORRECT = prove
 (`!pc data_ptr a b c d w4 w5 w6 w7 w8:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 186) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w4 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 20))) s =
                     w5 /\
                   read (memory :> bytes32 (word_add data_ptr (word 24))) s =
                     w6 /\
                   read (memory :> bytes32 (word_add data_ptr (word 28))) s =
                     w7 /\
                   read (memory :> bytes32 (word_add data_ptr (word 32))) s =
                     w8)
              (\s. read RIP s = word(pc + 314) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_F b c d))
                                                  (word_add w4 (EL 4 md5_T)))
                                        7)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w4 (EL 4 md5_T)))
                                       7) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_F na0 b c))
                                             (word_add w5 (EL 5 md5_T)))
                                   12)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w4 (EL 4 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w5 (EL 5 md5_T)))
                                       12) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                             (word_add w6 (EL 6 md5_T)))
                                   17)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w4 (EL 4 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w5 (EL 5 md5_T)))
                                       12) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                 (word_add w6 (EL 6 md5_T)))
                                       17) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                             (word_add w7 (EL 7 md5_T)))
                                   22)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w8 /\
                   read R11 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-4 result *)
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-5 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w4 (word 4118548399))) Fxor =
      word_add (word_add a Fxor) (word_add w4 (word 4118548399))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w4 (word 4118548399))) 7` THEN
    SUBGOAL_THEN `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w5 (word 1200080426))) Xform =
      word_add (word_add d Xform) (word_add w5 (word 1200080426))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-6 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w4 (word 4118548399))) Fxor =
      word_add (word_add a Fxor) (word_add w4 (word 4118548399))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w4 (word 4118548399))) 7` THEN
    SUBGOAL_THEN
     `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (b:int32) (word_add b Rrol7) = word_xor (word_add b Rrol7) b`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w5 (word 1200080426))) Xform =
      word_add (word_add d Xform) (word_add w5 (word 1200080426))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol12:int32 = word_rol
                      (word_add (word_add (d:int32) Xform)
                                (word_add w5 (word 1200080426))) 12` THEN
    ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
    SUBGOAL_THEN
     `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_xor (na0:int32) b) (word_add na0 Rrol12) =
      word_and (word_add na0 Rrol12) (word_xor na0 b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                       (word_xor na0 b)) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w6 (word 2821735955))) Yform =
      word_add (word_add c Yform) (word_add w6 (word 2821735955))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol17:int32 = word_rol
                      (word_add (word_add (c:int32) Yform)
                                (word_add w6 (word 2821735955))) 17` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-7 result *)
  REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor d c) (b:int32)) d =
    word_xor (word_and b (word_xor c d)) d`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
  ABBREV_TAC
   `Rrol7:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w4 (word 4118548399)))
                             Fxor) 7` THEN
  SUBGOAL_THEN
   `word_add (Rrol7:int32) b = word_add b Rrol7`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                     (word_xor b c)) c` THEN
  ABBREV_TAC
   `Rrol12:int32 = word_rol
                    (word_add (word_add (d:int32) (word_add w5 (word 1200080426)))
                              Xform) 12` THEN
  ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
  SUBGOAL_THEN
   `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor b (na0:int32)) u =
              word_and u (word_xor na0 b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                     (word_xor na0 b)) b` THEN
  ABBREV_TAC
   `Rrol17:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w6 (word 2821735955)))
                              Yform) 17` THEN
  ABBREV_TAC `nd1:int32 = word_add (na0:int32) Rrol12` THEN
  SUBGOAL_THEN
   `word_add Rrol17 (nd1:int32) = word_add nd1 Rrol17`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `nc2:int32 = word_add (nd1:int32) Rrol17` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) Fxor) (word_add w4 (word 4118548399)) =
    word_add (word_add a (word_add w4 (word 4118548399))) Fxor`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) Xform) (word_add w5 (word 1200080426)) =
    word_add (word_add d (word_add w5 (word 1200080426))) Xform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) Yform) (word_add w6 (word 2821735955)) =
    word_add (word_add c (word_add w6 (word 2821735955))) Yform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor (na0:int32) nd1) nc2) na0 =
    word_xor (word_and nc2 (word_xor nd1 na0)) na0`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w7 (word 4249261313)))
             (word_xor (word_and nc2 (word_xor nd1 na0)) na0) =
    word_add (word_add b (word_xor (word_and nc2 (word_xor nd1 na0)) na0))
             (word_add w7 (word 4249261313))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* MD5_QUARTER3_CORRECT: round-1 quarter-3 (steps 8..11, 36 instructions).   *)
(*                                                                           *)
(* Direct 36-step symbolic execution from pc+314 to pc+442. Mirrors Q2's    *)
(* template exactly, with inputs (a,b,c,d) standing for the post-Q2 register *)
(* layout, message words w8..w11, T[8..11], same per-step rotations.         *)
(*                                                                           *)
(* Pre-state pins R11 = word_zx (word_zx d) — same R11 carry pattern as Q2. *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER3_CORRECT = prove
 (`!pc data_ptr a b c d w8 w9 w10 w11 w12:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 314) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w8 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 36))) s =
                     w9 /\
                   read (memory :> bytes32 (word_add data_ptr (word 40))) s =
                     w10 /\
                   read (memory :> bytes32 (word_add data_ptr (word 44))) s =
                     w11 /\
                   read (memory :> bytes32 (word_add data_ptr (word 48))) s =
                     w12)
              (\s. read RIP s = word(pc + 442) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_F b c d))
                                                  (word_add w8 (EL 8 md5_T)))
                                        7)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w8 (EL 8 md5_T)))
                                       7) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_F na0 b c))
                                             (word_add w9 (EL 9 md5_T)))
                                   12)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w8 (EL 8 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w9 (EL 9 md5_T)))
                                       12) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                             (word_add w10 (EL 10 md5_T)))
                                   17)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w8 (EL 8 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w9 (EL 9 md5_T)))
                                       12) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                 (word_add w10 (EL 10 md5_T)))
                                       17) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                             (word_add w11 (EL 11 md5_T)))
                                   22)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w12 /\
                   read R11 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-8 result *)
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-9 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w8 (word 1770035416))) Fxor =
      word_add (word_add a Fxor) (word_add w8 (word 1770035416))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w8 (word 1770035416))) 7` THEN
    SUBGOAL_THEN `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w9 (word 2336552879))) Xform =
      word_add (word_add d Xform) (word_add w9 (word 2336552879))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-10 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w8 (word 1770035416))) Fxor =
      word_add (word_add a Fxor) (word_add w8 (word 1770035416))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w8 (word 1770035416))) 7` THEN
    SUBGOAL_THEN
     `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (b:int32) (word_add b Rrol7) = word_xor (word_add b Rrol7) b`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w9 (word 2336552879))) Xform =
      word_add (word_add d Xform) (word_add w9 (word 2336552879))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol12:int32 = word_rol
                      (word_add (word_add (d:int32) Xform)
                                (word_add w9 (word 2336552879))) 12` THEN
    ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
    SUBGOAL_THEN
     `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_xor (na0:int32) b) (word_add na0 Rrol12) =
      word_and (word_add na0 Rrol12) (word_xor na0 b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                       (word_xor na0 b)) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w10 (word 4294925233))) Yform =
      word_add (word_add c Yform) (word_add w10 (word 4294925233))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol17:int32 = word_rol
                      (word_add (word_add (c:int32) Yform)
                                (word_add w10 (word 4294925233))) 17` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-11 result *)
  REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor d c) (b:int32)) d =
    word_xor (word_and b (word_xor c d)) d`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
  ABBREV_TAC
   `Rrol7:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w8 (word 1770035416)))
                             Fxor) 7` THEN
  SUBGOAL_THEN
   `word_add (Rrol7:int32) b = word_add b Rrol7`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                     (word_xor b c)) c` THEN
  ABBREV_TAC
   `Rrol12:int32 = word_rol
                    (word_add (word_add (d:int32) (word_add w9 (word 2336552879)))
                              Xform) 12` THEN
  ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
  SUBGOAL_THEN
   `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor b (na0:int32)) u =
              word_and u (word_xor na0 b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                     (word_xor na0 b)) b` THEN
  ABBREV_TAC
   `Rrol17:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w10 (word 4294925233)))
                              Yform) 17` THEN
  ABBREV_TAC `nd1:int32 = word_add (na0:int32) Rrol12` THEN
  SUBGOAL_THEN
   `word_add Rrol17 (nd1:int32) = word_add nd1 Rrol17`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `nc2:int32 = word_add (nd1:int32) Rrol17` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) Fxor) (word_add w8 (word 1770035416)) =
    word_add (word_add a (word_add w8 (word 1770035416))) Fxor`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) Xform) (word_add w9 (word 2336552879)) =
    word_add (word_add d (word_add w9 (word 2336552879))) Xform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) Yform) (word_add w10 (word 4294925233)) =
    word_add (word_add c (word_add w10 (word 4294925233))) Yform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor (na0:int32) nd1) nc2) na0 =
    word_xor (word_and nc2 (word_xor nd1 na0)) na0`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w11 (word 2304563134)))
             (word_xor (word_and nc2 (word_xor nd1 na0)) na0) =
    word_add (word_add b (word_xor (word_and nc2 (word_xor nd1 na0)) na0))
             (word_add w11 (word 2304563134))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* MD5_QUARTER4_CORRECT: round-1 quarter-4 (steps 12..15, 36 instructions).  *)
(*                                                                           *)
(* Direct 36-step symbolic execution from pc+442 to pc+569. Mirrors Q2/Q3's *)
(* template. Inputs (a,b,c,d) are post-Q3 register values, message words   *)
(* w12..w15, T[12..15], same per-step rotations [7;12;17;22] (still F).     *)
(*                                                                           *)
(* Pre-state pins R11 = word_zx (word_zx d) — same R11 carry pattern as Q2. *)
(* The asm's last `mov (%rsi),%r10d` (objdump 0x22f) reloads R10 with w0    *)
(* (offset 0) — a dead load, immediately overwritten by round-2 step 16.    *)
(* Q4 post exports `R10 = word_zx w0` (consequence) and `R11 = read RDX s`  *)
(* for downstream composition with round-2 setup.                           *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER4_CORRECT = prove
 (`!pc data_ptr a b c d w0 w12 w13 w14 w15:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 442) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w12 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 52))) s =
                     w13 /\
                   read (memory :> bytes32 (word_add data_ptr (word 56))) s =
                     w14 /\
                   read (memory :> bytes32 (word_add data_ptr (word 60))) s =
                     w15)
              (\s. read RIP s = word(pc + 569) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_F b c d))
                                                  (word_add w12 (EL 12 md5_T)))
                                        7)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w12 (EL 12 md5_T)))
                                       7) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_F na0 b c))
                                             (word_add w13 (EL 13 md5_T)))
                                   12)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w12 (EL 12 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w13 (EL 13 md5_T)))
                                       12) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                             (word_add w14 (EL 14 md5_T)))
                                   17)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_F b c d))
                                                 (word_add w12 (EL 12 md5_T)))
                                       7) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_F na0 b c))
                                                 (word_add w13 (EL 13 md5_T)))
                                       12) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                 (word_add w14 (EL 14 md5_T)))
                                       17) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                             (word_add w15 (EL 15 md5_T)))
                                   22)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w0 /\
                   read R11 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-12 result *)
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-13 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w12 (word 1804603682))) Fxor =
      word_add (word_add a Fxor) (word_add w12 (word 1804603682))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w12 (word 1804603682))) 7` THEN
    SUBGOAL_THEN `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w13 (word 4254626195))) Xform =
      word_add (word_add d Xform) (word_add w13 (word 4254626195))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-14 result *)
    REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_and (word_xor d c) (b:int32)) d =
      word_xor (word_and b (word_xor c d)) d`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w12 (word 1804603682))) Fxor =
      word_add (word_add a Fxor) (word_add w12 (word 1804603682))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol7:int32 = word_rol
                     (word_add (word_add (a:int32) Fxor)
                               (word_add w12 (word 1804603682))) 7` THEN
    SUBGOAL_THEN
     `word_add (Rrol7:int32) b = word_add b Rrol7`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (b:int32) (word_add b Rrol7) = word_xor (word_add b Rrol7) b`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                       (word_xor b c)) c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w13 (word 4254626195))) Xform =
      word_add (word_add d Xform) (word_add w13 (word 4254626195))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol12:int32 = word_rol
                      (word_add (word_add (d:int32) Xform)
                                (word_add w13 (word 4254626195))) 12` THEN
    ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
    SUBGOAL_THEN
     `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_xor (na0:int32) b) (word_add na0 Rrol12) =
      word_and (word_add na0 Rrol12) (word_xor na0 b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                       (word_xor na0 b)) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w14 (word 2792965006))) Yform =
      word_add (word_add c Yform) (word_add w14 (word 2792965006))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Rrol17:int32 = word_rol
                      (word_add (word_add (c:int32) Yform)
                                (word_add w14 (word 2792965006))) 17` THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-15 result *)
  REWRITE_TAC[GSYM MD5_F_XOR_AND_FORM] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor d c) (b:int32)) d =
    word_xor (word_and b (word_xor c d)) d`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Fxor:int32 = word_xor (word_and (b:int32) (word_xor c d)) d` THEN
  ABBREV_TAC
   `Rrol7:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w12 (word 1804603682)))
                             Fxor) 7` THEN
  SUBGOAL_THEN
   `word_add (Rrol7:int32) b = word_add b Rrol7`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor c b) u = word_and u (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Xform:int32 = word_xor (word_and (word_add (b:int32) Rrol7)
                                     (word_xor b c)) c` THEN
  ABBREV_TAC
   `Rrol12:int32 = word_rol
                    (word_add (word_add (d:int32) (word_add w13 (word 4254626195)))
                              Xform) 12` THEN
  ABBREV_TAC `na0:int32 = word_add (b:int32) Rrol7` THEN
  SUBGOAL_THEN
   `word_add Rrol12 (na0:int32) = word_add na0 Rrol12`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:int32. word_and (word_xor b (na0:int32)) u =
              word_and u (word_xor na0 b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Yform:int32 = word_xor (word_and (word_add (na0:int32) Rrol12)
                                     (word_xor na0 b)) b` THEN
  ABBREV_TAC
   `Rrol17:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w14 (word 2792965006)))
                              Yform) 17` THEN
  ABBREV_TAC `nd1:int32 = word_add (na0:int32) Rrol12` THEN
  SUBGOAL_THEN
   `word_add Rrol17 (nd1:int32) = word_add nd1 Rrol17`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `nc2:int32 = word_add (nd1:int32) Rrol17` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) Fxor) (word_add w12 (word 1804603682)) =
    word_add (word_add a (word_add w12 (word 1804603682))) Fxor`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) Xform) (word_add w13 (word 4254626195)) =
    word_add (word_add d (word_add w13 (word 4254626195))) Xform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) Yform) (word_add w14 (word 2792965006)) =
    word_add (word_add c (word_add w14 (word 2792965006))) Yform`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor (na0:int32) nd1) nc2) na0 =
    word_xor (word_and nc2 (word_xor nd1 na0)) na0`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w15 (word 1236535329)))
             (word_xor (word_and nc2 (word_xor nd1 na0)) na0) =
    word_add (word_add b (word_xor (word_and nc2 (word_xor nd1 na0)) na0))
             (word_add w15 (word 1236535329))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Round 2 quarter 5: steps 16..19 (G-round, first quarter).                  *)
(*                                                                           *)
(* Pre at pc+569 (Q4 post), a/b/c/d in RAX/RBX/RCX/RDX, R10 holds w0 (the    *)
(* dead reload from Q4's tail), R11 = word_zx (word_zx d).                   *)
(*                                                                           *)
(* Step 16 reads w1 (offset 4), step 17 reads w6 (offset 24), step 18 reads  *)
(* w11 (offset 44), step 19 reads w0 (offset 0). Round 2's K(i) = 5i+1 mod   *)
(* 16 yields message indices [1;6;11;0]. Rotation amounts [5;9;14;20].       *)
(* T constants 0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa.               *)
(*                                                                           *)
(* The asm encodes G(b,c,d) using the disjoint-AND identity                  *)
(*   (b AND d) + (c AND NOT d) = md5_G b c d                                 *)
(* via MD5_G_DISJOINT_ADD; round 2 also clobbers R12 (used as a temporary    *)
(* between LEAL and ADDL/ROLL), so MAYCHANGE must include R12.               *)
(*                                                                           *)
(* Post at pc+730 (last instruction of step 19's roll/add). Tail dead load   *)
(* at line 265 reloads R10 with w5 for step 20.                              *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER5_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w5 w6 w11:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 569) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w0 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s =
                     w1 /\
                   read (memory :> bytes32 (word_add data_ptr (word 20))) s =
                     w5 /\
                   read (memory :> bytes32 (word_add data_ptr (word 24))) s =
                     w6 /\
                   read (memory :> bytes32 (word_add data_ptr (word 44))) s =
                     w11)
              (\s. read RIP s = word(pc + 730) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_G b c d))
                                                  (word_add w1 (EL 16 md5_T)))
                                        5)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w1 (EL 16 md5_T)))
                                       5) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_G na0 b c))
                                             (word_add w6 (EL 17 md5_T)))
                                   9)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w1 (EL 16 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w6 (EL 17 md5_T)))
                                       9) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                             (word_add w11 (EL 18 md5_T)))
                                   14)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w1 (EL 16 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w6 (EL 17 md5_T)))
                                       9) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                                 (word_add w11 (EL 18 md5_T)))
                                       14) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_G nc2 nd1 na0))
                                             (word_add w0 (EL 19 md5_T)))
                                   20)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w5 /\
                   read R11 s = read RDX s /\
                   read R12 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11; R12] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--47) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-16 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-17 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w1 (word 4129170786)) =
      word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w6 (word 3225465664)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w6 (word 3225465664)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep17:int32 = md5_G (word_add (b:int32) Grol5) b c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w6 (word 3225465664))) Gstep17 =
      word_add (word_add d Gstep17) (word_add w6 (word 3225465664))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-18 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w1 (word 4129170786)) =
      word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
      word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [CONV_TAC WORD_BITWISE_RULE;
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w6 (word 3225465664)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w6 (word 3225465664)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol9:int32 = word_rol
                     (word_add (word_add (d:int32) (word_add w6 (word 3225465664)))
                               (md5_G (word_add b Grol5) b c)) 9` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
               (word_add w6 (word 3225465664)) =
      word_add (word_add d (word_add w6 (word 3225465664)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not b) (word_add Grol5 (b:int32)) =
      word_and (word_add b Grol5) (word_not b) /\
      word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
      word_and (word_add (word_add b Grol5) Grol9) b`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE;
        SUBGOAL_THEN
         `word_add Grol9 (word_add Grol5 (b:int32)) =
          word_add (word_add b Grol5) Grol9`
         SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (c:int32) (word_add w11 (word 643717713)))
                         (word_and (word_add b Grol5) (word_not b)))
               (word_and (word_add (word_add b Grol5) Grol9) b) =
      word_add (word_add c (word_add w11 (word 643717713)))
               (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep18:int32 = md5_G (word_add (word_add (b:int32) Grol5) Grol9)
                            (word_add b Grol5) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w11 (word 643717713))) Gstep18 =
      word_add (word_add c Gstep18) (word_add w11 (word 643717713))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-19 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                       (word_and (word_not d) c))
             (word_and d b) =
    word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol5:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w1 (word 4129170786)))
                             (md5_G b c d)) 5` THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) (md5_G b c d)) (word_add w1 (word 4129170786)) =
    word_add (word_add a (word_add w1 (word 4129170786))) (md5_G b c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
    word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [CONV_TAC WORD_BITWISE_RULE;
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (d:int32) (word_add w6 (word 3225465664)))
                       (word_and b (word_not c)))
             (word_and (word_add b Grol5) c) =
    word_add (word_add d (word_add w6 (word 3225465664)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol9:int32 = word_rol
                   (word_add (word_add (d:int32) (word_add w6 (word 3225465664)))
                             (md5_G (word_add b Grol5) b c)) 9` THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
             (word_add w6 (word 3225465664)) =
    word_add (word_add d (word_add w6 (word 3225465664)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not b) (word_add Grol5 (b:int32)) =
    word_and (word_add b Grol5) (word_not b) /\
    word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) b`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE;
      SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9`
       SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (c:int32) (word_add w11 (word 643717713)))
                       (word_and (word_add b Grol5) (word_not b)))
             (word_and (word_add (word_add b Grol5) Grol9) b) =
    word_add (word_add c (word_add w11 (word 643717713)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol14:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w11 (word 643717713)))
                              (md5_G (word_add (word_add b Grol5) Grol9)
                                     (word_add b Grol5) b)) 14` THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (md5_G (word_add (word_add b Grol5) Grol9)
                                        (word_add b Grol5) b))
             (word_add w11 (word 643717713)) =
    word_add (word_add c (word_add w11 (word 643717713)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not (word_add Grol5 (b:int32)))
             (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) (word_not (word_add b Grol5)) /\
    word_and (word_add Grol5 (b:int32))
             (word_add Grol14 (word_add Grol9 (word_add Grol5 b))) =
    word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
             (word_add b Grol5)`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE];
      SUBGOAL_THEN
       `word_add Grol14 (word_add Grol9 (word_add Grol5 (b:int32))) =
        word_add (word_add (word_add b Grol5) Grol9) Grol14 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (b:int32) (word_add w0 (word 3921069994)))
                       (word_and (word_add (word_add b Grol5) Grol9)
                                 (word_not (word_add b Grol5))))
             (word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                       (word_add b Grol5)) =
    word_add (word_add b (word_add w0 (word 3921069994)))
             (md5_G (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                    (word_add (word_add b Grol5) Grol9)
                    (word_add b Grol5))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Gstep19:int32 = md5_G (word_add (word_add (word_add (b:int32) Grol5) Grol9) Grol14)
                          (word_add (word_add b Grol5) Grol9)
                          (word_add b Grol5)` THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w0 (word 3921069994))) Gstep19 =
    word_add (word_add b Gstep19) (word_add w0 (word 3921069994))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let MD5_QUARTER6_CORRECT = prove
 (`!pc data_ptr a b c d w4 w5 w9 w10 w15:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 730) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w5 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read R12 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s =
                     w4 /\
                   read (memory :> bytes32 (word_add data_ptr (word 20))) s =
                     w5 /\
                   read (memory :> bytes32 (word_add data_ptr (word 36))) s =
                     w9 /\
                   read (memory :> bytes32 (word_add data_ptr (word 40))) s =
                     w10 /\
                   read (memory :> bytes32 (word_add data_ptr (word 60))) s =
                     w15)
              (\s. read RIP s = word(pc + 882) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_G b c d))
                                                  (word_add w5 (EL 20 md5_T)))
                                        5)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w5 (EL 20 md5_T)))
                                       5) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_G na0 b c))
                                             (word_add w10 (EL 21 md5_T)))
                                   9)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w5 (EL 20 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w10 (EL 21 md5_T)))
                                       9) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                             (word_add w15 (EL 22 md5_T)))
                                   14)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w5 (EL 20 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w10 (EL 21 md5_T)))
                                       9) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                                 (word_add w15 (EL 22 md5_T)))
                                       14) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_G nc2 nd1 na0))
                                             (word_add w4 (EL 23 md5_T)))
                                   20)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w9 /\
                   read R11 s = read RDX s /\
                   read R12 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11; R12] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-20 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-21 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w5 (word 3593408605)) =
      word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w10 (word 38016083)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w10 (word 38016083)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep21:int32 = md5_G (word_add (b:int32) Grol5) b c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w10 (word 38016083))) Gstep21 =
      word_add (word_add d Gstep21) (word_add w10 (word 38016083))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-22 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w5 (word 3593408605)) =
      word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
      word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [CONV_TAC WORD_BITWISE_RULE;
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w10 (word 38016083)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w10 (word 38016083)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol9:int32 = word_rol
                     (word_add (word_add (d:int32) (word_add w10 (word 38016083)))
                               (md5_G (word_add b Grol5) b c)) 9` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
               (word_add w10 (word 38016083)) =
      word_add (word_add d (word_add w10 (word 38016083)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not b) (word_add Grol5 (b:int32)) =
      word_and (word_add b Grol5) (word_not b) /\
      word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
      word_and (word_add (word_add b Grol5) Grol9) b`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE;
        SUBGOAL_THEN
         `word_add Grol9 (word_add Grol5 (b:int32)) =
          word_add (word_add b Grol5) Grol9`
         SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (c:int32) (word_add w15 (word 3634488961)))
                         (word_and (word_add b Grol5) (word_not b)))
               (word_and (word_add (word_add b Grol5) Grol9) b) =
      word_add (word_add c (word_add w15 (word 3634488961)))
               (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep22:int32 = md5_G (word_add (word_add (b:int32) Grol5) Grol9)
                            (word_add b Grol5) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w15 (word 3634488961))) Gstep22 =
      word_add (word_add c Gstep22) (word_add w15 (word 3634488961))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-23 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                       (word_and (word_not d) c))
             (word_and d b) =
    word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol5:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w5 (word 3593408605)))
                             (md5_G b c d)) 5` THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) (md5_G b c d)) (word_add w5 (word 3593408605)) =
    word_add (word_add a (word_add w5 (word 3593408605))) (md5_G b c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
    word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [CONV_TAC WORD_BITWISE_RULE;
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (d:int32) (word_add w10 (word 38016083)))
                       (word_and b (word_not c)))
             (word_and (word_add b Grol5) c) =
    word_add (word_add d (word_add w10 (word 38016083)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol9:int32 = word_rol
                   (word_add (word_add (d:int32) (word_add w10 (word 38016083)))
                             (md5_G (word_add b Grol5) b c)) 9` THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
             (word_add w10 (word 38016083)) =
    word_add (word_add d (word_add w10 (word 38016083)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not b) (word_add Grol5 (b:int32)) =
    word_and (word_add b Grol5) (word_not b) /\
    word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) b`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE;
      SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9`
       SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (c:int32) (word_add w15 (word 3634488961)))
                       (word_and (word_add b Grol5) (word_not b)))
             (word_and (word_add (word_add b Grol5) Grol9) b) =
    word_add (word_add c (word_add w15 (word 3634488961)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol14:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w15 (word 3634488961)))
                              (md5_G (word_add (word_add b Grol5) Grol9)
                                     (word_add b Grol5) b)) 14` THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (md5_G (word_add (word_add b Grol5) Grol9)
                                        (word_add b Grol5) b))
             (word_add w15 (word 3634488961)) =
    word_add (word_add c (word_add w15 (word 3634488961)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not (word_add Grol5 (b:int32)))
             (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) (word_not (word_add b Grol5)) /\
    word_and (word_add Grol5 (b:int32))
             (word_add Grol14 (word_add Grol9 (word_add Grol5 b))) =
    word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
             (word_add b Grol5)`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE];
      SUBGOAL_THEN
       `word_add Grol14 (word_add Grol9 (word_add Grol5 (b:int32))) =
        word_add (word_add (word_add b Grol5) Grol9) Grol14 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (b:int32) (word_add w4 (word 3889429448)))
                       (word_and (word_add (word_add b Grol5) Grol9)
                                 (word_not (word_add b Grol5))))
             (word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                       (word_add b Grol5)) =
    word_add (word_add b (word_add w4 (word 3889429448)))
             (md5_G (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                    (word_add (word_add b Grol5) Grol9)
                    (word_add b Grol5))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Gstep23:int32 = md5_G (word_add (word_add (word_add (b:int32) Grol5) Grol9) Grol14)
                          (word_add (word_add b Grol5) Grol9)
                          (word_add b Grol5)` THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w4 (word 3889429448))) Gstep23 =
    word_add (word_add b Gstep23) (word_add w4 (word 3889429448))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let MD5_QUARTER7_CORRECT = prove
 (`!pc data_ptr a b c d w3 w8 w9 w13 w14:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 882) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w9 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read R12 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 12))) s =
                     w3 /\
                   read (memory :> bytes32 (word_add data_ptr (word 32))) s =
                     w8 /\
                   read (memory :> bytes32 (word_add data_ptr (word 36))) s =
                     w9 /\
                   read (memory :> bytes32 (word_add data_ptr (word 52))) s =
                     w13 /\
                   read (memory :> bytes32 (word_add data_ptr (word 56))) s =
                     w14)
              (\s. read RIP s = word(pc + 1034) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_G b c d))
                                                  (word_add w9 (EL 24 md5_T)))
                                        5)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w9 (EL 24 md5_T)))
                                       5) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_G na0 b c))
                                             (word_add w14 (EL 25 md5_T)))
                                   9)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w9 (EL 24 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w14 (EL 25 md5_T)))
                                       9) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                             (word_add w3 (EL 26 md5_T)))
                                   14)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w9 (EL 24 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w14 (EL 25 md5_T)))
                                       9) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                                 (word_add w3 (EL 26 md5_T)))
                                       14) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_G nc2 nd1 na0))
                                             (word_add w8 (EL 27 md5_T)))
                                   20)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w13 /\
                   read R11 s = read RDX s /\
                   read R12 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11; R12] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-24 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-25 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w9 (word 568446438)) =
      word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w14 (word 3275163606)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w14 (word 3275163606)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep25:int32 = md5_G (word_add (b:int32) Grol5) b c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w14 (word 3275163606))) Gstep25 =
      word_add (word_add d Gstep25) (word_add w14 (word 3275163606))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-26 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w9 (word 568446438)) =
      word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
      word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [CONV_TAC WORD_BITWISE_RULE;
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w14 (word 3275163606)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w14 (word 3275163606)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol9:int32 = word_rol
                     (word_add (word_add (d:int32) (word_add w14 (word 3275163606)))
                               (md5_G (word_add b Grol5) b c)) 9` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
               (word_add w14 (word 3275163606)) =
      word_add (word_add d (word_add w14 (word 3275163606)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not b) (word_add Grol5 (b:int32)) =
      word_and (word_add b Grol5) (word_not b) /\
      word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
      word_and (word_add (word_add b Grol5) Grol9) b`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE;
        SUBGOAL_THEN
         `word_add Grol9 (word_add Grol5 (b:int32)) =
          word_add (word_add b Grol5) Grol9`
         SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (c:int32) (word_add w3 (word 4107603335)))
                         (word_and (word_add b Grol5) (word_not b)))
               (word_and (word_add (word_add b Grol5) Grol9) b) =
      word_add (word_add c (word_add w3 (word 4107603335)))
               (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep26:int32 = md5_G (word_add (word_add (b:int32) Grol5) Grol9)
                            (word_add b Grol5) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w3 (word 4107603335))) Gstep26 =
      word_add (word_add c Gstep26) (word_add w3 (word 4107603335))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-27 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                       (word_and (word_not d) c))
             (word_and d b) =
    word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol5:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w9 (word 568446438)))
                             (md5_G b c d)) 5` THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) (md5_G b c d)) (word_add w9 (word 568446438)) =
    word_add (word_add a (word_add w9 (word 568446438))) (md5_G b c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
    word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [CONV_TAC WORD_BITWISE_RULE;
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (d:int32) (word_add w14 (word 3275163606)))
                       (word_and b (word_not c)))
             (word_and (word_add b Grol5) c) =
    word_add (word_add d (word_add w14 (word 3275163606)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol9:int32 = word_rol
                   (word_add (word_add (d:int32) (word_add w14 (word 3275163606)))
                             (md5_G (word_add b Grol5) b c)) 9` THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
             (word_add w14 (word 3275163606)) =
    word_add (word_add d (word_add w14 (word 3275163606)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not b) (word_add Grol5 (b:int32)) =
    word_and (word_add b Grol5) (word_not b) /\
    word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) b`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE;
      SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9`
       SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (c:int32) (word_add w3 (word 4107603335)))
                       (word_and (word_add b Grol5) (word_not b)))
             (word_and (word_add (word_add b Grol5) Grol9) b) =
    word_add (word_add c (word_add w3 (word 4107603335)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol14:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w3 (word 4107603335)))
                              (md5_G (word_add (word_add b Grol5) Grol9)
                                     (word_add b Grol5) b)) 14` THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (md5_G (word_add (word_add b Grol5) Grol9)
                                        (word_add b Grol5) b))
             (word_add w3 (word 4107603335)) =
    word_add (word_add c (word_add w3 (word 4107603335)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not (word_add Grol5 (b:int32)))
             (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) (word_not (word_add b Grol5)) /\
    word_and (word_add Grol5 (b:int32))
             (word_add Grol14 (word_add Grol9 (word_add Grol5 b))) =
    word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
             (word_add b Grol5)`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE];
      SUBGOAL_THEN
       `word_add Grol14 (word_add Grol9 (word_add Grol5 (b:int32))) =
        word_add (word_add (word_add b Grol5) Grol9) Grol14 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (b:int32) (word_add w8 (word 1163531501)))
                       (word_and (word_add (word_add b Grol5) Grol9)
                                 (word_not (word_add b Grol5))))
             (word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                       (word_add b Grol5)) =
    word_add (word_add b (word_add w8 (word 1163531501)))
             (md5_G (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                    (word_add (word_add b Grol5) Grol9)
                    (word_add b Grol5))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Gstep27:int32 = md5_G (word_add (word_add (word_add (b:int32) Grol5) Grol9) Grol14)
                          (word_add (word_add b Grol5) Grol9)
                          (word_add b Grol5)` THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w8 (word 1163531501))) Gstep27 =
    word_add (word_add b Gstep27) (word_add w8 (word 1163531501))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let MD5_QUARTER8_CORRECT = prove
 (`!pc data_ptr a b c d w0 w2 w7 w12 w13:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1034) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w13 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read R12 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 8))) s =
                     w2 /\
                   read (memory :> bytes32 (word_add data_ptr (word 28))) s =
                     w7 /\
                   read (memory :> bytes32 (word_add data_ptr (word 48))) s =
                     w12 /\
                   read (memory :> bytes32 (word_add data_ptr (word 52))) s =
                     w13)
              (\s. read RIP s = word(pc + 1185) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_G b c d))
                                                  (word_add w13 (EL 28 md5_T)))
                                        5)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w13 (EL 28 md5_T)))
                                       5) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_G na0 b c))
                                             (word_add w2 (EL 29 md5_T)))
                                   9)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w13 (EL 28 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w2 (EL 29 md5_T)))
                                       9) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                             (word_add w7 (EL 30 md5_T)))
                                   14)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_G b c d))
                                                 (word_add w13 (EL 28 md5_T)))
                                       5) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_G na0 b c))
                                                 (word_add w2 (EL 29 md5_T)))
                                       9) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_G nd1 na0 b))
                                                 (word_add w7 (EL 30 md5_T)))
                                       14) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_G nc2 nd1 na0))
                                             (word_add w12 (EL 31 md5_T)))
                                   20)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w0 /\
                   read R11 s = read RDX s /\
                   read R12 s = read RDX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11; R12] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  CONJ_TAC THENL
   [(* RAX: step-28 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-29 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w13 (word 2850285829)) =
      word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c)`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w2 (word 4243563512)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w2 (word 4243563512)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep29:int32 = md5_G (word_add (b:int32) Grol5) b c` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w2 (word 4243563512))) Gstep29 =
      word_add (word_add d Gstep29) (word_add w2 (word 4243563512))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-30 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                         (word_and (word_not d) c))
               (word_and d b) =
      word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol5:int32 = word_rol
                     (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                               (md5_G b c d)) 5` THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (md5_G b c d)) (word_add w13 (word 2850285829)) =
      word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
      word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [CONV_TAC WORD_BITWISE_RULE;
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (d:int32) (word_add w2 (word 4243563512)))
                         (word_and b (word_not c)))
               (word_and (word_add b Grol5) c) =
      word_add (word_add d (word_add w2 (word 4243563512)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Grol9:int32 = word_rol
                     (word_add (word_add (d:int32) (word_add w2 (word 4243563512)))
                               (md5_G (word_add b Grol5) b c)) 9` THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
               (word_add w2 (word 4243563512)) =
      word_add (word_add d (word_add w2 (word 4243563512)))
               (md5_G (word_add b Grol5) b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `word_and (word_not b) (word_add Grol5 (b:int32)) =
      word_and (word_add b Grol5) (word_not b) /\
      word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
      word_and (word_add (word_add b Grol5) Grol9) b`
     (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
        CONV_TAC WORD_BITWISE_RULE;
        SUBGOAL_THEN
         `word_add Grol9 (word_add Grol5 (b:int32)) =
          word_add (word_add b Grol5) Grol9`
         SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add (c:int32) (word_add w7 (word 1735328473)))
                         (word_and (word_add b Grol5) (word_not b)))
               (word_and (word_add (word_add b Grol5) Grol9) b) =
      word_add (word_add c (word_add w7 (word 1735328473)))
               (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Gstep30:int32 = md5_G (word_add (word_add (b:int32) Grol5) Grol9)
                            (word_add b Grol5) b` THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w7 (word 1735328473))) Gstep30 =
      word_add (word_add c Gstep30) (word_add w7 (word 1735328473))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-31 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                       (word_and (word_not d) c))
             (word_and d b) =
    word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol5:int32 = word_rol
                   (word_add (word_add (a:int32) (word_add w13 (word 2850285829)))
                             (md5_G b c d)) 5` THEN
  SUBGOAL_THEN
   `word_add (word_add (a:int32) (md5_G b c d)) (word_add w13 (word 2850285829)) =
    word_add (word_add a (word_add w13 (word 2850285829))) (md5_G b c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not c) (b:int32) = word_and b (word_not c) /\
    word_and c (word_add Grol5 (b:int32)) = word_and (word_add b Grol5) c`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [CONV_TAC WORD_BITWISE_RULE;
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (d:int32) (word_add w2 (word 4243563512)))
                       (word_and b (word_not c)))
             (word_and (word_add b Grol5) c) =
    word_add (word_add d (word_add w2 (word 4243563512)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol9:int32 = word_rol
                   (word_add (word_add (d:int32) (word_add w2 (word 4243563512)))
                             (md5_G (word_add b Grol5) b c)) 9` THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (md5_G (word_add b Grol5) b c))
             (word_add w2 (word 4243563512)) =
    word_add (word_add d (word_add w2 (word 4243563512)))
             (md5_G (word_add b Grol5) b c)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not b) (word_add Grol5 (b:int32)) =
    word_and (word_add b Grol5) (word_not b) /\
    word_and (b:int32) (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) b`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_ADD_SYM] THEN
      CONV_TAC WORD_BITWISE_RULE;
      SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9`
       SUBST1_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (c:int32) (word_add w7 (word 1735328473)))
                       (word_and (word_add b Grol5) (word_not b)))
             (word_and (word_add (word_add b Grol5) Grol9) b) =
    word_add (word_add c (word_add w7 (word 1735328473)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Grol14:int32 = word_rol
                    (word_add (word_add (c:int32) (word_add w7 (word 1735328473)))
                              (md5_G (word_add (word_add b Grol5) Grol9)
                                     (word_add b Grol5) b)) 14` THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (md5_G (word_add (word_add b Grol5) Grol9)
                                        (word_add b Grol5) b))
             (word_add w7 (word 1735328473)) =
    word_add (word_add c (word_add w7 (word 1735328473)))
             (md5_G (word_add (word_add b Grol5) Grol9) (word_add b Grol5) b)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_and (word_not (word_add Grol5 (b:int32)))
             (word_add Grol9 (word_add Grol5 b)) =
    word_and (word_add (word_add b Grol5) Grol9) (word_not (word_add b Grol5)) /\
    word_and (word_add Grol5 (b:int32))
             (word_add Grol14 (word_add Grol9 (word_add Grol5 b))) =
    word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
             (word_add b Grol5)`
   (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `word_add Grol9 (word_add Grol5 (b:int32)) =
        word_add (word_add b Grol5) Grol9 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE];
      SUBGOAL_THEN
       `word_add Grol14 (word_add Grol9 (word_add Grol5 (b:int32))) =
        word_add (word_add (word_add b Grol5) Grol9) Grol14 /\
        word_add Grol5 (b:int32) = word_add b Grol5`
       (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC WORD_RULE; CONV_TAC WORD_BITWISE_RULE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (word_add (b:int32) (word_add w12 (word 2368359562)))
                       (word_and (word_add (word_add b Grol5) Grol9)
                                 (word_not (word_add b Grol5))))
             (word_and (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                       (word_add b Grol5)) =
    word_add (word_add b (word_add w12 (word 2368359562)))
             (md5_G (word_add (word_add (word_add b Grol5) Grol9) Grol14)
                    (word_add (word_add b Grol5) Grol9)
                    (word_add b Grol5))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MD5_G_DISJOINT_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Gstep31:int32 = md5_G (word_add (word_add (word_add (b:int32) Grol5) Grol9) Grol14)
                          (word_add (word_add b Grol5) Grol9)
                          (word_add b Grol5)` THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w12 (word 2368359562))) Gstep31 =
    word_add (word_add b Gstep31) (word_add w12 (word 2368359562))`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let MD5_ROUND1_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 52) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 569) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (let na0 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_F b c d))
                                                (word_add w0 (EL 0 md5_T)))
                                      7) in
                       let nd1 =
                           word_add na0
                            (word_rol (word_add (word_add d (md5_F na0 b c))
                                                (word_add w1 (EL 1 md5_T)))
                                      12) in
                       let nc2 =
                           word_add nd1
                            (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                (word_add w2 (EL 2 md5_T)))
                                      17) in
                       let nb3 =
                           word_add nc2
                            (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                                (word_add w3 (EL 3 md5_T)))
                                      22) in
                       let na4 =
                           word_add nb3
                            (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                                (word_add w4 (EL 4 md5_T)))
                                      7) in
                       let nd5 =
                           word_add na4
                            (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                                (word_add w5 (EL 5 md5_T)))
                                      12) in
                       let nc6 =
                           word_add nd5
                            (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                                (word_add w6 (EL 6 md5_T)))
                                      17) in
                       let nb7 =
                           word_add nc6
                            (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                                (word_add w7 (EL 7 md5_T)))
                                      22) in
                       let na8 =
                           word_add nb7
                            (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                                (word_add w8 (EL 8 md5_T)))
                                      7) in
                       let nd9 =
                           word_add na8
                            (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                                (word_add w9 (EL 9 md5_T)))
                                      12) in
                       let nc10 =
                           word_add nd9
                            (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                                (word_add w10 (EL 10 md5_T)))
                                      17) in
                       let nb11 =
                           word_add nc10
                            (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                                (word_add w11 (EL 11 md5_T)))
                                      22) in
                       let na12 =
                           word_add nb11
                            (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                                (word_add w12 (EL 12 md5_T)))
                                      7) in
                       na12) /\
                  read RDX s =
                    word_zx
                      (let na0 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_F b c d))
                                                (word_add w0 (EL 0 md5_T)))
                                      7) in
                       let nd1 =
                           word_add na0
                            (word_rol (word_add (word_add d (md5_F na0 b c))
                                                (word_add w1 (EL 1 md5_T)))
                                      12) in
                       let nc2 =
                           word_add nd1
                            (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                (word_add w2 (EL 2 md5_T)))
                                      17) in
                       let nb3 =
                           word_add nc2
                            (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                                (word_add w3 (EL 3 md5_T)))
                                      22) in
                       let na4 =
                           word_add nb3
                            (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                                (word_add w4 (EL 4 md5_T)))
                                      7) in
                       let nd5 =
                           word_add na4
                            (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                                (word_add w5 (EL 5 md5_T)))
                                      12) in
                       let nc6 =
                           word_add nd5
                            (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                                (word_add w6 (EL 6 md5_T)))
                                      17) in
                       let nb7 =
                           word_add nc6
                            (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                                (word_add w7 (EL 7 md5_T)))
                                      22) in
                       let na8 =
                           word_add nb7
                            (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                                (word_add w8 (EL 8 md5_T)))
                                      7) in
                       let nd9 =
                           word_add na8
                            (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                                (word_add w9 (EL 9 md5_T)))
                                      12) in
                       let nc10 =
                           word_add nd9
                            (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                                (word_add w10 (EL 10 md5_T)))
                                      17) in
                       let nb11 =
                           word_add nc10
                            (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                                (word_add w11 (EL 11 md5_T)))
                                      22) in
                       let na12 =
                           word_add nb11
                            (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                                (word_add w12 (EL 12 md5_T)))
                                      7) in
                       let nd13 =
                           word_add na12
                            (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                                (word_add w13 (EL 13 md5_T)))
                                      12) in
                       nd13) /\
                  read RCX s =
                    word_zx
                      (let na0 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_F b c d))
                                                (word_add w0 (EL 0 md5_T)))
                                      7) in
                       let nd1 =
                           word_add na0
                            (word_rol (word_add (word_add d (md5_F na0 b c))
                                                (word_add w1 (EL 1 md5_T)))
                                      12) in
                       let nc2 =
                           word_add nd1
                            (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                (word_add w2 (EL 2 md5_T)))
                                      17) in
                       let nb3 =
                           word_add nc2
                            (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                                (word_add w3 (EL 3 md5_T)))
                                      22) in
                       let na4 =
                           word_add nb3
                            (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                                (word_add w4 (EL 4 md5_T)))
                                      7) in
                       let nd5 =
                           word_add na4
                            (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                                (word_add w5 (EL 5 md5_T)))
                                      12) in
                       let nc6 =
                           word_add nd5
                            (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                                (word_add w6 (EL 6 md5_T)))
                                      17) in
                       let nb7 =
                           word_add nc6
                            (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                                (word_add w7 (EL 7 md5_T)))
                                      22) in
                       let na8 =
                           word_add nb7
                            (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                                (word_add w8 (EL 8 md5_T)))
                                      7) in
                       let nd9 =
                           word_add na8
                            (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                                (word_add w9 (EL 9 md5_T)))
                                      12) in
                       let nc10 =
                           word_add nd9
                            (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                                (word_add w10 (EL 10 md5_T)))
                                      17) in
                       let nb11 =
                           word_add nc10
                            (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                                (word_add w11 (EL 11 md5_T)))
                                      22) in
                       let na12 =
                           word_add nb11
                            (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                                (word_add w12 (EL 12 md5_T)))
                                      7) in
                       let nd13 =
                           word_add na12
                            (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                                (word_add w13 (EL 13 md5_T)))
                                      12) in
                       let nc14 =
                           word_add nd13
                            (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                                (word_add w14 (EL 14 md5_T)))
                                      17) in
                       nc14) /\
                  read RBX s =
                    word_zx
                      (let na0 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_F b c d))
                                                (word_add w0 (EL 0 md5_T)))
                                      7) in
                       let nd1 =
                           word_add na0
                            (word_rol (word_add (word_add d (md5_F na0 b c))
                                                (word_add w1 (EL 1 md5_T)))
                                      12) in
                       let nc2 =
                           word_add nd1
                            (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                                (word_add w2 (EL 2 md5_T)))
                                      17) in
                       let nb3 =
                           word_add nc2
                            (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                                (word_add w3 (EL 3 md5_T)))
                                      22) in
                       let na4 =
                           word_add nb3
                            (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                                (word_add w4 (EL 4 md5_T)))
                                      7) in
                       let nd5 =
                           word_add na4
                            (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                                (word_add w5 (EL 5 md5_T)))
                                      12) in
                       let nc6 =
                           word_add nd5
                            (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                                (word_add w6 (EL 6 md5_T)))
                                      17) in
                       let nb7 =
                           word_add nc6
                            (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                                (word_add w7 (EL 7 md5_T)))
                                      22) in
                       let na8 =
                           word_add nb7
                            (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                                (word_add w8 (EL 8 md5_T)))
                                      7) in
                       let nd9 =
                           word_add na8
                            (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                                (word_add w9 (EL 9 md5_T)))
                                      12) in
                       let nc10 =
                           word_add nd9
                            (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                                (word_add w10 (EL 10 md5_T)))
                                      17) in
                       let nb11 =
                           word_add nc10
                            (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                                (word_add w11 (EL 11 md5_T)))
                                      22) in
                       let na12 =
                           word_add nb11
                            (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                                (word_add w12 (EL 12 md5_T)))
                                      7) in
                       let nd13 =
                           word_add na12
                            (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                                (word_add w13 (EL 13 md5_T)))
                                      12) in
                       let nc14 =
                           word_add nd13
                            (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                                (word_add w14 (EL 14 md5_T)))
                                      17) in
                       let nb15 =
                           word_add nc14
                            (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                                (word_add w15 (EL 15 md5_T)))
                                      22) in
                       nb15) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = read RDX s)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
ENSURES_SEQUENCE_TAC `pc + 186`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (word_add b
              (word_rol (word_add (word_add a (md5_F b c d))
                                  (word_add w0 (EL 0 md5_T)))
                        7)) /\
        read RDX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             word_add na0
              (word_rol (word_add (word_add d (md5_F na0 b c))
                                  (word_add w1 (EL 1 md5_T)))
                        12)) /\
        read RCX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             word_add nd1
              (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                  (word_add w2 (EL 2 md5_T)))
                        17)) /\
        read RBX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             word_add nc2
              (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                  (word_add w3 (EL 3 md5_T)))
                        22)) /\
        read R10 s = (word_zx:int32->int64) (w4:int32) /\
        read R11 s = read RDX s /\
        read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15 /\
        read (memory :> bytes32 data_ptr) s = w0` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`;
    `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`]
   MD5_QUARTER1_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 314`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             na4) /\
        read RDX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             nd5) /\
        read RCX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             nc6) /\
        read RBX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             let nb7 =
                 word_add nc6
                  (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                      (word_add w7 (EL 7 md5_T)))
                            22) in
             nb7) /\
        read R10 s = (word_zx:int32->int64) (w8:int32) /\
        read R11 s = read RDX s /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15 /\
        read (memory :> bytes32 data_ptr) s = w0` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      na0):int32`;
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      nb3):int32`;
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      nc2):int32`;
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      nd1):int32`;
    `w4:int32`; `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`]
   MD5_QUARTER2_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 442`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             let nb7 =
                 word_add nc6
                  (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                      (word_add w7 (EL 7 md5_T)))
                            22) in
             let na8 =
                 word_add nb7
                  (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                      (word_add w8 (EL 8 md5_T)))
                            7) in
             na8) /\
        read RDX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             let nb7 =
                 word_add nc6
                  (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                      (word_add w7 (EL 7 md5_T)))
                            22) in
             let na8 =
                 word_add nb7
                  (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                      (word_add w8 (EL 8 md5_T)))
                            7) in
             let nd9 =
                 word_add na8
                  (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                      (word_add w9 (EL 9 md5_T)))
                            12) in
             nd9) /\
        read RCX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             let nb7 =
                 word_add nc6
                  (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                      (word_add w7 (EL 7 md5_T)))
                            22) in
             let na8 =
                 word_add nb7
                  (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                      (word_add w8 (EL 8 md5_T)))
                            7) in
             let nd9 =
                 word_add na8
                  (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                      (word_add w9 (EL 9 md5_T)))
                            12) in
             let nc10 =
                 word_add nd9
                  (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                      (word_add w10 (EL 10 md5_T)))
                            17) in
             nc10) /\
        read RBX s =
          word_zx
            (let na0 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_F b c d))
                                      (word_add w0 (EL 0 md5_T)))
                            7) in
             let nd1 =
                 word_add na0
                  (word_rol (word_add (word_add d (md5_F na0 b c))
                                      (word_add w1 (EL 1 md5_T)))
                            12) in
             let nc2 =
                 word_add nd1
                  (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                      (word_add w2 (EL 2 md5_T)))
                            17) in
             let nb3 =
                 word_add nc2
                  (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                      (word_add w3 (EL 3 md5_T)))
                            22) in
             let na4 =
                 word_add nb3
                  (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                      (word_add w4 (EL 4 md5_T)))
                            7) in
             let nd5 =
                 word_add na4
                  (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                      (word_add w5 (EL 5 md5_T)))
                            12) in
             let nc6 =
                 word_add nd5
                  (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                      (word_add w6 (EL 6 md5_T)))
                            17) in
             let nb7 =
                 word_add nc6
                  (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                      (word_add w7 (EL 7 md5_T)))
                            22) in
             let na8 =
                 word_add nb7
                  (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                      (word_add w8 (EL 8 md5_T)))
                            7) in
             let nd9 =
                 word_add na8
                  (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                      (word_add w9 (EL 9 md5_T)))
                            12) in
             let nc10 =
                 word_add nd9
                  (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                      (word_add w10 (EL 10 md5_T)))
                            17) in
             let nb11 =
                 word_add nc10
                  (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                      (word_add w11 (EL 11 md5_T)))
                            22) in
             nb11) /\
        read R10 s = (word_zx:int32->int64) (w12:int32) /\
        read R11 s = read RDX s /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15 /\
        read (memory :> bytes32 data_ptr) s = w0` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na4 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      na4):int32`;
    (* b := nb7 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      let nb7 =
          word_add nc6
           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                               (word_add w7 (EL 7 md5_T)))
                     22) in
      nb7):int32`;
    (* c := nc6 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      nc6):int32`;
    (* d := nd5 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      nd5):int32`;
    `w8:int32`; `w9:int32`; `w10:int32`; `w11:int32`; `w12:int32`]
   MD5_QUARTER3_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na8 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      let nb7 =
          word_add nc6
           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                               (word_add w7 (EL 7 md5_T)))
                     22) in
      let na8 =
          word_add nb7
           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                               (word_add w8 (EL 8 md5_T)))
                     7) in
      na8):int32`;
    (* b := nb11 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      let nb7 =
          word_add nc6
           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                               (word_add w7 (EL 7 md5_T)))
                     22) in
      let na8 =
          word_add nb7
           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                               (word_add w8 (EL 8 md5_T)))
                     7) in
      let nd9 =
          word_add na8
           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                               (word_add w9 (EL 9 md5_T)))
                     12) in
      let nc10 =
          word_add nd9
           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                               (word_add w10 (EL 10 md5_T)))
                     17) in
      let nb11 =
          word_add nc10
           (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                               (word_add w11 (EL 11 md5_T)))
                     22) in
      nb11):int32`;
    (* c := nc10 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      let nb7 =
          word_add nc6
           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                               (word_add w7 (EL 7 md5_T)))
                     22) in
      let na8 =
          word_add nb7
           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                               (word_add w8 (EL 8 md5_T)))
                     7) in
      let nd9 =
          word_add na8
           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                               (word_add w9 (EL 9 md5_T)))
                     12) in
      let nc10 =
          word_add nd9
           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                               (word_add w10 (EL 10 md5_T)))
                     17) in
      nc10):int32`;
    (* d := nd9 *)
    `(let na0 =
          word_add b
           (word_rol (word_add (word_add a (md5_F b c d))
                               (word_add w0 (EL 0 md5_T)))
                     7) in
      let nd1 =
          word_add na0
           (word_rol (word_add (word_add d (md5_F na0 b c))
                               (word_add w1 (EL 1 md5_T)))
                     12) in
      let nc2 =
          word_add nd1
           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                               (word_add w2 (EL 2 md5_T)))
                     17) in
      let nb3 =
          word_add nc2
           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                               (word_add w3 (EL 3 md5_T)))
                     22) in
      let na4 =
          word_add nb3
           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                               (word_add w4 (EL 4 md5_T)))
                     7) in
      let nd5 =
          word_add na4
           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                               (word_add w5 (EL 5 md5_T)))
                     12) in
      let nc6 =
          word_add nd5
           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                               (word_add w6 (EL 6 md5_T)))
                     17) in
      let nb7 =
          word_add nc6
           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                               (word_add w7 (EL 7 md5_T)))
                     22) in
      let na8 =
          word_add nb7
           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                               (word_add w8 (EL 8 md5_T)))
                     7) in
      let nd9 =
          word_add na8
           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                               (word_add w9 (EL 9 md5_T)))
                     12) in
      nd9):int32`;
    `w0:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`]
   MD5_QUARTER4_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* MD5 round 3 (H): quarters 9..12.                                          *)
(*                                                                           *)
(* Q9 covers steps 32..35 — the first H-round quarter.                        *)
(* H(x,y,z) = x XOR y XOR z is its own bridge: no helper lemma is needed     *)
(* (XOR is associative and commutative). The asm encodes H via a chain of   *)
(* xorl instructions on R11, then the rotation/rotate-add. Step 35 embeds   *)
(* the next-quarter R10 reload (movl 4(%rsi),%r10d), so post R10 = w1.       *)
(* Post R11 = read RCX s (the asm sets R11 = ECX after the xor chain ends). *)
(* R12 is NOT touched in round 3 (no LEAL/AND/NOT idiom in H), so the       *)
(* MAYCHANGE frame drops R12.                                                *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER9_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w0:int32) (w1:int32) (w5:int32) (w8:int32) (w11:int32) (w14:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1185) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w0 /\
                   read R11 s = word_zx (word_zx d:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s =
                     w1 /\
                   read (memory :> bytes32 (word_add data_ptr (word 20))) s =
                     w5 /\
                   read (memory :> bytes32 (word_add data_ptr (word 32))) s =
                     w8 /\
                   read (memory :> bytes32 (word_add data_ptr (word 44))) s =
                     w11 /\
                   read (memory :> bytes32 (word_add data_ptr (word 56))) s =
                     w14)
              (\s. read RIP s = word(pc + 1308) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_H b c d))
                                                  (word_add w5 (EL 32 md5_T)))
                                        4)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w5 (EL 32 md5_T)))
                                       4) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_H na0 b c))
                                             (word_add w8 (EL 33 md5_T)))
                                   11)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w5 (EL 32 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w8 (EL 33 md5_T)))
                                       11) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                             (word_add w11 (EL 34 md5_T)))
                                   16)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w5 (EL 32 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w8 (EL 33 md5_T)))
                                       11) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                                 (word_add w11 (EL 34 md5_T)))
                                       16) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_H nc2 nd1 na0))
                                             (word_add w14 (EL 35 md5_T)))
                                   23)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w1 /\
                   read R11 s = read RCX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_H] THEN
  CONJ_TAC THENL
   [(* RAX: step-32 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-33 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w5 (word 4294588738)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w5 (word 4294588738))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w5 (word 4294588738))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-34 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w5 (word 4294588738)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w5 (word 4294588738))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w5 (word 4294588738))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w8 (word 2272392833)))
               (word_xor (word_add b Hrol4) (word_xor b c)) =
      word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
               (word_add w8 (word 2272392833))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol11:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor (word_add b Hrol4)
                                                    (word_xor b c)))
                                (word_add w8 (word 2272392833))) 11` THEN
    SUBGOAL_THEN
     `word_add Hrol11 (word_add (b:int32) Hrol4) =
      word_add (word_add b Hrol4) Hrol11`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (word_add (b:int32) Hrol4) b)
               (word_add (word_add b Hrol4) Hrol11) =
      word_xor (word_add (word_add b Hrol4) Hrol11)
               (word_xor (word_add b Hrol4) b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w11 (word 1839030562)))
               (word_xor (word_add (word_add b Hrol4) Hrol11)
                         (word_xor (word_add b Hrol4) b)) =
      word_add (word_add c
                         (word_xor (word_add (word_add b Hrol4) Hrol11)
                                   (word_xor (word_add b Hrol4) b)))
               (word_add w11 (word 1839030562))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-35 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_xor (c:int32) d) b = word_xor b (word_xor c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:int32 y. word_add (word_add (a:int32) (word_add w5 (word 4294588738)))
                         (word_xor x y) =
                word_add (word_add a (word_xor x y))
                         (word_add w5 (word 4294588738))`
   ASSUME_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Hrol4:int32 = word_rol
                   (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                             (word_add w5 (word 4294588738))) 4` THEN
  SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
    word_xor (word_add b Hrol4) (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (word_add w8 (word 2272392833)))
             (word_xor (word_add b Hrol4) (word_xor b c)) =
    word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
             (word_add w8 (word 2272392833))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol11:int32 = word_rol
                    (word_add (word_add (d:int32)
                                        (word_xor (word_add b Hrol4)
                                                  (word_xor b c)))
                              (word_add w8 (word 2272392833))) 11` THEN
  SUBGOAL_THEN
   `word_add Hrol11 (word_add (b:int32) Hrol4) =
    word_add (word_add b Hrol4) Hrol11`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (b:int32) Hrol4) b)
             (word_add (word_add b Hrol4) Hrol11) =
    word_xor (word_add (word_add b Hrol4) Hrol11)
             (word_xor (word_add b Hrol4) b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (word_add w11 (word 1839030562)))
             (word_xor (word_add (word_add b Hrol4) Hrol11)
                       (word_xor (word_add b Hrol4) b)) =
    word_add (word_add c
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_xor (word_add b Hrol4) b)))
             (word_add w11 (word 1839030562))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol16:int32 = word_rol
                    (word_add (word_add (c:int32)
                                        (word_xor (word_add (word_add b Hrol4)
                                                            Hrol11)
                                                  (word_xor (word_add b Hrol4)
                                                            b)))
                              (word_add w11 (word 1839030562))) 16` THEN
  SUBGOAL_THEN
   `word_add Hrol16 (word_add (word_add (b:int32) Hrol4) Hrol11) =
    word_add (word_add (word_add b Hrol4) Hrol11) Hrol16`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (word_add (b:int32) Hrol4) Hrol11)
                       (word_add b Hrol4))
             (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16) =
    word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
             (word_xor (word_add (word_add b Hrol4) Hrol11) (word_add b Hrol4))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w14 (word 4259657740)))
             (word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_add b Hrol4))) =
    word_add (word_add b
                       (word_xor (word_add (word_add (word_add b Hrol4) Hrol11)
                                           Hrol16)
                                 (word_xor (word_add (word_add b Hrol4) Hrol11)
                                           (word_add b Hrol4))))
             (word_add w14 (word 4259657740))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 — Round 3 (H) quarter 10 (MD5 steps 36..39). 32 stepper steps,    *)
(* spanning [pc+1308, pc+1424). H encoding closes via the same template as   *)
(* Q9 (xor-swap + reassoc + cascading rotation abbreviations).               *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER10_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w1:int32) (w4:int32) (w7:int32) (w10:int32) (w13:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1308) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w1 /\
                   read R11 s = word_zx (word_zx c:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s =
                     w4 /\
                   read (memory :> bytes32 (word_add data_ptr (word 28))) s =
                     w7 /\
                   read (memory :> bytes32 (word_add data_ptr (word 40))) s =
                     w10 /\
                   read (memory :> bytes32 (word_add data_ptr (word 52))) s =
                     w13)
              (\s. read RIP s = word(pc + 1424) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_H b c d))
                                                  (word_add w1 (EL 36 md5_T)))
                                        4)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w1 (EL 36 md5_T)))
                                       4) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_H na0 b c))
                                             (word_add w4 (EL 37 md5_T)))
                                   11)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w1 (EL 36 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w4 (EL 37 md5_T)))
                                       11) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                             (word_add w7 (EL 38 md5_T)))
                                   16)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w1 (EL 36 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w4 (EL 37 md5_T)))
                                       11) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                                 (word_add w7 (EL 38 md5_T)))
                                       16) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_H nc2 nd1 na0))
                                             (word_add w10 (EL 39 md5_T)))
                                   23)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w13 /\
                   read R11 s = read RCX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_H] THEN
  CONJ_TAC THENL
   [(* RAX: step-36 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-37 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w1 (word 2763975236)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w1 (word 2763975236))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w1 (word 2763975236))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-38 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w1 (word 2763975236)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w1 (word 2763975236))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w1 (word 2763975236))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w4 (word 1272893353)))
               (word_xor (word_add b Hrol4) (word_xor b c)) =
      word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
               (word_add w4 (word 1272893353))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol11:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor (word_add b Hrol4)
                                                    (word_xor b c)))
                                (word_add w4 (word 1272893353))) 11` THEN
    SUBGOAL_THEN
     `word_add Hrol11 (word_add (b:int32) Hrol4) =
      word_add (word_add b Hrol4) Hrol11`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (word_add (b:int32) Hrol4) b)
               (word_add (word_add b Hrol4) Hrol11) =
      word_xor (word_add (word_add b Hrol4) Hrol11)
               (word_xor (word_add b Hrol4) b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w7 (word 4139469664)))
               (word_xor (word_add (word_add b Hrol4) Hrol11)
                         (word_xor (word_add b Hrol4) b)) =
      word_add (word_add c
                         (word_xor (word_add (word_add b Hrol4) Hrol11)
                                   (word_xor (word_add b Hrol4) b)))
               (word_add w7 (word 4139469664))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-39 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_xor (c:int32) d) b = word_xor b (word_xor c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:int32 y. word_add (word_add (a:int32) (word_add w1 (word 2763975236)))
                         (word_xor x y) =
                word_add (word_add a (word_xor x y))
                         (word_add w1 (word 2763975236))`
   ASSUME_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Hrol4:int32 = word_rol
                   (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                             (word_add w1 (word 2763975236))) 4` THEN
  SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
    word_xor (word_add b Hrol4) (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (word_add w4 (word 1272893353)))
             (word_xor (word_add b Hrol4) (word_xor b c)) =
    word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
             (word_add w4 (word 1272893353))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol11:int32 = word_rol
                    (word_add (word_add (d:int32)
                                        (word_xor (word_add b Hrol4)
                                                  (word_xor b c)))
                              (word_add w4 (word 1272893353))) 11` THEN
  SUBGOAL_THEN
   `word_add Hrol11 (word_add (b:int32) Hrol4) =
    word_add (word_add b Hrol4) Hrol11`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (b:int32) Hrol4) b)
             (word_add (word_add b Hrol4) Hrol11) =
    word_xor (word_add (word_add b Hrol4) Hrol11)
             (word_xor (word_add b Hrol4) b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (word_add w7 (word 4139469664)))
             (word_xor (word_add (word_add b Hrol4) Hrol11)
                       (word_xor (word_add b Hrol4) b)) =
    word_add (word_add c
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_xor (word_add b Hrol4) b)))
             (word_add w7 (word 4139469664))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol16:int32 = word_rol
                    (word_add (word_add (c:int32)
                                        (word_xor (word_add (word_add b Hrol4)
                                                            Hrol11)
                                                  (word_xor (word_add b Hrol4)
                                                            b)))
                              (word_add w7 (word 4139469664))) 16` THEN
  SUBGOAL_THEN
   `word_add Hrol16 (word_add (word_add (b:int32) Hrol4) Hrol11) =
    word_add (word_add (word_add b Hrol4) Hrol11) Hrol16`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (word_add (b:int32) Hrol4) Hrol11)
                       (word_add b Hrol4))
             (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16) =
    word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
             (word_xor (word_add (word_add b Hrol4) Hrol11) (word_add b Hrol4))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w10 (word 3200236656)))
             (word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_add b Hrol4))) =
    word_add (word_add b
                       (word_xor (word_add (word_add (word_add b Hrol4) Hrol11)
                                           Hrol16)
                                 (word_xor (word_add (word_add b Hrol4) Hrol11)
                                           (word_add b Hrol4))))
             (word_add w10 (word 3200236656))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let MD5_QUARTER11_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w0:int32) (w3:int32) (w6:int32) (w9:int32) (w13:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1424) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w13 /\
                   read R11 s = word_zx (word_zx c:int32) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                   read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                   read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9)
              (\s. read RIP s = word(pc + 1539) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_H b c d))
                                                  (word_add w13 (EL 40 md5_T)))
                                        4)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w13 (EL 40 md5_T)))
                                       4) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_H na0 b c))
                                             (word_add w0 (EL 41 md5_T)))
                                   11)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w13 (EL 40 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w0 (EL 41 md5_T)))
                                       11) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                             (word_add w3 (EL 42 md5_T)))
                                   16)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w13 (EL 40 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w0 (EL 41 md5_T)))
                                       11) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                                 (word_add w3 (EL 42 md5_T)))
                                       16) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_H nc2 nd1 na0))
                                             (word_add w6 (EL 43 md5_T)))
                                   23)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w9 /\
                   read R11 s = read RCX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_H] THEN
  CONJ_TAC THENL
   [(* RAX: step-40 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-41 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w13 (word 681279174)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w13 (word 681279174))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w13 (word 681279174))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-42 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w13 (word 681279174)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w13 (word 681279174))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w13 (word 681279174))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w0 (word 3936430074)))
               (word_xor (word_add b Hrol4) (word_xor b c)) =
      word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
               (word_add w0 (word 3936430074))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol11:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor (word_add b Hrol4)
                                                    (word_xor b c)))
                                (word_add w0 (word 3936430074))) 11` THEN
    SUBGOAL_THEN
     `word_add Hrol11 (word_add (b:int32) Hrol4) =
      word_add (word_add b Hrol4) Hrol11`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (word_add (b:int32) Hrol4) b)
               (word_add (word_add b Hrol4) Hrol11) =
      word_xor (word_add (word_add b Hrol4) Hrol11)
               (word_xor (word_add b Hrol4) b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w3 (word 3572445317)))
               (word_xor (word_add (word_add b Hrol4) Hrol11)
                         (word_xor (word_add b Hrol4) b)) =
      word_add (word_add c
                         (word_xor (word_add (word_add b Hrol4) Hrol11)
                                   (word_xor (word_add b Hrol4) b)))
               (word_add w3 (word 3572445317))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-43 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_xor (c:int32) d) b = word_xor b (word_xor c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:int32 y. word_add (word_add (a:int32) (word_add w13 (word 681279174)))
                         (word_xor x y) =
                word_add (word_add a (word_xor x y))
                         (word_add w13 (word 681279174))`
   ASSUME_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Hrol4:int32 = word_rol
                   (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                             (word_add w13 (word 681279174))) 4` THEN
  SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
    word_xor (word_add b Hrol4) (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (word_add w0 (word 3936430074)))
             (word_xor (word_add b Hrol4) (word_xor b c)) =
    word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
             (word_add w0 (word 3936430074))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol11:int32 = word_rol
                    (word_add (word_add (d:int32)
                                        (word_xor (word_add b Hrol4)
                                                  (word_xor b c)))
                              (word_add w0 (word 3936430074))) 11` THEN
  SUBGOAL_THEN
   `word_add Hrol11 (word_add (b:int32) Hrol4) =
    word_add (word_add b Hrol4) Hrol11`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (b:int32) Hrol4) b)
             (word_add (word_add b Hrol4) Hrol11) =
    word_xor (word_add (word_add b Hrol4) Hrol11)
             (word_xor (word_add b Hrol4) b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (word_add w3 (word 3572445317)))
             (word_xor (word_add (word_add b Hrol4) Hrol11)
                       (word_xor (word_add b Hrol4) b)) =
    word_add (word_add c
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_xor (word_add b Hrol4) b)))
             (word_add w3 (word 3572445317))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol16:int32 = word_rol
                    (word_add (word_add (c:int32)
                                        (word_xor (word_add (word_add b Hrol4)
                                                            Hrol11)
                                                  (word_xor (word_add b Hrol4)
                                                            b)))
                              (word_add w3 (word 3572445317))) 16` THEN
  SUBGOAL_THEN
   `word_add Hrol16 (word_add (word_add (b:int32) Hrol4) Hrol11) =
    word_add (word_add (word_add b Hrol4) Hrol11) Hrol16`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (word_add (b:int32) Hrol4) Hrol11)
                       (word_add b Hrol4))
             (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16) =
    word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
             (word_xor (word_add (word_add b Hrol4) Hrol11) (word_add b Hrol4))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w6 (word 76029189)))
             (word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_add b Hrol4))) =
    word_add (word_add b
                       (word_xor (word_add (word_add (word_add b Hrol4) Hrol11)
                                           Hrol16)
                                 (word_xor (word_add (word_add b Hrol4) Hrol11)
                                           (word_add b Hrol4))))
             (word_add w6 (word 76029189))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Round 3, fourth quarter (MD5 steps 44..47).                                *)
(* PC range [pc+1539, pc+1654), 32 stepper steps.  Mirrors Q10/Q11 (the       *)
(* canonical round-3 quarter template) with K(44..47) = [9;12;15;2] and       *)
(* T[44..47] = 3654602809 / 3873151461 / 530742520 / 3299628645.  Q11's       *)
(* embedded tail reload at step 43 leaves R10 = w9, which Q12's first         *)
(* `leal` consumes; Q12's own step-47 tail is `mov (%rsi),%r10d`, so the      *)
(* post exports `read R10 s = word_zx w0` for the round-3 -> round-4 entry.   *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER12_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w0:int32) (w2:int32) (w9:int32) (w12:int32) (w15:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1539) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w9 /\
                   read R11 s = word_zx (word_zx c:int32) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                   read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                   read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
              (\s. read RIP s = word(pc + 1654) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_H b c d))
                                                  (word_add w9 (EL 44 md5_T)))
                                        4)) /\
                   read RDX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w9 (EL 44 md5_T)))
                                       4) in
                        word_add na0
                         (word_rol (word_add (word_add d (md5_H na0 b c))
                                             (word_add w12 (EL 45 md5_T)))
                                   11)) /\
                   read RCX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w9 (EL 44 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w12 (EL 45 md5_T)))
                                       11) in
                        word_add nd1
                         (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                             (word_add w15 (EL 46 md5_T)))
                                   16)) /\
                   read RBX s =
                     word_zx
                       (let na0 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_H b c d))
                                                 (word_add w9 (EL 44 md5_T)))
                                       4) in
                        let nd1 =
                            word_add na0
                             (word_rol (word_add (word_add d (md5_H na0 b c))
                                                 (word_add w12 (EL 45 md5_T)))
                                       11) in
                        let nc2 =
                            word_add nd1
                             (word_rol (word_add (word_add c (md5_H nd1 na0 b))
                                                 (word_add w15 (EL 46 md5_T)))
                                       16) in
                        word_add nc2
                         (word_rol (word_add (word_add b (md5_H nc2 nd1 na0))
                                             (word_add w2 (EL 47 md5_T)))
                                   23)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w0 /\
                   read R11 s = read RCX s)
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_H] THEN
  CONJ_TAC THENL
   [(* RAX: step-44 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-45 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w9 (word 3654602809)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w9 (word 3654602809))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w9 (word 3654602809))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-46 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `word_xor (word_xor c d) (b:int32) = word_xor b (word_xor c d)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (a:int32) (word_add w9 (word 3654602809)))
               (word_xor b (word_xor c d)) =
      word_add (word_add a (word_xor b (word_xor c d)))
               (word_add w9 (word 3654602809))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol4:int32 = word_rol
                     (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                               (word_add w9 (word 3654602809))) 4` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
      word_xor (word_add b Hrol4) (word_xor b c)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (d:int32) (word_add w12 (word 3873151461)))
               (word_xor (word_add b Hrol4) (word_xor b c)) =
      word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
               (word_add w12 (word 3873151461))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Hrol11:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor (word_add b Hrol4)
                                                    (word_xor b c)))
                                (word_add w12 (word 3873151461))) 11` THEN
    SUBGOAL_THEN
     `word_add Hrol11 (word_add (b:int32) Hrol4) =
      word_add (word_add b Hrol4) Hrol11`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_xor (word_xor (word_add (b:int32) Hrol4) b)
               (word_add (word_add b Hrol4) Hrol11) =
      word_xor (word_add (word_add b Hrol4) Hrol11)
               (word_xor (word_add b Hrol4) b)`
     SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add (c:int32) (word_add w15 (word 530742520)))
               (word_xor (word_add (word_add b Hrol4) Hrol11)
                         (word_xor (word_add b Hrol4) b)) =
      word_add (word_add c
                         (word_xor (word_add (word_add b Hrol4) Hrol11)
                                   (word_xor (word_add b Hrol4) b)))
               (word_add w15 (word 530742520))`
     SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* RBX: step-47 result *)
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_xor (word_xor (c:int32) d) b = word_xor b (word_xor c d)`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:int32 y. word_add (word_add (a:int32) (word_add w9 (word 3654602809)))
                         (word_xor x y) =
                word_add (word_add a (word_xor x y))
                         (word_add w9 (word 3654602809))`
   ASSUME_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Hrol4:int32 = word_rol
                   (word_add (word_add (a:int32) (word_xor b (word_xor c d)))
                             (word_add w9 (word 3654602809))) 4` THEN
  SUBGOAL_THEN `word_add Hrol4 (b:int32) = word_add b Hrol4`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (b:int32) c) (word_add b Hrol4) =
    word_xor (word_add b Hrol4) (word_xor b c)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (d:int32) (word_add w12 (word 3873151461)))
             (word_xor (word_add b Hrol4) (word_xor b c)) =
    word_add (word_add d (word_xor (word_add b Hrol4) (word_xor b c)))
             (word_add w12 (word 3873151461))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol11:int32 = word_rol
                    (word_add (word_add (d:int32)
                                        (word_xor (word_add b Hrol4)
                                                  (word_xor b c)))
                              (word_add w12 (word 3873151461))) 11` THEN
  SUBGOAL_THEN
   `word_add Hrol11 (word_add (b:int32) Hrol4) =
    word_add (word_add b Hrol4) Hrol11`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (b:int32) Hrol4) b)
             (word_add (word_add b Hrol4) Hrol11) =
    word_xor (word_add (word_add b Hrol4) Hrol11)
             (word_xor (word_add b Hrol4) b)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (c:int32) (word_add w15 (word 530742520)))
             (word_xor (word_add (word_add b Hrol4) Hrol11)
                       (word_xor (word_add b Hrol4) b)) =
    word_add (word_add c
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_xor (word_add b Hrol4) b)))
             (word_add w15 (word 530742520))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
   `Hrol16:int32 = word_rol
                    (word_add (word_add (c:int32)
                                        (word_xor (word_add (word_add b Hrol4)
                                                            Hrol11)
                                                  (word_xor (word_add b Hrol4)
                                                            b)))
                              (word_add w15 (word 530742520))) 16` THEN
  SUBGOAL_THEN
   `word_add Hrol16 (word_add (word_add (b:int32) Hrol4) Hrol11) =
    word_add (word_add (word_add b Hrol4) Hrol11) Hrol16`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_add (word_add (b:int32) Hrol4) Hrol11)
                       (word_add b Hrol4))
             (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16) =
    word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
             (word_xor (word_add (word_add b Hrol4) Hrol11) (word_add b Hrol4))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_add (word_add (b:int32) (word_add w2 (word 3299628645)))
             (word_xor (word_add (word_add (word_add b Hrol4) Hrol11) Hrol16)
                       (word_xor (word_add (word_add b Hrol4) Hrol11)
                                 (word_add b Hrol4))) =
    word_add (word_add b
                       (word_xor (word_add (word_add (word_add b Hrol4) Hrol11)
                                           Hrol16)
                                 (word_xor (word_add (word_add b Hrol4) Hrol11)
                                           (word_add b Hrol4))))
             (word_add w2 (word 3299628645))`
   (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let MD5_ROUND2_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 569) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read R10 s = word_zx w0 /\
                  read R11 s = word_zx (word_zx d:int32) /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 1185) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (let na16 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_G b c d))
                                                (word_add w1 (EL 16 md5_T)))
                                      5) in
                       let nd17 =
                           word_add na16
                            (word_rol (word_add (word_add d (md5_G na16 b c))
                                                (word_add w6 (EL 17 md5_T)))
                                      9) in
                       let nc18 =
                           word_add nd17
                            (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                                (word_add w11 (EL 18 md5_T)))
                                      14) in
                       let nb19 =
                           word_add nc18
                            (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                                (word_add w0 (EL 19 md5_T)))
                                      20) in
                       let na20 =
                           word_add nb19
                            (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                                (word_add w5 (EL 20 md5_T)))
                                      5) in
                       let nd21 =
                           word_add na20
                            (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                                (word_add w10 (EL 21 md5_T)))
                                      9) in
                       let nc22 =
                           word_add nd21
                            (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                                (word_add w15 (EL 22 md5_T)))
                                      14) in
                       let nb23 =
                           word_add nc22
                            (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                                (word_add w4 (EL 23 md5_T)))
                                      20) in
                       let na24 =
                           word_add nb23
                            (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                                (word_add w9 (EL 24 md5_T)))
                                      5) in
                       let nd25 =
                           word_add na24
                            (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                                (word_add w14 (EL 25 md5_T)))
                                      9) in
                       let nc26 =
                           word_add nd25
                            (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                                (word_add w3 (EL 26 md5_T)))
                                      14) in
                       let nb27 =
                           word_add nc26
                            (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                                (word_add w8 (EL 27 md5_T)))
                                      20) in
                       let na28 =
                           word_add nb27
                            (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                                (word_add w13 (EL 28 md5_T)))
                                      5) in
                       na28) /\
                  read RDX s =
                    word_zx
                      (let na16 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_G b c d))
                                                (word_add w1 (EL 16 md5_T)))
                                      5) in
                       let nd17 =
                           word_add na16
                            (word_rol (word_add (word_add d (md5_G na16 b c))
                                                (word_add w6 (EL 17 md5_T)))
                                      9) in
                       let nc18 =
                           word_add nd17
                            (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                                (word_add w11 (EL 18 md5_T)))
                                      14) in
                       let nb19 =
                           word_add nc18
                            (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                                (word_add w0 (EL 19 md5_T)))
                                      20) in
                       let na20 =
                           word_add nb19
                            (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                                (word_add w5 (EL 20 md5_T)))
                                      5) in
                       let nd21 =
                           word_add na20
                            (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                                (word_add w10 (EL 21 md5_T)))
                                      9) in
                       let nc22 =
                           word_add nd21
                            (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                                (word_add w15 (EL 22 md5_T)))
                                      14) in
                       let nb23 =
                           word_add nc22
                            (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                                (word_add w4 (EL 23 md5_T)))
                                      20) in
                       let na24 =
                           word_add nb23
                            (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                                (word_add w9 (EL 24 md5_T)))
                                      5) in
                       let nd25 =
                           word_add na24
                            (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                                (word_add w14 (EL 25 md5_T)))
                                      9) in
                       let nc26 =
                           word_add nd25
                            (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                                (word_add w3 (EL 26 md5_T)))
                                      14) in
                       let nb27 =
                           word_add nc26
                            (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                                (word_add w8 (EL 27 md5_T)))
                                      20) in
                       let na28 =
                           word_add nb27
                            (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                                (word_add w13 (EL 28 md5_T)))
                                      5) in
                       let nd29 =
                           word_add na28
                            (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                                (word_add w2 (EL 29 md5_T)))
                                      9) in
                       nd29) /\
                  read RCX s =
                    word_zx
                      (let na16 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_G b c d))
                                                (word_add w1 (EL 16 md5_T)))
                                      5) in
                       let nd17 =
                           word_add na16
                            (word_rol (word_add (word_add d (md5_G na16 b c))
                                                (word_add w6 (EL 17 md5_T)))
                                      9) in
                       let nc18 =
                           word_add nd17
                            (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                                (word_add w11 (EL 18 md5_T)))
                                      14) in
                       let nb19 =
                           word_add nc18
                            (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                                (word_add w0 (EL 19 md5_T)))
                                      20) in
                       let na20 =
                           word_add nb19
                            (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                                (word_add w5 (EL 20 md5_T)))
                                      5) in
                       let nd21 =
                           word_add na20
                            (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                                (word_add w10 (EL 21 md5_T)))
                                      9) in
                       let nc22 =
                           word_add nd21
                            (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                                (word_add w15 (EL 22 md5_T)))
                                      14) in
                       let nb23 =
                           word_add nc22
                            (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                                (word_add w4 (EL 23 md5_T)))
                                      20) in
                       let na24 =
                           word_add nb23
                            (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                                (word_add w9 (EL 24 md5_T)))
                                      5) in
                       let nd25 =
                           word_add na24
                            (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                                (word_add w14 (EL 25 md5_T)))
                                      9) in
                       let nc26 =
                           word_add nd25
                            (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                                (word_add w3 (EL 26 md5_T)))
                                      14) in
                       let nb27 =
                           word_add nc26
                            (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                                (word_add w8 (EL 27 md5_T)))
                                      20) in
                       let na28 =
                           word_add nb27
                            (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                                (word_add w13 (EL 28 md5_T)))
                                      5) in
                       let nd29 =
                           word_add na28
                            (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                                (word_add w2 (EL 29 md5_T)))
                                      9) in
                       let nc30 =
                           word_add nd29
                            (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                                (word_add w7 (EL 30 md5_T)))
                                      14) in
                       nc30) /\
                  read RBX s =
                    word_zx
                      (let na16 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_G b c d))
                                                (word_add w1 (EL 16 md5_T)))
                                      5) in
                       let nd17 =
                           word_add na16
                            (word_rol (word_add (word_add d (md5_G na16 b c))
                                                (word_add w6 (EL 17 md5_T)))
                                      9) in
                       let nc18 =
                           word_add nd17
                            (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                                (word_add w11 (EL 18 md5_T)))
                                      14) in
                       let nb19 =
                           word_add nc18
                            (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                                (word_add w0 (EL 19 md5_T)))
                                      20) in
                       let na20 =
                           word_add nb19
                            (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                                (word_add w5 (EL 20 md5_T)))
                                      5) in
                       let nd21 =
                           word_add na20
                            (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                                (word_add w10 (EL 21 md5_T)))
                                      9) in
                       let nc22 =
                           word_add nd21
                            (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                                (word_add w15 (EL 22 md5_T)))
                                      14) in
                       let nb23 =
                           word_add nc22
                            (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                                (word_add w4 (EL 23 md5_T)))
                                      20) in
                       let na24 =
                           word_add nb23
                            (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                                (word_add w9 (EL 24 md5_T)))
                                      5) in
                       let nd25 =
                           word_add na24
                            (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                                (word_add w14 (EL 25 md5_T)))
                                      9) in
                       let nc26 =
                           word_add nd25
                            (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                                (word_add w3 (EL 26 md5_T)))
                                      14) in
                       let nb27 =
                           word_add nc26
                            (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                                (word_add w8 (EL 27 md5_T)))
                                      20) in
                       let na28 =
                           word_add nb27
                            (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                                (word_add w13 (EL 28 md5_T)))
                                      5) in
                       let nd29 =
                           word_add na28
                            (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                                (word_add w2 (EL 29 md5_T)))
                                      9) in
                       let nc30 =
                           word_add nd29
                            (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                                (word_add w7 (EL 30 md5_T)))
                                      14) in
                       let nb31 =
                           word_add nc30
                            (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                                (word_add w12 (EL 31 md5_T)))
                                      20) in
                       nb31) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = read RDX s /\
                  read R12 s = read RDX s)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11; R12] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
ENSURES_SEQUENCE_TAC `pc + 730`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             na16) /\
        read RDX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             nd17) /\
        read RCX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             nc18) /\
        read RBX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             nb19) /\
        read R10 s = (word_zx:int32->int64) (w5:int32) /\
        read R11 s = read RDX s /\
        read R12 s = read RDX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`;
    `w0:int32`; `w1:int32`; `w5:int32`; `w6:int32`; `w11:int32`]
   MD5_QUARTER5_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 882`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             na20) /\
        read RDX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             nd21) /\
        read RCX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             nc22) /\
        read RBX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             let nb23 =
                 word_add nc22
                  (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                      (word_add w4 (EL 23 md5_T)))
                            20) in
             nb23) /\
        read R10 s = (word_zx:int32->int64) (w9:int32) /\
        read R11 s = read RDX s /\
        read R12 s = read RDX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na16 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      na16):int32`;
    (* b := nb19 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      nb19):int32`;
    (* c := nc18 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      nc18):int32`;
    (* d := nd17 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      nd17):int32`;
    `w4:int32`; `w5:int32`; `w9:int32`; `w10:int32`; `w15:int32`]
   MD5_QUARTER6_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 1034`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             let nb23 =
                 word_add nc22
                  (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                      (word_add w4 (EL 23 md5_T)))
                            20) in
             let na24 =
                 word_add nb23
                  (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                      (word_add w9 (EL 24 md5_T)))
                            5) in
             na24) /\
        read RDX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             let nb23 =
                 word_add nc22
                  (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                      (word_add w4 (EL 23 md5_T)))
                            20) in
             let na24 =
                 word_add nb23
                  (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                      (word_add w9 (EL 24 md5_T)))
                            5) in
             let nd25 =
                 word_add na24
                  (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                      (word_add w14 (EL 25 md5_T)))
                            9) in
             nd25) /\
        read RCX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             let nb23 =
                 word_add nc22
                  (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                      (word_add w4 (EL 23 md5_T)))
                            20) in
             let na24 =
                 word_add nb23
                  (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                      (word_add w9 (EL 24 md5_T)))
                            5) in
             let nd25 =
                 word_add na24
                  (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                      (word_add w14 (EL 25 md5_T)))
                            9) in
             let nc26 =
                 word_add nd25
                  (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                      (word_add w3 (EL 26 md5_T)))
                            14) in
             nc26) /\
        read RBX s =
          word_zx
            (let na16 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_G b c d))
                                      (word_add w1 (EL 16 md5_T)))
                            5) in
             let nd17 =
                 word_add na16
                  (word_rol (word_add (word_add d (md5_G na16 b c))
                                      (word_add w6 (EL 17 md5_T)))
                            9) in
             let nc18 =
                 word_add nd17
                  (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                                      (word_add w11 (EL 18 md5_T)))
                            14) in
             let nb19 =
                 word_add nc18
                  (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                                      (word_add w0 (EL 19 md5_T)))
                            20) in
             let na20 =
                 word_add nb19
                  (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                      (word_add w5 (EL 20 md5_T)))
                            5) in
             let nd21 =
                 word_add na20
                  (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                      (word_add w10 (EL 21 md5_T)))
                            9) in
             let nc22 =
                 word_add nd21
                  (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                      (word_add w15 (EL 22 md5_T)))
                            14) in
             let nb23 =
                 word_add nc22
                  (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                      (word_add w4 (EL 23 md5_T)))
                            20) in
             let na24 =
                 word_add nb23
                  (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                      (word_add w9 (EL 24 md5_T)))
                            5) in
             let nd25 =
                 word_add na24
                  (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                      (word_add w14 (EL 25 md5_T)))
                            9) in
             let nc26 =
                 word_add nd25
                  (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                      (word_add w3 (EL 26 md5_T)))
                            14) in
             let nb27 =
                 word_add nc26
                  (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                      (word_add w8 (EL 27 md5_T)))
                            20) in
             nb27) /\
        read R10 s = (word_zx:int32->int64) (w13:int32) /\
        read R11 s = read RDX s /\
        read R12 s = read RDX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na20 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      na20):int32`;
    (* b := nb23 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      let nb23 =
          word_add nc22
           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                               (word_add w4 (EL 23 md5_T)))
                     20) in
      nb23):int32`;
    (* c := nc22 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      nc22):int32`;
    (* d := nd21 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      nd21):int32`;
    `w3:int32`; `w8:int32`; `w9:int32`; `w13:int32`; `w14:int32`]
   MD5_QUARTER7_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na24 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      let nb23 =
          word_add nc22
           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                               (word_add w4 (EL 23 md5_T)))
                     20) in
      let na24 =
          word_add nb23
           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                               (word_add w9 (EL 24 md5_T)))
                     5) in
      na24):int32`;
    (* b := nb27 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      let nb23 =
          word_add nc22
           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                               (word_add w4 (EL 23 md5_T)))
                     20) in
      let na24 =
          word_add nb23
           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                               (word_add w9 (EL 24 md5_T)))
                     5) in
      let nd25 =
          word_add na24
           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                               (word_add w14 (EL 25 md5_T)))
                     9) in
      let nc26 =
          word_add nd25
           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                               (word_add w3 (EL 26 md5_T)))
                     14) in
      let nb27 =
          word_add nc26
           (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                               (word_add w8 (EL 27 md5_T)))
                     20) in
      nb27):int32`;
    (* c := nc26 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      let nb23 =
          word_add nc22
           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                               (word_add w4 (EL 23 md5_T)))
                     20) in
      let na24 =
          word_add nb23
           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                               (word_add w9 (EL 24 md5_T)))
                     5) in
      let nd25 =
          word_add na24
           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                               (word_add w14 (EL 25 md5_T)))
                     9) in
      let nc26 =
          word_add nd25
           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                               (word_add w3 (EL 26 md5_T)))
                     14) in
      nc26):int32`;
    (* d := nd25 *)
    `(let na16 =
          word_add b
           (word_rol (word_add (word_add a (md5_G b c d))
                               (word_add w1 (EL 16 md5_T)))
                     5) in
      let nd17 =
          word_add na16
           (word_rol (word_add (word_add d (md5_G na16 b c))
                               (word_add w6 (EL 17 md5_T)))
                     9) in
      let nc18 =
          word_add nd17
           (word_rol (word_add (word_add c (md5_G nd17 na16 b))
                               (word_add w11 (EL 18 md5_T)))
                     14) in
      let nb19 =
          word_add nc18
           (word_rol (word_add (word_add b (md5_G nc18 nd17 na16))
                               (word_add w0 (EL 19 md5_T)))
                     20) in
      let na20 =
          word_add nb19
           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                               (word_add w5 (EL 20 md5_T)))
                     5) in
      let nd21 =
          word_add na20
           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                               (word_add w10 (EL 21 md5_T)))
                     9) in
      let nc22 =
          word_add nd21
           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                               (word_add w15 (EL 22 md5_T)))
                     14) in
      let nb23 =
          word_add nc22
           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                               (word_add w4 (EL 23 md5_T)))
                     20) in
      let na24 =
          word_add nb23
           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                               (word_add w9 (EL 24 md5_T)))
                     5) in
      let nd25 =
          word_add na24
           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                               (word_add w14 (EL 25 md5_T)))
                     9) in
      nd25):int32`;
    `w0:int32`; `w2:int32`; `w7:int32`; `w12:int32`; `w13:int32`]
   MD5_QUARTER8_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 — MD5_ROUND3_CORRECT: compose Q9..Q12 over [pc+1185, pc+1654).    *)
(* Cuts at pc+1308/1424/1539. R12 is NOT in the frame (round 3 H-encoding   *)
(* doesn't use the LEAL/AND/NOT idiom that round 1/2's G uses).              *)
(* ------------------------------------------------------------------------- *)

let MD5_ROUND3_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 1185) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read R10 s = word_zx w0 /\
                  read R11 s = word_zx (word_zx d:int32) /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 1654) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (let na32 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_H b c d))
                                                (word_add w5 (EL 32 md5_T)))
                                      4) in
                       let nd33 =
                           word_add na32
                            (word_rol (word_add (word_add d (md5_H na32 b c))
                                                (word_add w8 (EL 33 md5_T)))
                                      11) in
                       let nc34 =
                           word_add nd33
                            (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                                (word_add w11 (EL 34 md5_T)))
                                      16) in
                       let nb35 =
                           word_add nc34
                            (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                                (word_add w14 (EL 35 md5_T)))
                                      23) in
                       let na36 =
                           word_add nb35
                            (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                                (word_add w1 (EL 36 md5_T)))
                                      4) in
                       let nd37 =
                           word_add na36
                            (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                                (word_add w4 (EL 37 md5_T)))
                                      11) in
                       let nc38 =
                           word_add nd37
                            (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                                (word_add w7 (EL 38 md5_T)))
                                      16) in
                       let nb39 =
                           word_add nc38
                            (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                                (word_add w10 (EL 39 md5_T)))
                                      23) in
                       let na40 =
                           word_add nb39
                            (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                                (word_add w13 (EL 40 md5_T)))
                                      4) in
                       let nd41 =
                           word_add na40
                            (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                                (word_add w0 (EL 41 md5_T)))
                                      11) in
                       let nc42 =
                           word_add nd41
                            (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                                (word_add w3 (EL 42 md5_T)))
                                      16) in
                       let nb43 =
                           word_add nc42
                            (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                                (word_add w6 (EL 43 md5_T)))
                                      23) in
                       let na44 =
                           word_add nb43
                            (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                                (word_add w9 (EL 44 md5_T)))
                                      4) in
                       na44) /\
                  read RDX s =
                    word_zx
                      (let na32 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_H b c d))
                                                (word_add w5 (EL 32 md5_T)))
                                      4) in
                       let nd33 =
                           word_add na32
                            (word_rol (word_add (word_add d (md5_H na32 b c))
                                                (word_add w8 (EL 33 md5_T)))
                                      11) in
                       let nc34 =
                           word_add nd33
                            (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                                (word_add w11 (EL 34 md5_T)))
                                      16) in
                       let nb35 =
                           word_add nc34
                            (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                                (word_add w14 (EL 35 md5_T)))
                                      23) in
                       let na36 =
                           word_add nb35
                            (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                                (word_add w1 (EL 36 md5_T)))
                                      4) in
                       let nd37 =
                           word_add na36
                            (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                                (word_add w4 (EL 37 md5_T)))
                                      11) in
                       let nc38 =
                           word_add nd37
                            (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                                (word_add w7 (EL 38 md5_T)))
                                      16) in
                       let nb39 =
                           word_add nc38
                            (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                                (word_add w10 (EL 39 md5_T)))
                                      23) in
                       let na40 =
                           word_add nb39
                            (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                                (word_add w13 (EL 40 md5_T)))
                                      4) in
                       let nd41 =
                           word_add na40
                            (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                                (word_add w0 (EL 41 md5_T)))
                                      11) in
                       let nc42 =
                           word_add nd41
                            (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                                (word_add w3 (EL 42 md5_T)))
                                      16) in
                       let nb43 =
                           word_add nc42
                            (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                                (word_add w6 (EL 43 md5_T)))
                                      23) in
                       let na44 =
                           word_add nb43
                            (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                                (word_add w9 (EL 44 md5_T)))
                                      4) in
                       let nd45 =
                           word_add na44
                            (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42))
                                                (word_add w12 (EL 45 md5_T)))
                                      11) in
                       nd45) /\
                  read RCX s =
                    word_zx
                      (let na32 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_H b c d))
                                                (word_add w5 (EL 32 md5_T)))
                                      4) in
                       let nd33 =
                           word_add na32
                            (word_rol (word_add (word_add d (md5_H na32 b c))
                                                (word_add w8 (EL 33 md5_T)))
                                      11) in
                       let nc34 =
                           word_add nd33
                            (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                                (word_add w11 (EL 34 md5_T)))
                                      16) in
                       let nb35 =
                           word_add nc34
                            (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                                (word_add w14 (EL 35 md5_T)))
                                      23) in
                       let na36 =
                           word_add nb35
                            (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                                (word_add w1 (EL 36 md5_T)))
                                      4) in
                       let nd37 =
                           word_add na36
                            (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                                (word_add w4 (EL 37 md5_T)))
                                      11) in
                       let nc38 =
                           word_add nd37
                            (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                                (word_add w7 (EL 38 md5_T)))
                                      16) in
                       let nb39 =
                           word_add nc38
                            (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                                (word_add w10 (EL 39 md5_T)))
                                      23) in
                       let na40 =
                           word_add nb39
                            (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                                (word_add w13 (EL 40 md5_T)))
                                      4) in
                       let nd41 =
                           word_add na40
                            (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                                (word_add w0 (EL 41 md5_T)))
                                      11) in
                       let nc42 =
                           word_add nd41
                            (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                                (word_add w3 (EL 42 md5_T)))
                                      16) in
                       let nb43 =
                           word_add nc42
                            (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                                (word_add w6 (EL 43 md5_T)))
                                      23) in
                       let na44 =
                           word_add nb43
                            (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                                (word_add w9 (EL 44 md5_T)))
                                      4) in
                       let nd45 =
                           word_add na44
                            (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42))
                                                (word_add w12 (EL 45 md5_T)))
                                      11) in
                       let nc46 =
                           word_add nd45
                            (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43))
                                                (word_add w15 (EL 46 md5_T)))
                                      16) in
                       nc46) /\
                  read RBX s =
                    word_zx
                      (let na32 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_H b c d))
                                                (word_add w5 (EL 32 md5_T)))
                                      4) in
                       let nd33 =
                           word_add na32
                            (word_rol (word_add (word_add d (md5_H na32 b c))
                                                (word_add w8 (EL 33 md5_T)))
                                      11) in
                       let nc34 =
                           word_add nd33
                            (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                                (word_add w11 (EL 34 md5_T)))
                                      16) in
                       let nb35 =
                           word_add nc34
                            (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                                (word_add w14 (EL 35 md5_T)))
                                      23) in
                       let na36 =
                           word_add nb35
                            (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                                (word_add w1 (EL 36 md5_T)))
                                      4) in
                       let nd37 =
                           word_add na36
                            (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                                (word_add w4 (EL 37 md5_T)))
                                      11) in
                       let nc38 =
                           word_add nd37
                            (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                                (word_add w7 (EL 38 md5_T)))
                                      16) in
                       let nb39 =
                           word_add nc38
                            (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                                (word_add w10 (EL 39 md5_T)))
                                      23) in
                       let na40 =
                           word_add nb39
                            (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                                (word_add w13 (EL 40 md5_T)))
                                      4) in
                       let nd41 =
                           word_add na40
                            (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                                (word_add w0 (EL 41 md5_T)))
                                      11) in
                       let nc42 =
                           word_add nd41
                            (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                                (word_add w3 (EL 42 md5_T)))
                                      16) in
                       let nb43 =
                           word_add nc42
                            (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                                (word_add w6 (EL 43 md5_T)))
                                      23) in
                       let na44 =
                           word_add nb43
                            (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                                (word_add w9 (EL 44 md5_T)))
                                      4) in
                       let nd45 =
                           word_add na44
                            (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42))
                                                (word_add w12 (EL 45 md5_T)))
                                      11) in
                       let nc46 =
                           word_add nd45
                            (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43))
                                                (word_add w15 (EL 46 md5_T)))
                                      16) in
                       let nb47 =
                           word_add nc46
                            (word_rol (word_add (word_add nb43 (md5_H nc46 nd45 na44))
                                                (word_add w2 (EL 47 md5_T)))
                                      23) in
                       nb47) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = read RCX s)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
ENSURES_SEQUENCE_TAC `pc + 1308`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             na32) /\
        read RDX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             nd33) /\
        read RCX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             nc34) /\
        read RBX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             nb35) /\
        read R10 s = (word_zx:int32->int64) (w1:int32) /\
        read R11 s = read RCX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`;
    `w0:int32`; `w1:int32`; `w5:int32`; `w8:int32`; `w11:int32`; `w14:int32`]
   MD5_QUARTER9_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 1424`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             na36) /\
        read RDX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             nd37) /\
        read RCX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             nc38) /\
        read RBX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             let nb39 =
                 word_add nc38
                  (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                      (word_add w10 (EL 39 md5_T)))
                            23) in
             nb39) /\
        read R10 s = (word_zx:int32->int64) (w13:int32) /\
        read R11 s = read RCX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na32 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      na32):int32`;
    (* b := nb35 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      nb35):int32`;
    (* c := nc34 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      nc34):int32`;
    (* d := nd33 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      nd33):int32`;
    `w1:int32`; `w4:int32`; `w7:int32`; `w10:int32`; `w13:int32`]
   MD5_QUARTER10_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 1539`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             let nb39 =
                 word_add nc38
                  (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                      (word_add w10 (EL 39 md5_T)))
                            23) in
             let na40 =
                 word_add nb39
                  (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                      (word_add w13 (EL 40 md5_T)))
                            4) in
             na40) /\
        read RDX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             let nb39 =
                 word_add nc38
                  (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                      (word_add w10 (EL 39 md5_T)))
                            23) in
             let na40 =
                 word_add nb39
                  (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                      (word_add w13 (EL 40 md5_T)))
                            4) in
             let nd41 =
                 word_add na40
                  (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                      (word_add w0 (EL 41 md5_T)))
                            11) in
             nd41) /\
        read RCX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             let nb39 =
                 word_add nc38
                  (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                      (word_add w10 (EL 39 md5_T)))
                            23) in
             let na40 =
                 word_add nb39
                  (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                      (word_add w13 (EL 40 md5_T)))
                            4) in
             let nd41 =
                 word_add na40
                  (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                      (word_add w0 (EL 41 md5_T)))
                            11) in
             let nc42 =
                 word_add nd41
                  (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                      (word_add w3 (EL 42 md5_T)))
                            16) in
             nc42) /\
        read RBX s =
          word_zx
            (let na32 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_H b c d))
                                      (word_add w5 (EL 32 md5_T)))
                            4) in
             let nd33 =
                 word_add na32
                  (word_rol (word_add (word_add d (md5_H na32 b c))
                                      (word_add w8 (EL 33 md5_T)))
                            11) in
             let nc34 =
                 word_add nd33
                  (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                                      (word_add w11 (EL 34 md5_T)))
                            16) in
             let nb35 =
                 word_add nc34
                  (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                                      (word_add w14 (EL 35 md5_T)))
                            23) in
             let na36 =
                 word_add nb35
                  (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                      (word_add w1 (EL 36 md5_T)))
                            4) in
             let nd37 =
                 word_add na36
                  (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                      (word_add w4 (EL 37 md5_T)))
                            11) in
             let nc38 =
                 word_add nd37
                  (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                      (word_add w7 (EL 38 md5_T)))
                            16) in
             let nb39 =
                 word_add nc38
                  (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                      (word_add w10 (EL 39 md5_T)))
                            23) in
             let na40 =
                 word_add nb39
                  (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                      (word_add w13 (EL 40 md5_T)))
                            4) in
             let nd41 =
                 word_add na40
                  (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                      (word_add w0 (EL 41 md5_T)))
                            11) in
             let nc42 =
                 word_add nd41
                  (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                      (word_add w3 (EL 42 md5_T)))
                            16) in
             let nb43 =
                 word_add nc42
                  (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                      (word_add w6 (EL 43 md5_T)))
                            23) in
             nb43) /\
        read R10 s = (word_zx:int32->int64) (w9:int32) /\
        read R11 s = read RCX s /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na36 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      na36):int32`;
    (* b := nb39 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      let nb39 =
          word_add nc38
           (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                               (word_add w10 (EL 39 md5_T)))
                     23) in
      nb39):int32`;
    (* c := nc38 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      nc38):int32`;
    (* d := nd37 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      nd37):int32`;
    `w0:int32`; `w3:int32`; `w6:int32`; `w9:int32`; `w13:int32`]
   MD5_QUARTER11_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na40 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      let nb39 =
          word_add nc38
           (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                               (word_add w10 (EL 39 md5_T)))
                     23) in
      let na40 =
          word_add nb39
           (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                               (word_add w13 (EL 40 md5_T)))
                     4) in
      na40):int32`;
    (* b := nb43 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      let nb39 =
          word_add nc38
           (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                               (word_add w10 (EL 39 md5_T)))
                     23) in
      let na40 =
          word_add nb39
           (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                               (word_add w13 (EL 40 md5_T)))
                     4) in
      let nd41 =
          word_add na40
           (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                               (word_add w0 (EL 41 md5_T)))
                     11) in
      let nc42 =
          word_add nd41
           (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                               (word_add w3 (EL 42 md5_T)))
                     16) in
      let nb43 =
          word_add nc42
           (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                               (word_add w6 (EL 43 md5_T)))
                     23) in
      nb43):int32`;
    (* c := nc42 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      let nb39 =
          word_add nc38
           (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                               (word_add w10 (EL 39 md5_T)))
                     23) in
      let na40 =
          word_add nb39
           (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                               (word_add w13 (EL 40 md5_T)))
                     4) in
      let nd41 =
          word_add na40
           (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                               (word_add w0 (EL 41 md5_T)))
                     11) in
      let nc42 =
          word_add nd41
           (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                               (word_add w3 (EL 42 md5_T)))
                     16) in
      nc42):int32`;
    (* d := nd41 *)
    `(let na32 =
          word_add b
           (word_rol (word_add (word_add a (md5_H b c d))
                               (word_add w5 (EL 32 md5_T)))
                     4) in
      let nd33 =
          word_add na32
           (word_rol (word_add (word_add d (md5_H na32 b c))
                               (word_add w8 (EL 33 md5_T)))
                     11) in
      let nc34 =
          word_add nd33
           (word_rol (word_add (word_add c (md5_H nd33 na32 b))
                               (word_add w11 (EL 34 md5_T)))
                     16) in
      let nb35 =
          word_add nc34
           (word_rol (word_add (word_add b (md5_H nc34 nd33 na32))
                               (word_add w14 (EL 35 md5_T)))
                     23) in
      let na36 =
          word_add nb35
           (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                               (word_add w1 (EL 36 md5_T)))
                     4) in
      let nd37 =
          word_add na36
           (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                               (word_add w4 (EL 37 md5_T)))
                     11) in
      let nc38 =
          word_add nd37
           (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                               (word_add w7 (EL 38 md5_T)))
                     16) in
      let nb39 =
          word_add nc38
           (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                               (word_add w10 (EL 39 md5_T)))
                     23) in
      let na40 =
          word_add nb39
           (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                               (word_add w13 (EL 40 md5_T)))
                     4) in
      let nd41 =
          word_add na40
           (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                               (word_add w0 (EL 41 md5_T)))
                     11) in
      nd41):int32`;
    `w0:int32`; `w2:int32`; `w9:int32`; `w12:int32`; `w15:int32`]
   MD5_QUARTER12_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — Round 4 (I) quarter 13 (MD5 steps 48..51). 39 stepper steps,    *)
(* spanning [pc+1654, pc+1806). 5 more steps than the round-3 first-quarter  *)
(* Q9, owed to the 3-instruction round-3 -> round-4 boundary prelude         *)
(* (`movl 0(%rsi),%r10d; movl $0xffffffff,%r11d; xorl %edx,%r11d`) plus the  *)
(* round-4 idiom interleaving. The I encoding closes via a single inline     *)
(* WORD_BLAST bridge:                                                        *)
(*   word_xor (word_or (word_xor (word 4294967295) d) b) c                   *)
(*     = word_xor c (word_or b (word_not d)) = md5_I b c d.                  *)
(* The cascading-abbreviation template (Irol6/Irol10/Irol15) mirrors Q9's    *)
(* Hrol4/Hrol11/Hrol16. R11 post-condition encodes the Q14 step-prelude that *)
(* leaks into Q13's tail: `R11 = word_xor (word 4294967295) (read RDX s)`.    *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER13_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w0:int32) (w5:int32) (w7:int32) (w12:int32) (w14:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1654) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w0 /\
                   read R11 s = read RCX s /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                   read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                   read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                   read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14)
              (\s. read RIP s = word(pc + 1806) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_I b c d))
                                                  (word_add w0 (EL 48 md5_T)))
                                        6)) /\
                   read RDX s =
                     word_zx
                       (let na48 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w0 (EL 48 md5_T)))
                                       6) in
                        word_add na48
                         (word_rol (word_add (word_add d (md5_I na48 b c))
                                             (word_add w7 (EL 49 md5_T)))
                                   10)) /\
                   read RCX s =
                     word_zx
                       (let na48 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w0 (EL 48 md5_T)))
                                       6) in
                        let nd49 =
                            word_add na48
                             (word_rol (word_add (word_add d (md5_I na48 b c))
                                                 (word_add w7 (EL 49 md5_T)))
                                       10) in
                        word_add nd49
                         (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                             (word_add w14 (EL 50 md5_T)))
                                   15)) /\
                   read RBX s =
                     word_zx
                       (let na48 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w0 (EL 48 md5_T)))
                                       6) in
                        let nd49 =
                            word_add na48
                             (word_rol (word_add (word_add d (md5_I na48 b c))
                                                 (word_add w7 (EL 49 md5_T)))
                                       10) in
                        let nc50 =
                            word_add nd49
                             (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                                 (word_add w14 (EL 50 md5_T)))
                                       15) in
                        word_add nc50
                         (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                             (word_add w5 (EL 51 md5_T)))
                                   21)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w12 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_I] THEN
  CONJ_TAC THENL
   [(* RAX: step-48 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_or (word_xor (word 4294967295) (d:int32)) b) c =
      word_xor c (word_or b (word_not d))`
     SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-49 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4096336452))) x =
                      word_add (word_add a x) (word_add w (word 4096336452))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w0 (word 4096336452))) 6` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-50 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4096336452))) x =
                      word_add (word_add a x) (word_add w (word 4096336452))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w0 (word 4096336452))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w7 (word 1126891415))) x =
                    word_add (word_add d x) (word_add w7 (word 1126891415))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w7 (word 1126891415))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w14 (word 2878612391))) x =
                    word_add (word_add c x) (word_add w14 (word 2878612391))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RBX: step-51 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4096336452))) x =
                      word_add (word_add a x) (word_add w (word 4096336452))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w0 (word 4096336452))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w7 (word 1126891415))) x =
                    word_add (word_add d x) (word_add w7 (word 1126891415))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w7 (word 1126891415))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w14 (word 2878612391))) x =
                    word_add (word_add c x) (word_add w14 (word 2878612391))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol15:int32 = word_rol
                      (word_add (word_add (c:int32)
                                          (word_xor (word_add b Irol6)
                                                    (word_or
                                                       (word_add (word_add b Irol6)
                                                                 Irol10)
                                                       (word_not b))))
                                (word_add w14 (word 2878612391))) 15` THEN
    SUBGOAL_THEN
     `word_add Irol15 (word_add (word_add (b:int32) Irol6) Irol10) =
      word_add (word_add (word_add b Irol6) Irol10) Irol15`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(b:int32) x. word_add (word_add b (word_add w5 (word 4237533241))) x =
                    word_add (word_add b x) (word_add w5 (word 4237533241))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* R11: word_xor 0xffffffff applied to word_zx of step-49 result *)
  REWRITE_TAC[prove
    (`!(x:int32). word_zx (word_xor (word 4294967295) x:int32):int64 =
                  word_xor (word 4294967295) (word_zx x:int64)`,
     GEN_TAC THEN CONV_TAC WORD_BLAST)]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — Round 4 (I) quarter 14 (MD5 steps 52..55). 36 stepper steps,    *)
(* spanning [pc+1806, pc+1946). Mirrors Q13 mechanically but does not pay    *)
(* the round-3 -> round-4 boundary prelude, so 3 fewer steps than Q13.       *)
(* The trailing R10 reload is `movl 32(%rsi),%r10d` (w8 for Q15 step-56),    *)
(* and R11 is reset to `word_xor 0xffffffff (read RDX s)` in preparation for *)
(* Q15's first I-evaluation.                                                 *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER14_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w1:int32) (w3:int32) (w8:int32) (w10:int32) (w12:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1806) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w12 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s) /\
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                   read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                   read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                   read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                   read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12)
              (\s. read RIP s = word(pc + 1946) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_I b c d))
                                                  (word_add w12 (EL 52 md5_T)))
                                        6)) /\
                   read RDX s =
                     word_zx
                       (let na52 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w12 (EL 52 md5_T)))
                                       6) in
                        word_add na52
                         (word_rol (word_add (word_add d (md5_I na52 b c))
                                             (word_add w3 (EL 53 md5_T)))
                                   10)) /\
                   read RCX s =
                     word_zx
                       (let na52 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w12 (EL 52 md5_T)))
                                       6) in
                        let nd53 =
                            word_add na52
                             (word_rol (word_add (word_add d (md5_I na52 b c))
                                                 (word_add w3 (EL 53 md5_T)))
                                       10) in
                        word_add nd53
                         (word_rol (word_add (word_add c (md5_I nd53 na52 b))
                                             (word_add w10 (EL 54 md5_T)))
                                   15)) /\
                   read RBX s =
                     word_zx
                       (let na52 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w12 (EL 52 md5_T)))
                                       6) in
                        let nd53 =
                            word_add na52
                             (word_rol (word_add (word_add d (md5_I na52 b c))
                                                 (word_add w3 (EL 53 md5_T)))
                                       10) in
                        let nc54 =
                            word_add nd53
                             (word_rol (word_add (word_add c (md5_I nd53 na52 b))
                                                 (word_add w10 (EL 54 md5_T)))
                                       15) in
                        word_add nc54
                         (word_rol (word_add (word_add b (md5_I nc54 nd53 na52))
                                             (word_add w1 (EL 55 md5_T)))
                                   21)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w8 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_I] THEN
  SUBGOAL_THEN
   `!(d:int32).
        word_zx
           (word_xor (word 4294967295:int64) (word_zx d:int64)):int32 =
        word_xor (word 4294967295) d`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RAX: step-52 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_or (word_xor (word 4294967295) (d:int32)) b) c =
      word_xor c (word_or b (word_not d))`
     SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-53 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1700485571))) x =
                      word_add (word_add a x) (word_add w (word 1700485571))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w12 (word 1700485571))) 6` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-54 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1700485571))) x =
                      word_add (word_add a x) (word_add w (word 1700485571))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w12 (word 1700485571))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w3 (word 2399980690))) x =
                    word_add (word_add d x) (word_add w3 (word 2399980690))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w3 (word 2399980690))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w10 (word 4293915773))) x =
                    word_add (word_add c x) (word_add w10 (word 4293915773))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RBX: step-55 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1700485571))) x =
                      word_add (word_add a x) (word_add w (word 1700485571))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w12 (word 1700485571))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w3 (word 2399980690))) x =
                    word_add (word_add d x) (word_add w3 (word 2399980690))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w3 (word 2399980690))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w10 (word 4293915773))) x =
                    word_add (word_add c x) (word_add w10 (word 4293915773))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol15:int32 = word_rol
                      (word_add (word_add (c:int32)
                                          (word_xor (word_add b Irol6)
                                                    (word_or
                                                       (word_add (word_add b Irol6)
                                                                 Irol10)
                                                       (word_not b))))
                                (word_add w10 (word 4293915773))) 15` THEN
    SUBGOAL_THEN
     `word_add Irol15 (word_add (word_add (b:int32) Irol6) Irol10) =
      word_add (word_add (word_add b Irol6) Irol10) Irol15`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(b:int32) x. word_add (word_add b (word_add w1 (word 2240044497))) x =
                    word_add (word_add b x) (word_add w1 (word 2240044497))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* R11: word_xor 0xffffffff applied to word_zx of step-53 result *)
  REWRITE_TAC[prove
    (`!(x:int32). word_zx (word_xor (word 4294967295) x:int32):int64 =
                  word_xor (word 4294967295) (word_zx x:int64)`,
     GEN_TAC THEN CONV_TAC WORD_BLAST)]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — Round 4 (I) quarter 15 (MD5 steps 56..59). 36 stepper steps,    *)
(* spanning [pc+1946, pc+2086). Mirrors Q14 verbatim with substitutions:     *)
(* T constants T[56]=1873313359, T[57]=4264355552, T[58]=2734768916,         *)
(* T[59]=1309151649; message-word permutation K = [8;15;6;13]; rotations are *)
(* the round-4 cycle [6;10;15;21]. Trailing R10 reload is movl 16(%rsi),     *)
(* %r10d (w4 for Q16 step-60). R11 mid-step carry preserved on entry+exit.   *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER15_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w4:int32) (w6:int32) (w8:int32) (w13:int32) (w15:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 1946) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w8 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s) /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                   read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                   read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                   read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                   read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
              (\s. read RIP s = word(pc + 2086) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_I b c d))
                                                  (word_add w8 (EL 56 md5_T)))
                                        6)) /\
                   read RDX s =
                     word_zx
                       (let na56 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w8 (EL 56 md5_T)))
                                       6) in
                        word_add na56
                         (word_rol (word_add (word_add d (md5_I na56 b c))
                                             (word_add w15 (EL 57 md5_T)))
                                   10)) /\
                   read RCX s =
                     word_zx
                       (let na56 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w8 (EL 56 md5_T)))
                                       6) in
                        let nd57 =
                            word_add na56
                             (word_rol (word_add (word_add d (md5_I na56 b c))
                                                 (word_add w15 (EL 57 md5_T)))
                                       10) in
                        word_add nd57
                         (word_rol (word_add (word_add c (md5_I nd57 na56 b))
                                             (word_add w6 (EL 58 md5_T)))
                                   15)) /\
                   read RBX s =
                     word_zx
                       (let na56 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w8 (EL 56 md5_T)))
                                       6) in
                        let nd57 =
                            word_add na56
                             (word_rol (word_add (word_add d (md5_I na56 b c))
                                                 (word_add w15 (EL 57 md5_T)))
                                       10) in
                        let nc58 =
                            word_add nd57
                             (word_rol (word_add (word_add c (md5_I nd57 na56 b))
                                                 (word_add w6 (EL 58 md5_T)))
                                       15) in
                        word_add nc58
                         (word_rol (word_add (word_add b (md5_I nc58 nd57 na56))
                                             (word_add w13 (EL 59 md5_T)))
                                   21)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w4 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_I] THEN
  SUBGOAL_THEN
   `!(d:int32).
        word_zx
           (word_xor (word 4294967295:int64) (word_zx d:int64)):int32 =
        word_xor (word 4294967295) d`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RAX: step-56 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_or (word_xor (word 4294967295) (d:int32)) b) c =
      word_xor c (word_or b (word_not d))`
     SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-57 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1873313359))) x =
                      word_add (word_add a x) (word_add w (word 1873313359))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w8 (word 1873313359))) 6` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-58 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1873313359))) x =
                      word_add (word_add a x) (word_add w (word 1873313359))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w8 (word 1873313359))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w15 (word 4264355552))) x =
                    word_add (word_add d x) (word_add w15 (word 4264355552))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w15 (word 4264355552))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w6 (word 2734768916))) x =
                    word_add (word_add c x) (word_add w6 (word 2734768916))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RBX: step-59 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 1873313359))) x =
                      word_add (word_add a x) (word_add w (word 1873313359))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w8 (word 1873313359))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w15 (word 4264355552))) x =
                    word_add (word_add d x) (word_add w15 (word 4264355552))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w15 (word 4264355552))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w6 (word 2734768916))) x =
                    word_add (word_add c x) (word_add w6 (word 2734768916))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol15:int32 = word_rol
                      (word_add (word_add (c:int32)
                                          (word_xor (word_add b Irol6)
                                                    (word_or
                                                       (word_add (word_add b Irol6)
                                                                 Irol10)
                                                       (word_not b))))
                                (word_add w6 (word 2734768916))) 15` THEN
    SUBGOAL_THEN
     `word_add Irol15 (word_add (word_add (b:int32) Irol6) Irol10) =
      word_add (word_add (word_add b Irol6) Irol10) Irol15`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(b:int32) x. word_add (word_add b (word_add w13 (word 1309151649))) x =
                    word_add (word_add b x) (word_add w13 (word 1309151649))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* R11: word_xor 0xffffffff applied to word_zx of step-57 result *)
  REWRITE_TAC[prove
    (`!(x:int32). word_zx (word_xor (word 4294967295) x:int32):int64 =
                  word_xor (word 4294967295) (word_zx x:int64)`,
     GEN_TAC THEN CONV_TAC WORD_BLAST)]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 — Round 4 (I) quarter 16 (MD5 steps 60..63). 36 stepper steps,    *)
(* spanning [pc+2086, pc+2225). Mirrors Q15 verbatim with substitutions:     *)
(* T constants T[60]=4149444226, T[61]=3174756917, T[62]=718787259,          *)
(* T[63]=3951481745; message-word permutation K = [4;11;2;9]; rotations are  *)
(* the round-4 cycle [6;10;15;21]. Trailing R10 reload is movl 0(%rsi),      *)
(* %r10d (w0 for the writeback prelude). R11 mid-step carry preserved on    *)
(* entry+exit (the asm template still emits the "neg-d" idiom even though    *)
(* there is no following round-4 step).                                      *)
(* ------------------------------------------------------------------------- *)

let MD5_QUARTER16_CORRECT = prove
 (`!pc (data_ptr:int64) (a:int32) (b:int32) (c:int32) (d:int32)
   (w0:int32) (w2:int32) (w4:int32) (w9:int32) (w11:int32).
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 2086) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w4 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s) /\
                   read (memory :> bytes32 data_ptr) s = w0 /\
                   read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                   read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                   read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11)
              (\s. read RIP s = word(pc + 2225) /\
                   read RAX s =
                     word_zx (word_add b
                              (word_rol (word_add (word_add a (md5_I b c d))
                                                  (word_add w4 (EL 60 md5_T)))
                                        6)) /\
                   read RDX s =
                     word_zx
                       (let na60 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w4 (EL 60 md5_T)))
                                       6) in
                        word_add na60
                         (word_rol (word_add (word_add d (md5_I na60 b c))
                                             (word_add w11 (EL 61 md5_T)))
                                   10)) /\
                   read RCX s =
                     word_zx
                       (let na60 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w4 (EL 60 md5_T)))
                                       6) in
                        let nd61 =
                            word_add na60
                             (word_rol (word_add (word_add d (md5_I na60 b c))
                                                 (word_add w11 (EL 61 md5_T)))
                                       10) in
                        word_add nd61
                         (word_rol (word_add (word_add c (md5_I nd61 na60 b))
                                             (word_add w2 (EL 62 md5_T)))
                                   15)) /\
                   read RBX s =
                     word_zx
                       (let na60 =
                            word_add b
                             (word_rol (word_add (word_add a (md5_I b c d))
                                                 (word_add w4 (EL 60 md5_T)))
                                       6) in
                        let nd61 =
                            word_add na60
                             (word_rol (word_add (word_add d (md5_I na60 b c))
                                                 (word_add w11 (EL 61 md5_T)))
                                       10) in
                        let nc62 =
                            word_add nd61
                             (word_rol (word_add (word_add c (md5_I nd61 na60 b))
                                                 (word_add w2 (EL 62 md5_T)))
                                       15) in
                        word_add nc62
                         (word_rol (word_add (word_add b (md5_I nc62 nd61 na60))
                                             (word_add w9 (EL 63 md5_T)))
                                   21)) /\
                   read RSI s = data_ptr /\
                   read R10 s = word_zx w0 /\
                   read R11 s = word_xor (word 4294967295) (read RDX s))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`;
           LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[LET_DEF; LET_END_DEF])) THEN
  REWRITE_TAC[md5_I] THEN
  SUBGOAL_THEN
   `!(d:int32).
        word_zx
           (word_xor (word 4294967295:int64) (word_zx d:int64)):int32 =
        word_xor (word 4294967295) d`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RAX: step-60 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `word_xor (word_or (word_xor (word 4294967295) (d:int32)) b) c =
      word_xor c (word_or b (word_not d))`
     SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RDX: step-61 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4149444226))) x =
                      word_add (word_add a x) (word_add w (word 4149444226))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w4 (word 4149444226))) 6` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RCX: step-62 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4149444226))) x =
                      word_add (word_add a x) (word_add w (word 4149444226))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w4 (word 4149444226))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w11 (word 3174756917))) x =
                    word_add (word_add d x) (word_add w11 (word 3174756917))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w11 (word 3174756917))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w2 (word 718787259))) x =
                    word_add (word_add c x) (word_add w2 (word 718787259))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* RBX: step-63 result *)
    REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `!(b:int32) c d. word_xor (word_or (word_xor (word 4294967295) d) b) c =
                      word_xor c (word_or b (word_not d))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(a:int32) w x. word_add (word_add a (word_add w (word 4149444226))) x =
                      word_add (word_add a x) (word_add w (word 4149444226))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol6:int32 = word_rol
                     (word_add (word_add (a:int32)
                                         (word_xor c (word_or b (word_not d))))
                               (word_add w4 (word 4149444226))) 6` THEN
    SUBGOAL_THEN `word_add Irol6 (b:int32) = word_add b Irol6`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(d:int32) x. word_add (word_add d (word_add w11 (word 3174756917))) x =
                    word_add (word_add d x) (word_add w11 (word 3174756917))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol10:int32 = word_rol
                      (word_add (word_add (d:int32)
                                          (word_xor b
                                                    (word_or (word_add b Irol6)
                                                             (word_not c))))
                                (word_add w11 (word 3174756917))) 10` THEN
    SUBGOAL_THEN `word_add Irol10 (word_add (b:int32) Irol6) =
                  word_add (word_add b Irol6) Irol10`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(c:int32) x. word_add (word_add c (word_add w2 (word 718787259))) x =
                    word_add (word_add c x) (word_add w2 (word 718787259))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ABBREV_TAC
     `Irol15:int32 = word_rol
                      (word_add (word_add (c:int32)
                                          (word_xor (word_add b Irol6)
                                                    (word_or
                                                       (word_add (word_add b Irol6)
                                                                 Irol10)
                                                       (word_not b))))
                                (word_add w2 (word 718787259))) 15` THEN
    SUBGOAL_THEN
     `word_add Irol15 (word_add (word_add (b:int32) Irol6) Irol10) =
      word_add (word_add (word_add b Irol6) Irol10) Irol15`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
     `!(b:int32) x. word_add (word_add b (word_add w9 (word 3951481745))) x =
                    word_add (word_add b x) (word_add w9 (word 3951481745))`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  (* R11: word_xor 0xffffffff applied to word_zx of step-61 result *)
  REWRITE_TAC[prove
    (`!(x:int32). word_zx (word_xor (word 4294967295) x:int32):int64 =
                  word_xor (word 4294967295) (word_zx x:int64)`,
     GEN_TAC THEN CONV_TAC WORD_BLAST)]);;


(* ------------------------------------------------------------------------- *)
(* Phase 8 — MD5_ROUND4_CORRECT: compose Q13..Q16 over [pc+1654, pc+2225).  *)
(* Cuts at pc+1806/1946/2086. R12 is NOT in the frame (round 4 I-encoding   *)
(* doesn't use the LEAL/AND/NOT idiom that round 1/2's G uses).              *)
(* R11 carries the round-4 mid-step shape word_xor 0xffffffff (read RDX).   *)
(* ------------------------------------------------------------------------- *)

let MD5_ROUND4_CORRECT = prove
 (`!pc data_ptr a b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15:int32.
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 1654) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read R10 s = word_zx w0 /\
                  read R11 s = read RCX s /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 2225) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (let na48 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_I b c d))
                                                (word_add w0 (EL 48 md5_T)))
                                      6) in
                       let nd49 =
                           word_add na48
                            (word_rol (word_add (word_add d (md5_I na48 b c))
                                                (word_add w7 (EL 49 md5_T)))
                                      10) in
                       let nc50 =
                           word_add nd49
                            (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                                (word_add w14 (EL 50 md5_T)))
                                      15) in
                       let nb51 =
                           word_add nc50
                            (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                                (word_add w5 (EL 51 md5_T)))
                                      21) in
                       let na52 =
                           word_add nb51
                            (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                                (word_add w12 (EL 52 md5_T)))
                                      6) in
                       let nd53 =
                           word_add na52
                            (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                                (word_add w3 (EL 53 md5_T)))
                                      10) in
                       let nc54 =
                           word_add nd53
                            (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                                (word_add w10 (EL 54 md5_T)))
                                      15) in
                       let nb55 =
                           word_add nc54
                            (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                                (word_add w1 (EL 55 md5_T)))
                                      21) in
                       let na56 =
                           word_add nb55
                            (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                                (word_add w8 (EL 56 md5_T)))
                                      6) in
                       let nd57 =
                           word_add na56
                            (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                                (word_add w15 (EL 57 md5_T)))
                                      10) in
                       let nc58 =
                           word_add nd57
                            (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                                (word_add w6 (EL 58 md5_T)))
                                      15) in
                       let nb59 =
                           word_add nc58
                            (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                                (word_add w13 (EL 59 md5_T)))
                                      21) in
                       let na60 =
                           word_add nb59
                            (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57))
                                                (word_add w4 (EL 60 md5_T)))
                                      6) in
                       na60) /\
                  read RDX s =
                    word_zx
                      (let na48 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_I b c d))
                                                (word_add w0 (EL 48 md5_T)))
                                      6) in
                       let nd49 =
                           word_add na48
                            (word_rol (word_add (word_add d (md5_I na48 b c))
                                                (word_add w7 (EL 49 md5_T)))
                                      10) in
                       let nc50 =
                           word_add nd49
                            (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                                (word_add w14 (EL 50 md5_T)))
                                      15) in
                       let nb51 =
                           word_add nc50
                            (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                                (word_add w5 (EL 51 md5_T)))
                                      21) in
                       let na52 =
                           word_add nb51
                            (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                                (word_add w12 (EL 52 md5_T)))
                                      6) in
                       let nd53 =
                           word_add na52
                            (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                                (word_add w3 (EL 53 md5_T)))
                                      10) in
                       let nc54 =
                           word_add nd53
                            (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                                (word_add w10 (EL 54 md5_T)))
                                      15) in
                       let nb55 =
                           word_add nc54
                            (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                                (word_add w1 (EL 55 md5_T)))
                                      21) in
                       let na56 =
                           word_add nb55
                            (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                                (word_add w8 (EL 56 md5_T)))
                                      6) in
                       let nd57 =
                           word_add na56
                            (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                                (word_add w15 (EL 57 md5_T)))
                                      10) in
                       let nc58 =
                           word_add nd57
                            (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                                (word_add w6 (EL 58 md5_T)))
                                      15) in
                       let nb59 =
                           word_add nc58
                            (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                                (word_add w13 (EL 59 md5_T)))
                                      21) in
                       let na60 =
                           word_add nb59
                            (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57))
                                                (word_add w4 (EL 60 md5_T)))
                                      6) in
                       let nd61 =
                           word_add na60
                            (word_rol (word_add (word_add nd57 (md5_I na60 nb59 nc58))
                                                (word_add w11 (EL 61 md5_T)))
                                      10) in
                       nd61) /\
                  read RCX s =
                    word_zx
                      (let na48 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_I b c d))
                                                (word_add w0 (EL 48 md5_T)))
                                      6) in
                       let nd49 =
                           word_add na48
                            (word_rol (word_add (word_add d (md5_I na48 b c))
                                                (word_add w7 (EL 49 md5_T)))
                                      10) in
                       let nc50 =
                           word_add nd49
                            (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                                (word_add w14 (EL 50 md5_T)))
                                      15) in
                       let nb51 =
                           word_add nc50
                            (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                                (word_add w5 (EL 51 md5_T)))
                                      21) in
                       let na52 =
                           word_add nb51
                            (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                                (word_add w12 (EL 52 md5_T)))
                                      6) in
                       let nd53 =
                           word_add na52
                            (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                                (word_add w3 (EL 53 md5_T)))
                                      10) in
                       let nc54 =
                           word_add nd53
                            (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                                (word_add w10 (EL 54 md5_T)))
                                      15) in
                       let nb55 =
                           word_add nc54
                            (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                                (word_add w1 (EL 55 md5_T)))
                                      21) in
                       let na56 =
                           word_add nb55
                            (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                                (word_add w8 (EL 56 md5_T)))
                                      6) in
                       let nd57 =
                           word_add na56
                            (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                                (word_add w15 (EL 57 md5_T)))
                                      10) in
                       let nc58 =
                           word_add nd57
                            (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                                (word_add w6 (EL 58 md5_T)))
                                      15) in
                       let nb59 =
                           word_add nc58
                            (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                                (word_add w13 (EL 59 md5_T)))
                                      21) in
                       let na60 =
                           word_add nb59
                            (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57))
                                                (word_add w4 (EL 60 md5_T)))
                                      6) in
                       let nd61 =
                           word_add na60
                            (word_rol (word_add (word_add nd57 (md5_I na60 nb59 nc58))
                                                (word_add w11 (EL 61 md5_T)))
                                      10) in
                       let nc62 =
                           word_add nd61
                            (word_rol (word_add (word_add nc58 (md5_I nd61 na60 nb59))
                                                (word_add w2 (EL 62 md5_T)))
                                      15) in
                       nc62) /\
                  read RBX s =
                    word_zx
                      (let na48 =
                           word_add b
                            (word_rol (word_add (word_add a (md5_I b c d))
                                                (word_add w0 (EL 48 md5_T)))
                                      6) in
                       let nd49 =
                           word_add na48
                            (word_rol (word_add (word_add d (md5_I na48 b c))
                                                (word_add w7 (EL 49 md5_T)))
                                      10) in
                       let nc50 =
                           word_add nd49
                            (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                                (word_add w14 (EL 50 md5_T)))
                                      15) in
                       let nb51 =
                           word_add nc50
                            (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                                (word_add w5 (EL 51 md5_T)))
                                      21) in
                       let na52 =
                           word_add nb51
                            (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                                (word_add w12 (EL 52 md5_T)))
                                      6) in
                       let nd53 =
                           word_add na52
                            (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                                (word_add w3 (EL 53 md5_T)))
                                      10) in
                       let nc54 =
                           word_add nd53
                            (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                                (word_add w10 (EL 54 md5_T)))
                                      15) in
                       let nb55 =
                           word_add nc54
                            (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                                (word_add w1 (EL 55 md5_T)))
                                      21) in
                       let na56 =
                           word_add nb55
                            (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                                (word_add w8 (EL 56 md5_T)))
                                      6) in
                       let nd57 =
                           word_add na56
                            (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                                (word_add w15 (EL 57 md5_T)))
                                      10) in
                       let nc58 =
                           word_add nd57
                            (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                                (word_add w6 (EL 58 md5_T)))
                                      15) in
                       let nb59 =
                           word_add nc58
                            (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                                (word_add w13 (EL 59 md5_T)))
                                      21) in
                       let na60 =
                           word_add nb59
                            (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57))
                                                (word_add w4 (EL 60 md5_T)))
                                      6) in
                       let nd61 =
                           word_add na60
                            (word_rol (word_add (word_add nd57 (md5_I na60 nb59 nc58))
                                                (word_add w11 (EL 61 md5_T)))
                                      10) in
                       let nc62 =
                           word_add nd61
                            (word_rol (word_add (word_add nc58 (md5_I nd61 na60 nb59))
                                                (word_add w2 (EL 62 md5_T)))
                                      15) in
                       let nb63 =
                           word_add nc62
                            (word_rol (word_add (word_add nb59 (md5_I nc62 nd61 na60))
                                                (word_add w9 (EL 63 md5_T)))
                                      21) in
                       nb63) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = word_xor (word 4294967295) (read RDX s))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R10; R11] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
ENSURES_SEQUENCE_TAC `pc + 1806`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             na48) /\
        read RDX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             nd49) /\
        read RCX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             nc50) /\
        read RBX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             nb51) /\
        read R10 s = (word_zx:int32->int64) (w12:int32) /\
        read R11 s = word_xor (word 4294967295) (read RDX s) /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`;
    `w0:int32`; `w5:int32`; `w7:int32`; `w12:int32`; `w14:int32`]
   MD5_QUARTER13_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 1946`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             na52) /\
        read RDX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             nd53) /\
        read RCX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             nc54) /\
        read RBX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             let nb55 =
                 word_add nc54
                  (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                      (word_add w1 (EL 55 md5_T)))
                            21) in
             nb55) /\
        read R10 s = (word_zx:int32->int64) (w8:int32) /\
        read R11 s = word_xor (word 4294967295) (read RDX s) /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na48 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      na48):int32`;
    (* b := nb51 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      nb51):int32`;
    (* c := nc50 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      nc50):int32`;
    (* d := nd49 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      nd49):int32`;
    `w1:int32`; `w3:int32`; `w8:int32`; `w10:int32`; `w12:int32`]
   MD5_QUARTER14_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
ENSURES_SEQUENCE_TAC `pc + 2086`
   `\s. read RSI s = data_ptr /\
        read RAX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             let nb55 =
                 word_add nc54
                  (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                      (word_add w1 (EL 55 md5_T)))
                            21) in
             let na56 =
                 word_add nb55
                  (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                      (word_add w8 (EL 56 md5_T)))
                            6) in
             na56) /\
        read RDX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             let nb55 =
                 word_add nc54
                  (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                      (word_add w1 (EL 55 md5_T)))
                            21) in
             let na56 =
                 word_add nb55
                  (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                      (word_add w8 (EL 56 md5_T)))
                            6) in
             let nd57 =
                 word_add na56
                  (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                      (word_add w15 (EL 57 md5_T)))
                            10) in
             nd57) /\
        read RCX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             let nb55 =
                 word_add nc54
                  (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                      (word_add w1 (EL 55 md5_T)))
                            21) in
             let na56 =
                 word_add nb55
                  (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                      (word_add w8 (EL 56 md5_T)))
                            6) in
             let nd57 =
                 word_add na56
                  (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                      (word_add w15 (EL 57 md5_T)))
                            10) in
             let nc58 =
                 word_add nd57
                  (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                      (word_add w6 (EL 58 md5_T)))
                            15) in
             nc58) /\
        read RBX s =
          word_zx
            (let na48 =
                 word_add b
                  (word_rol (word_add (word_add a (md5_I b c d))
                                      (word_add w0 (EL 48 md5_T)))
                            6) in
             let nd49 =
                 word_add na48
                  (word_rol (word_add (word_add d (md5_I na48 b c))
                                      (word_add w7 (EL 49 md5_T)))
                            10) in
             let nc50 =
                 word_add nd49
                  (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                                      (word_add w14 (EL 50 md5_T)))
                            15) in
             let nb51 =
                 word_add nc50
                  (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                                      (word_add w5 (EL 51 md5_T)))
                            21) in
             let na52 =
                 word_add nb51
                  (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                      (word_add w12 (EL 52 md5_T)))
                            6) in
             let nd53 =
                 word_add na52
                  (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                      (word_add w3 (EL 53 md5_T)))
                            10) in
             let nc54 =
                 word_add nd53
                  (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                      (word_add w10 (EL 54 md5_T)))
                            15) in
             let nb55 =
                 word_add nc54
                  (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                      (word_add w1 (EL 55 md5_T)))
                            21) in
             let na56 =
                 word_add nb55
                  (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                      (word_add w8 (EL 56 md5_T)))
                            6) in
             let nd57 =
                 word_add na56
                  (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                      (word_add w15 (EL 57 md5_T)))
                            10) in
             let nc58 =
                 word_add nd57
                  (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                      (word_add w6 (EL 58 md5_T)))
                            15) in
             let nb59 =
                 word_add nc58
                  (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                      (word_add w13 (EL 59 md5_T)))
                            21) in
             nb59) /\
        read R10 s = (word_zx:int32->int64) (w4:int32) /\
        read R11 s = word_xor (word 4294967295) (read RDX s) /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na52 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      na52):int32`;
    (* b := nb55 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      let nb55 =
          word_add nc54
           (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                               (word_add w1 (EL 55 md5_T)))
                     21) in
      nb55):int32`;
    (* c := nc54 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      nc54):int32`;
    (* d := nd53 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      nd53):int32`;
    `w4:int32`; `w6:int32`; `w8:int32`; `w13:int32`; `w15:int32`]
   MD5_QUARTER15_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    (* a := na56 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      let nb55 =
          word_add nc54
           (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                               (word_add w1 (EL 55 md5_T)))
                     21) in
      let na56 =
          word_add nb55
           (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                               (word_add w8 (EL 56 md5_T)))
                     6) in
      na56):int32`;
    (* b := nb59 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      let nb55 =
          word_add nc54
           (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                               (word_add w1 (EL 55 md5_T)))
                     21) in
      let na56 =
          word_add nb55
           (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                               (word_add w8 (EL 56 md5_T)))
                     6) in
      let nd57 =
          word_add na56
           (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                               (word_add w15 (EL 57 md5_T)))
                     10) in
      let nc58 =
          word_add nd57
           (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                               (word_add w6 (EL 58 md5_T)))
                     15) in
      let nb59 =
          word_add nc58
           (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                               (word_add w13 (EL 59 md5_T)))
                     21) in
      nb59):int32`;
    (* c := nc58 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      let nb55 =
          word_add nc54
           (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                               (word_add w1 (EL 55 md5_T)))
                     21) in
      let na56 =
          word_add nb55
           (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                               (word_add w8 (EL 56 md5_T)))
                     6) in
      let nd57 =
          word_add na56
           (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                               (word_add w15 (EL 57 md5_T)))
                     10) in
      let nc58 =
          word_add nd57
           (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                               (word_add w6 (EL 58 md5_T)))
                     15) in
      nc58):int32`;
    (* d := nd57 *)
    `(let na48 =
          word_add b
           (word_rol (word_add (word_add a (md5_I b c d))
                               (word_add w0 (EL 48 md5_T)))
                     6) in
      let nd49 =
          word_add na48
           (word_rol (word_add (word_add d (md5_I na48 b c))
                               (word_add w7 (EL 49 md5_T)))
                     10) in
      let nc50 =
          word_add nd49
           (word_rol (word_add (word_add c (md5_I nd49 na48 b))
                               (word_add w14 (EL 50 md5_T)))
                     15) in
      let nb51 =
          word_add nc50
           (word_rol (word_add (word_add b (md5_I nc50 nd49 na48))
                               (word_add w5 (EL 51 md5_T)))
                     21) in
      let na52 =
          word_add nb51
           (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                               (word_add w12 (EL 52 md5_T)))
                     6) in
      let nd53 =
          word_add na52
           (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                               (word_add w3 (EL 53 md5_T)))
                     10) in
      let nc54 =
          word_add nd53
           (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                               (word_add w10 (EL 54 md5_T)))
                     15) in
      let nb55 =
          word_add nc54
           (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                               (word_add w1 (EL 55 md5_T)))
                     21) in
      let na56 =
          word_add nb55
           (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                               (word_add w8 (EL 56 md5_T)))
                     6) in
      let nd57 =
          word_add na56
           (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                               (word_add w15 (EL 57 md5_T)))
                     10) in
      nd57):int32`;
    `w0:int32`; `w2:int32`; `w4:int32`; `w9:int32`; `w11:int32`]
   MD5_QUARTER16_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]]]);;
(* ------------------------------------------------------------------------- *)
(* Spec-form retrofit: md5_compress 64 W [a;b;c;d] = [na60;nb63;nc62;nd61].   *)
(*                                                                            *)
(* Single 64-step retrofit lemma, modeled on MD5_COMPRESS_4_F_VALUES (line    *)
(* 1030). Each per-step na/nd/nc/nb is bound to its standard MD5 update.     *)
(* The conclusion gives the cyclic rotation result after 64 rounds.          *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_64_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        na0 nd1 nc2 nb3 na4 nd5 nc6 nb7
        na8 nd9 nc10 nb11 na12 nd13 nc14 nb15
        na16 nd17 nc18 nb19 na20 nd21 nc22 nb23
        na24 nd25 nc26 nb27 na28 nd29 nc30 nb31
        na32 nd33 nc34 nb35 na36 nd37 nc38 nb39
        na40 nd41 nc42 nb43 na44 nd45 nc46 nb47
        na48 nd49 nc50 nb51 na52 nd53 nc54 nb55
        na56 nd57 nc58 nb59 na60 nd61 nc62 nb63.
        LENGTH W = 16 /\
        w0 = EL 0 W /\
        w1 = EL 1 W /\
        w2 = EL 2 W /\
        w3 = EL 3 W /\
        w4 = EL 4 W /\
        w5 = EL 5 W /\
        w6 = EL 6 W /\
        w7 = EL 7 W /\
        w8 = EL 8 W /\
        w9 = EL 9 W /\
        w10 = EL 10 W /\
        w11 = EL 11 W /\
        w12 = EL 12 W /\
        w13 = EL 13 W /\
        w14 = EL 14 W /\
        w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T)))
                         7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T)))
                         12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T)))
                         17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T)))
                         22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T)))
                         7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T)))
                         12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T)))
                         17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T)))
                         22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T)))
                         7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T)))
                         12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T)))
                         17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T)))
                         22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T)))
                         7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T)))
                         12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T)))
                         17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T)))
                         22) /\
        na16 = word_add nb15
               (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13))
                                   (word_add w1 (EL 16 md5_T)))
                         5) /\
        nd17 = word_add na16
               (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14))
                                   (word_add w6 (EL 17 md5_T)))
                         9) /\
        nc18 = word_add nd17
               (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15))
                                   (word_add w11 (EL 18 md5_T)))
                         14) /\
        nb19 = word_add nc18
               (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16))
                                   (word_add w0 (EL 19 md5_T)))
                         20) /\
        na20 = word_add nb19
               (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                   (word_add w5 (EL 20 md5_T)))
                         5) /\
        nd21 = word_add na20
               (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                   (word_add w10 (EL 21 md5_T)))
                         9) /\
        nc22 = word_add nd21
               (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                   (word_add w15 (EL 22 md5_T)))
                         14) /\
        nb23 = word_add nc22
               (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                   (word_add w4 (EL 23 md5_T)))
                         20) /\
        na24 = word_add nb23
               (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                   (word_add w9 (EL 24 md5_T)))
                         5) /\
        nd25 = word_add na24
               (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                   (word_add w14 (EL 25 md5_T)))
                         9) /\
        nc26 = word_add nd25
               (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                   (word_add w3 (EL 26 md5_T)))
                         14) /\
        nb27 = word_add nc26
               (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                   (word_add w8 (EL 27 md5_T)))
                         20) /\
        na28 = word_add nb27
               (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                   (word_add w13 (EL 28 md5_T)))
                         5) /\
        nd29 = word_add na28
               (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                   (word_add w2 (EL 29 md5_T)))
                         9) /\
        nc30 = word_add nd29
               (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                   (word_add w7 (EL 30 md5_T)))
                         14) /\
        nb31 = word_add nc30
               (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                   (word_add w12 (EL 31 md5_T)))
                         20) /\
        na32 = word_add nb31
               (word_rol (word_add (word_add na28 (md5_H nb31 nc30 nd29))
                                   (word_add w5 (EL 32 md5_T)))
                         4) /\
        nd33 = word_add na32
               (word_rol (word_add (word_add nd29 (md5_H na32 nb31 nc30))
                                   (word_add w8 (EL 33 md5_T)))
                         11) /\
        nc34 = word_add nd33
               (word_rol (word_add (word_add nc30 (md5_H nd33 na32 nb31))
                                   (word_add w11 (EL 34 md5_T)))
                         16) /\
        nb35 = word_add nc34
               (word_rol (word_add (word_add nb31 (md5_H nc34 nd33 na32))
                                   (word_add w14 (EL 35 md5_T)))
                         23) /\
        na36 = word_add nb35
               (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                   (word_add w1 (EL 36 md5_T)))
                         4) /\
        nd37 = word_add na36
               (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                   (word_add w4 (EL 37 md5_T)))
                         11) /\
        nc38 = word_add nd37
               (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                   (word_add w7 (EL 38 md5_T)))
                         16) /\
        nb39 = word_add nc38
               (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                   (word_add w10 (EL 39 md5_T)))
                         23) /\
        na40 = word_add nb39
               (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                   (word_add w13 (EL 40 md5_T)))
                         4) /\
        nd41 = word_add na40
               (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                   (word_add w0 (EL 41 md5_T)))
                         11) /\
        nc42 = word_add nd41
               (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                   (word_add w3 (EL 42 md5_T)))
                         16) /\
        nb43 = word_add nc42
               (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                   (word_add w6 (EL 43 md5_T)))
                         23) /\
        na44 = word_add nb43
               (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                   (word_add w9 (EL 44 md5_T)))
                         4) /\
        nd45 = word_add na44
               (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42))
                                   (word_add w12 (EL 45 md5_T)))
                         11) /\
        nc46 = word_add nd45
               (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43))
                                   (word_add w15 (EL 46 md5_T)))
                         16) /\
        nb47 = word_add nc46
               (word_rol (word_add (word_add nb43 (md5_H nc46 nd45 na44))
                                   (word_add w2 (EL 47 md5_T)))
                         23) /\
        na48 = word_add nb47
               (word_rol (word_add (word_add na44 (md5_I nb47 nc46 nd45))
                                   (word_add w0 (EL 48 md5_T)))
                         6) /\
        nd49 = word_add na48
               (word_rol (word_add (word_add nd45 (md5_I na48 nb47 nc46))
                                   (word_add w7 (EL 49 md5_T)))
                         10) /\
        nc50 = word_add nd49
               (word_rol (word_add (word_add nc46 (md5_I nd49 na48 nb47))
                                   (word_add w14 (EL 50 md5_T)))
                         15) /\
        nb51 = word_add nc50
               (word_rol (word_add (word_add nb47 (md5_I nc50 nd49 na48))
                                   (word_add w5 (EL 51 md5_T)))
                         21) /\
        na52 = word_add nb51
               (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49))
                                   (word_add w12 (EL 52 md5_T)))
                         6) /\
        nd53 = word_add na52
               (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50))
                                   (word_add w3 (EL 53 md5_T)))
                         10) /\
        nc54 = word_add nd53
               (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51))
                                   (word_add w10 (EL 54 md5_T)))
                         15) /\
        nb55 = word_add nc54
               (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52))
                                   (word_add w1 (EL 55 md5_T)))
                         21) /\
        na56 = word_add nb55
               (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53))
                                   (word_add w8 (EL 56 md5_T)))
                         6) /\
        nd57 = word_add na56
               (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54))
                                   (word_add w15 (EL 57 md5_T)))
                         10) /\
        nc58 = word_add nd57
               (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55))
                                   (word_add w6 (EL 58 md5_T)))
                         15) /\
        nb59 = word_add nc58
               (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56))
                                   (word_add w13 (EL 59 md5_T)))
                         21) /\
        na60 = word_add nb59
               (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57))
                                   (word_add w4 (EL 60 md5_T)))
                         6) /\
        nd61 = word_add na60
               (word_rol (word_add (word_add nd57 (md5_I na60 nb59 nc58))
                                   (word_add w11 (EL 61 md5_T)))
                         10) /\
        nc62 = word_add nd61
               (word_rol (word_add (word_add nc58 (md5_I nd61 na60 nb59))
                                   (word_add w2 (EL 62 md5_T)))
                         15) /\
        nb63 = word_add nc62
               (word_rol (word_add (word_add nb59 (md5_I nc62 nd61 na60))
                                   (word_add w9 (EL 63 md5_T)))
                         21)
        ==> md5_compress 64 W [a;b;c;d] =
            [na60; nb63; nc62; nd61]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `64 = 63 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `63 = 62 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `62 = 61 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `61 = 60 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `60 = 59 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `59 = 58 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `58 = 57 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `57 = 56 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `56 = 55 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `55 = 54 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `54 = 53 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `53 = 52 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `52 = 51 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `51 = 50 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `50 = 49 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `49 = 48 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `48 = 47 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `47 = 46 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `46 = 45 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `45 = 44 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `44 = 43 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `43 = 42 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `42 = 41 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `41 = 40 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `40 = 39 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `39 = 38 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `38 = 37 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `37 = 36 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `36 = 35 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `35 = 34 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `34 = 33 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `33 = 32 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `32 = 31 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `31 = 30 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `30 = 29 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `29 = 28 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `28 = 27 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `27 = 26 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `26 = 25 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `25 = 24 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `24 = 23 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `23 = 22 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `22 = 21 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `21 = 20 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `20 = 19 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `19 = 18 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `18 = 17 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `17 = 16 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  (* Round 0 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (a:int32)
             (word_add (md5_F b c d) (word_add (EL 0 W) (EL 0 md5_T))) =
    word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na0:int32 =
    word_add b
     (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 1 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (d:int32)
             (word_add (md5_F na0 b c) (word_add (EL 1 W) (EL 1 md5_T))) =
    word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd1:int32 =
    word_add na0
     (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 2 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (c:int32)
             (word_add (md5_F nd1 na0 b) (word_add (EL 2 W) (EL 2 md5_T))) =
    word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc2:int32 =
    word_add nd1
     (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 3 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (b:int32)
             (word_add (md5_F nc2 nd1 na0) (word_add (EL 3 W) (EL 3 md5_T))) =
    word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb3:int32 =
    word_add nc2
     (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 4 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na0:int32)
             (word_add (md5_F nb3 nc2 nd1) (word_add (EL 4 W) (EL 4 md5_T))) =
    word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na4:int32 =
    word_add nb3
     (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 5 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd1:int32)
             (word_add (md5_F na4 nb3 nc2) (word_add (EL 5 W) (EL 5 md5_T))) =
    word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd5:int32 =
    word_add na4
     (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 6 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc2:int32)
             (word_add (md5_F nd5 na4 nb3) (word_add (EL 6 W) (EL 6 md5_T))) =
    word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc6:int32 =
    word_add nd5
     (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 7 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb3:int32)
             (word_add (md5_F nc6 nd5 na4) (word_add (EL 7 W) (EL 7 md5_T))) =
    word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb7:int32 =
    word_add nc6
     (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 8 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na4:int32)
             (word_add (md5_F nb7 nc6 nd5) (word_add (EL 8 W) (EL 8 md5_T))) =
    word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na8:int32 =
    word_add nb7
     (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 9 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd5:int32)
             (word_add (md5_F na8 nb7 nc6) (word_add (EL 9 W) (EL 9 md5_T))) =
    word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd9:int32 =
    word_add na8
     (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 10 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc6:int32)
             (word_add (md5_F nd9 na8 nb7) (word_add (EL 10 W) (EL 10 md5_T))) =
    word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc10:int32 =
    word_add nd9
     (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 11 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb7:int32)
             (word_add (md5_F nc10 nd9 na8) (word_add (EL 11 W) (EL 11 md5_T))) =
    word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb11:int32 =
    word_add nc10
     (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 12 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na8:int32)
             (word_add (md5_F nb11 nc10 nd9) (word_add (EL 12 W) (EL 12 md5_T))) =
    word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na12:int32 =
    word_add nb11
     (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 13 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd9:int32)
             (word_add (md5_F na12 nb11 nc10) (word_add (EL 13 W) (EL 13 md5_T))) =
    word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd13:int32 =
    word_add na12
     (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 14 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc10:int32)
             (word_add (md5_F nd13 na12 nb11) (word_add (EL 14 W) (EL 14 md5_T))) =
    word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc14:int32 =
    word_add nd13
     (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 15 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb11:int32)
             (word_add (md5_F nc14 nd13 na12) (word_add (EL 15 W) (EL 15 md5_T))) =
    word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb15:int32 =
    word_add nc14
     (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 16 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na12:int32)
             (word_add (md5_G nb15 nc14 nd13) (word_add (EL 1 W) (EL 16 md5_T))) =
    word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na16:int32 =
    word_add nb15
     (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 17 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd13:int32)
             (word_add (md5_G na16 nb15 nc14) (word_add (EL 6 W) (EL 17 md5_T))) =
    word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd17:int32 =
    word_add na16
     (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 18 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc14:int32)
             (word_add (md5_G nd17 na16 nb15) (word_add (EL 11 W) (EL 18 md5_T))) =
    word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc18:int32 =
    word_add nd17
     (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 19 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb15:int32)
             (word_add (md5_G nc18 nd17 na16) (word_add (EL 0 W) (EL 19 md5_T))) =
    word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb19:int32 =
    word_add nc18
     (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 20 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na16:int32)
             (word_add (md5_G nb19 nc18 nd17) (word_add (EL 5 W) (EL 20 md5_T))) =
    word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na20:int32 =
    word_add nb19
     (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 21 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd17:int32)
             (word_add (md5_G na20 nb19 nc18) (word_add (EL 10 W) (EL 21 md5_T))) =
    word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd21:int32 =
    word_add na20
     (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 22 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc18:int32)
             (word_add (md5_G nd21 na20 nb19) (word_add (EL 15 W) (EL 22 md5_T))) =
    word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc22:int32 =
    word_add nd21
     (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 23 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb19:int32)
             (word_add (md5_G nc22 nd21 na20) (word_add (EL 4 W) (EL 23 md5_T))) =
    word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb23:int32 =
    word_add nc22
     (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 24 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na20:int32)
             (word_add (md5_G nb23 nc22 nd21) (word_add (EL 9 W) (EL 24 md5_T))) =
    word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na24:int32 =
    word_add nb23
     (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 25 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd21:int32)
             (word_add (md5_G na24 nb23 nc22) (word_add (EL 14 W) (EL 25 md5_T))) =
    word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd25:int32 =
    word_add na24
     (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 26 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc22:int32)
             (word_add (md5_G nd25 na24 nb23) (word_add (EL 3 W) (EL 26 md5_T))) =
    word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc26:int32 =
    word_add nd25
     (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 27 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb23:int32)
             (word_add (md5_G nc26 nd25 na24) (word_add (EL 8 W) (EL 27 md5_T))) =
    word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb27:int32 =
    word_add nc26
     (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 28 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na24:int32)
             (word_add (md5_G nb27 nc26 nd25) (word_add (EL 13 W) (EL 28 md5_T))) =
    word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na28:int32 =
    word_add nb27
     (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 29 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd25:int32)
             (word_add (md5_G na28 nb27 nc26) (word_add (EL 2 W) (EL 29 md5_T))) =
    word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd29:int32 =
    word_add na28
     (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 30 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc26:int32)
             (word_add (md5_G nd29 na28 nb27) (word_add (EL 7 W) (EL 30 md5_T))) =
    word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc30:int32 =
    word_add nd29
     (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 31 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb27:int32)
             (word_add (md5_G nc30 nd29 na28) (word_add (EL 12 W) (EL 31 md5_T))) =
    word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb31:int32 =
    word_add nc30
     (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 32 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na28:int32)
             (word_add (md5_H nb31 nc30 nd29) (word_add (EL 5 W) (EL 32 md5_T))) =
    word_add (word_add na28 (md5_H nb31 nc30 nd29)) (word_add w5 (EL 32 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na32:int32 =
    word_add nb31
     (word_rol (word_add (word_add na28 (md5_H nb31 nc30 nd29)) (word_add w5 (EL 32 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 33 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd29:int32)
             (word_add (md5_H na32 nb31 nc30) (word_add (EL 8 W) (EL 33 md5_T))) =
    word_add (word_add nd29 (md5_H na32 nb31 nc30)) (word_add w8 (EL 33 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd33:int32 =
    word_add na32
     (word_rol (word_add (word_add nd29 (md5_H na32 nb31 nc30)) (word_add w8 (EL 33 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 34 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc30:int32)
             (word_add (md5_H nd33 na32 nb31) (word_add (EL 11 W) (EL 34 md5_T))) =
    word_add (word_add nc30 (md5_H nd33 na32 nb31)) (word_add w11 (EL 34 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc34:int32 =
    word_add nd33
     (word_rol (word_add (word_add nc30 (md5_H nd33 na32 nb31)) (word_add w11 (EL 34 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 35 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb31:int32)
             (word_add (md5_H nc34 nd33 na32) (word_add (EL 14 W) (EL 35 md5_T))) =
    word_add (word_add nb31 (md5_H nc34 nd33 na32)) (word_add w14 (EL 35 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb35:int32 =
    word_add nc34
     (word_rol (word_add (word_add nb31 (md5_H nc34 nd33 na32)) (word_add w14 (EL 35 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 36 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na32:int32)
             (word_add (md5_H nb35 nc34 nd33) (word_add (EL 1 W) (EL 36 md5_T))) =
    word_add (word_add na32 (md5_H nb35 nc34 nd33)) (word_add w1 (EL 36 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na36:int32 =
    word_add nb35
     (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33)) (word_add w1 (EL 36 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 37 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd33:int32)
             (word_add (md5_H na36 nb35 nc34) (word_add (EL 4 W) (EL 37 md5_T))) =
    word_add (word_add nd33 (md5_H na36 nb35 nc34)) (word_add w4 (EL 37 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd37:int32 =
    word_add na36
     (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34)) (word_add w4 (EL 37 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 38 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc34:int32)
             (word_add (md5_H nd37 na36 nb35) (word_add (EL 7 W) (EL 38 md5_T))) =
    word_add (word_add nc34 (md5_H nd37 na36 nb35)) (word_add w7 (EL 38 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc38:int32 =
    word_add nd37
     (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35)) (word_add w7 (EL 38 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 39 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb35:int32)
             (word_add (md5_H nc38 nd37 na36) (word_add (EL 10 W) (EL 39 md5_T))) =
    word_add (word_add nb35 (md5_H nc38 nd37 na36)) (word_add w10 (EL 39 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb39:int32 =
    word_add nc38
     (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36)) (word_add w10 (EL 39 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 40 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na36:int32)
             (word_add (md5_H nb39 nc38 nd37) (word_add (EL 13 W) (EL 40 md5_T))) =
    word_add (word_add na36 (md5_H nb39 nc38 nd37)) (word_add w13 (EL 40 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na40:int32 =
    word_add nb39
     (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37)) (word_add w13 (EL 40 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 41 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd37:int32)
             (word_add (md5_H na40 nb39 nc38) (word_add (EL 0 W) (EL 41 md5_T))) =
    word_add (word_add nd37 (md5_H na40 nb39 nc38)) (word_add w0 (EL 41 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd41:int32 =
    word_add na40
     (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38)) (word_add w0 (EL 41 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 42 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc38:int32)
             (word_add (md5_H nd41 na40 nb39) (word_add (EL 3 W) (EL 42 md5_T))) =
    word_add (word_add nc38 (md5_H nd41 na40 nb39)) (word_add w3 (EL 42 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc42:int32 =
    word_add nd41
     (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39)) (word_add w3 (EL 42 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 43 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb39:int32)
             (word_add (md5_H nc42 nd41 na40) (word_add (EL 6 W) (EL 43 md5_T))) =
    word_add (word_add nb39 (md5_H nc42 nd41 na40)) (word_add w6 (EL 43 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb43:int32 =
    word_add nc42
     (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40)) (word_add w6 (EL 43 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 44 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na40:int32)
             (word_add (md5_H nb43 nc42 nd41) (word_add (EL 9 W) (EL 44 md5_T))) =
    word_add (word_add na40 (md5_H nb43 nc42 nd41)) (word_add w9 (EL 44 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na44:int32 =
    word_add nb43
     (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41)) (word_add w9 (EL 44 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 45 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd41:int32)
             (word_add (md5_H na44 nb43 nc42) (word_add (EL 12 W) (EL 45 md5_T))) =
    word_add (word_add nd41 (md5_H na44 nb43 nc42)) (word_add w12 (EL 45 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd45:int32 =
    word_add na44
     (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42)) (word_add w12 (EL 45 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 46 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc42:int32)
             (word_add (md5_H nd45 na44 nb43) (word_add (EL 15 W) (EL 46 md5_T))) =
    word_add (word_add nc42 (md5_H nd45 na44 nb43)) (word_add w15 (EL 46 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc46:int32 =
    word_add nd45
     (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43)) (word_add w15 (EL 46 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 47 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb43:int32)
             (word_add (md5_H nc46 nd45 na44) (word_add (EL 2 W) (EL 47 md5_T))) =
    word_add (word_add nb43 (md5_H nc46 nd45 na44)) (word_add w2 (EL 47 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb47:int32 =
    word_add nc46
     (word_rol (word_add (word_add nb43 (md5_H nc46 nd45 na44)) (word_add w2 (EL 47 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 48 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na44:int32)
             (word_add (md5_I nb47 nc46 nd45) (word_add (EL 0 W) (EL 48 md5_T))) =
    word_add (word_add na44 (md5_I nb47 nc46 nd45)) (word_add w0 (EL 48 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na48:int32 =
    word_add nb47
     (word_rol (word_add (word_add na44 (md5_I nb47 nc46 nd45)) (word_add w0 (EL 48 md5_T)))
               6)`
   (SUBST1_TAC o SYM) THEN
  (* Round 49 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd45:int32)
             (word_add (md5_I na48 nb47 nc46) (word_add (EL 7 W) (EL 49 md5_T))) =
    word_add (word_add nd45 (md5_I na48 nb47 nc46)) (word_add w7 (EL 49 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd49:int32 =
    word_add na48
     (word_rol (word_add (word_add nd45 (md5_I na48 nb47 nc46)) (word_add w7 (EL 49 md5_T)))
               10)`
   (SUBST1_TAC o SYM) THEN
  (* Round 50 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc46:int32)
             (word_add (md5_I nd49 na48 nb47) (word_add (EL 14 W) (EL 50 md5_T))) =
    word_add (word_add nc46 (md5_I nd49 na48 nb47)) (word_add w14 (EL 50 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc50:int32 =
    word_add nd49
     (word_rol (word_add (word_add nc46 (md5_I nd49 na48 nb47)) (word_add w14 (EL 50 md5_T)))
               15)`
   (SUBST1_TAC o SYM) THEN
  (* Round 51 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb47:int32)
             (word_add (md5_I nc50 nd49 na48) (word_add (EL 5 W) (EL 51 md5_T))) =
    word_add (word_add nb47 (md5_I nc50 nd49 na48)) (word_add w5 (EL 51 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb51:int32 =
    word_add nc50
     (word_rol (word_add (word_add nb47 (md5_I nc50 nd49 na48)) (word_add w5 (EL 51 md5_T)))
               21)`
   (SUBST1_TAC o SYM) THEN
  (* Round 52 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na48:int32)
             (word_add (md5_I nb51 nc50 nd49) (word_add (EL 12 W) (EL 52 md5_T))) =
    word_add (word_add na48 (md5_I nb51 nc50 nd49)) (word_add w12 (EL 52 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na52:int32 =
    word_add nb51
     (word_rol (word_add (word_add na48 (md5_I nb51 nc50 nd49)) (word_add w12 (EL 52 md5_T)))
               6)`
   (SUBST1_TAC o SYM) THEN
  (* Round 53 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd49:int32)
             (word_add (md5_I na52 nb51 nc50) (word_add (EL 3 W) (EL 53 md5_T))) =
    word_add (word_add nd49 (md5_I na52 nb51 nc50)) (word_add w3 (EL 53 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd53:int32 =
    word_add na52
     (word_rol (word_add (word_add nd49 (md5_I na52 nb51 nc50)) (word_add w3 (EL 53 md5_T)))
               10)`
   (SUBST1_TAC o SYM) THEN
  (* Round 54 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc50:int32)
             (word_add (md5_I nd53 na52 nb51) (word_add (EL 10 W) (EL 54 md5_T))) =
    word_add (word_add nc50 (md5_I nd53 na52 nb51)) (word_add w10 (EL 54 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc54:int32 =
    word_add nd53
     (word_rol (word_add (word_add nc50 (md5_I nd53 na52 nb51)) (word_add w10 (EL 54 md5_T)))
               15)`
   (SUBST1_TAC o SYM) THEN
  (* Round 55 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb51:int32)
             (word_add (md5_I nc54 nd53 na52) (word_add (EL 1 W) (EL 55 md5_T))) =
    word_add (word_add nb51 (md5_I nc54 nd53 na52)) (word_add w1 (EL 55 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb55:int32 =
    word_add nc54
     (word_rol (word_add (word_add nb51 (md5_I nc54 nd53 na52)) (word_add w1 (EL 55 md5_T)))
               21)`
   (SUBST1_TAC o SYM) THEN
  (* Round 56 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na52:int32)
             (word_add (md5_I nb55 nc54 nd53) (word_add (EL 8 W) (EL 56 md5_T))) =
    word_add (word_add na52 (md5_I nb55 nc54 nd53)) (word_add w8 (EL 56 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na56:int32 =
    word_add nb55
     (word_rol (word_add (word_add na52 (md5_I nb55 nc54 nd53)) (word_add w8 (EL 56 md5_T)))
               6)`
   (SUBST1_TAC o SYM) THEN
  (* Round 57 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd53:int32)
             (word_add (md5_I na56 nb55 nc54) (word_add (EL 15 W) (EL 57 md5_T))) =
    word_add (word_add nd53 (md5_I na56 nb55 nc54)) (word_add w15 (EL 57 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd57:int32 =
    word_add na56
     (word_rol (word_add (word_add nd53 (md5_I na56 nb55 nc54)) (word_add w15 (EL 57 md5_T)))
               10)`
   (SUBST1_TAC o SYM) THEN
  (* Round 58 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc54:int32)
             (word_add (md5_I nd57 na56 nb55) (word_add (EL 6 W) (EL 58 md5_T))) =
    word_add (word_add nc54 (md5_I nd57 na56 nb55)) (word_add w6 (EL 58 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc58:int32 =
    word_add nd57
     (word_rol (word_add (word_add nc54 (md5_I nd57 na56 nb55)) (word_add w6 (EL 58 md5_T)))
               15)`
   (SUBST1_TAC o SYM) THEN
  (* Round 59 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb55:int32)
             (word_add (md5_I nc58 nd57 na56) (word_add (EL 13 W) (EL 59 md5_T))) =
    word_add (word_add nb55 (md5_I nc58 nd57 na56)) (word_add w13 (EL 59 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb59:int32 =
    word_add nc58
     (word_rol (word_add (word_add nb55 (md5_I nc58 nd57 na56)) (word_add w13 (EL 59 md5_T)))
               21)`
   (SUBST1_TAC o SYM) THEN
  (* Round 60 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na56:int32)
             (word_add (md5_I nb59 nc58 nd57) (word_add (EL 4 W) (EL 60 md5_T))) =
    word_add (word_add na56 (md5_I nb59 nc58 nd57)) (word_add w4 (EL 60 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na60:int32 =
    word_add nb59
     (word_rol (word_add (word_add na56 (md5_I nb59 nc58 nd57)) (word_add w4 (EL 60 md5_T)))
               6)`
   (SUBST1_TAC o SYM) THEN
  (* Round 61 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd57:int32)
             (word_add (md5_I na60 nb59 nc58) (word_add (EL 11 W) (EL 61 md5_T))) =
    word_add (word_add nd57 (md5_I na60 nb59 nc58)) (word_add w11 (EL 61 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd61:int32 =
    word_add na60
     (word_rol (word_add (word_add nd57 (md5_I na60 nb59 nc58)) (word_add w11 (EL 61 md5_T)))
               10)`
   (SUBST1_TAC o SYM) THEN
  (* Round 62 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc58:int32)
             (word_add (md5_I nd61 na60 nb59) (word_add (EL 2 W) (EL 62 md5_T))) =
    word_add (word_add nc58 (md5_I nd61 na60 nb59)) (word_add w2 (EL 62 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc62:int32 =
    word_add nd61
     (word_rol (word_add (word_add nc58 (md5_I nd61 na60 nb59)) (word_add w2 (EL 62 md5_T)))
               15)`
   (SUBST1_TAC o SYM) THEN
  (* Round 63 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb59:int32)
             (word_add (md5_I nc62 nd61 na60) (word_add (EL 9 W) (EL 63 md5_T))) =
    word_add (word_add nb59 (md5_I nc62 nd61 na60)) (word_add w9 (EL 63 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb63:int32 =
    word_add nc62
     (word_rol (word_add (word_add nb59 (md5_I nc62 nd61 na60)) (word_add w9 (EL 63 md5_T)))
               21)`
   (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Spec-form retrofit (round 1): md5_compress 16 W [a;b;c;d] =                *)
(*                               [na12; nb15; nc14; nd13].                   *)
(*                                                                            *)
(* Phase-9 prep round-1 bridge. Truncated 16-step variant of                  *)
(* MD5_COMPRESS_64_VALUES. Each per-step na/nd/nc/nb is bound to its          *)
(* standard MD5 update formula using the round-1 selector md5_F.              *)
(* The conclusion gives the cyclic rotation result after 16 rounds.           *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_16_F_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        na0 nd1 nc2 nb3 na4 nd5 nc6 nb7
        na8 nd9 nc10 nb11 na12 nd13 nc14 nb15.
        LENGTH W = 16 /\
        w0 = EL 0 W /\
        w1 = EL 1 W /\
        w2 = EL 2 W /\
        w3 = EL 3 W /\
        w4 = EL 4 W /\
        w5 = EL 5 W /\
        w6 = EL 6 W /\
        w7 = EL 7 W /\
        w8 = EL 8 W /\
        w9 = EL 9 W /\
        w10 = EL 10 W /\
        w11 = EL 11 W /\
        w12 = EL 12 W /\
        w13 = EL 13 W /\
        w14 = EL 14 W /\
        w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T)))
                         7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T)))
                         12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T)))
                         17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T)))
                         22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T)))
                         7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T)))
                         12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T)))
                         17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T)))
                         22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T)))
                         7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T)))
                         12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T)))
                         17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T)))
                         22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T)))
                         7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T)))
                         12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T)))
                         17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T)))
                         22)
        ==> md5_compress 16 W [a;b;c;d] =
            [na12; nb15; nc14; nd13]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  (* Round 0 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (a:int32)
             (word_add (md5_F b c d) (word_add (EL 0 W) (EL 0 md5_T))) =
    word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na0:int32 =
    word_add b
     (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 1 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (d:int32)
             (word_add (md5_F na0 b c) (word_add (EL 1 W) (EL 1 md5_T))) =
    word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd1:int32 =
    word_add na0
     (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 2 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (c:int32)
             (word_add (md5_F nd1 na0 b) (word_add (EL 2 W) (EL 2 md5_T))) =
    word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc2:int32 =
    word_add nd1
     (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 3 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (b:int32)
             (word_add (md5_F nc2 nd1 na0) (word_add (EL 3 W) (EL 3 md5_T))) =
    word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb3:int32 =
    word_add nc2
     (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 4 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na0:int32)
             (word_add (md5_F nb3 nc2 nd1) (word_add (EL 4 W) (EL 4 md5_T))) =
    word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na4:int32 =
    word_add nb3
     (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 5 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd1:int32)
             (word_add (md5_F na4 nb3 nc2) (word_add (EL 5 W) (EL 5 md5_T))) =
    word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd5:int32 =
    word_add na4
     (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 6 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc2:int32)
             (word_add (md5_F nd5 na4 nb3) (word_add (EL 6 W) (EL 6 md5_T))) =
    word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc6:int32 =
    word_add nd5
     (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 7 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb3:int32)
             (word_add (md5_F nc6 nd5 na4) (word_add (EL 7 W) (EL 7 md5_T))) =
    word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb7:int32 =
    word_add nc6
     (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 8 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na4:int32)
             (word_add (md5_F nb7 nc6 nd5) (word_add (EL 8 W) (EL 8 md5_T))) =
    word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na8:int32 =
    word_add nb7
     (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 9 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd5:int32)
             (word_add (md5_F na8 nb7 nc6) (word_add (EL 9 W) (EL 9 md5_T))) =
    word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd9:int32 =
    word_add na8
     (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 10 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc6:int32)
             (word_add (md5_F nd9 na8 nb7) (word_add (EL 10 W) (EL 10 md5_T))) =
    word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc10:int32 =
    word_add nd9
     (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 11 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb7:int32)
             (word_add (md5_F nc10 nd9 na8) (word_add (EL 11 W) (EL 11 md5_T))) =
    word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb11:int32 =
    word_add nc10
     (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 12 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na8:int32)
             (word_add (md5_F nb11 nc10 nd9) (word_add (EL 12 W) (EL 12 md5_T))) =
    word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na12:int32 =
    word_add nb11
     (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 13 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd9:int32)
             (word_add (md5_F na12 nb11 nc10) (word_add (EL 13 W) (EL 13 md5_T))) =
    word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd13:int32 =
    word_add na12
     (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 14 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc10:int32)
             (word_add (md5_F nd13 na12 nb11) (word_add (EL 14 W) (EL 14 md5_T))) =
    word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc14:int32 =
    word_add nd13
     (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 15 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb11:int32)
             (word_add (md5_F nc14 nd13 na12) (word_add (EL 15 W) (EL 15 md5_T))) =
    word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb15:int32 =
    word_add nc14
     (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* EL-form retrofit of MD5_COMPRESS_16_F_VALUES.                              *)
(* Same chain hypotheses; conclusion uses EL k (md5_compress 16 W [a;b;c;d])  *)
(* so callers (e.g. R1->R2 bridge) can match ROUND2's pre-condition without   *)
(* unrolling the let-form list literal in the cut predicate.                  *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_16_F_EL_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    na0 nd1 nc2 nb3 na4 nd5 nc6 nb7 na8 nd9 nc10 nb11 na12 nd13 nc14 nb15.
        LENGTH W = 16 /\
        w0 = EL 0 W /\ w1 = EL 1 W /\ w2 = EL 2 W /\ w3 = EL 3 W /\
        w4 = EL 4 W /\ w5 = EL 5 W /\ w6 = EL 6 W /\ w7 = EL 7 W /\
        w8 = EL 8 W /\ w9 = EL 9 W /\ w10 = EL 10 W /\ w11 = EL 11 W /\
        w12 = EL 12 W /\ w13 = EL 13 W /\ w14 = EL 14 W /\ w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T))) 7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T))) 12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T))) 17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T))) 22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T))) 7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T))) 12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T))) 17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T))) 22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T))) 7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T))) 12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T))) 17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T))) 22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T))) 7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T))) 12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T))) 17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T))) 22)
        ==> EL 0 (md5_compress 16 W [a;b;c;d]) = na12 /\
            EL 1 (md5_compress 16 W [a;b;c;d]) = nb15 /\
            EL 2 (md5_compress 16 W [a;b;c;d]) = nc14 /\
            EL 3 (md5_compress 16 W [a;b;c;d]) = nd13`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL
    [`W:int32 list`; `a:int32`; `b:int32`; `c:int32`; `d:int32`;
     `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`;
     `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`; `w9:int32`;
     `w10:int32`; `w11:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`;
     `na0:int32`; `nd1:int32`; `nc2:int32`; `nb3:int32`;
     `na4:int32`; `nd5:int32`; `nc6:int32`; `nb7:int32`;
     `na8:int32`; `nd9:int32`; `nc10:int32`; `nb11:int32`;
     `na12:int32`; `nd13:int32`; `nc14:int32`; `nb15:int32`]
    MD5_COMPRESS_16_F_VALUES) THEN
  ANTS_TAC THENL [POP_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MD5_F_LET_TO_EL_4WAY: bridges TEST_R1's let-form post (4 RAX..RDX equations) *)
(* to EL i (md5_compress 16 ... [a;b;c;d]) form for i = 0,1,2,3.              *)
(* Used in MD5_BLOCK_BODY_TEST_R1_R2 segment-1 SUB_T3.                          *)
(* ------------------------------------------------------------------------- *)

let MD5_F_LET_TO_EL_4WAY = prove
 (`!(s:x86state) (a:int32) b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
        (read RAX s =
         word_zx
          (
           let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
           let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
           let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
           let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
           let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
           let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
           let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
           let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
           let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
           let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
           let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
           let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
           let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
           na12)) /\
        (read RBX s =
         word_zx
          (
           let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
           let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
           let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
           let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
           let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
           let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
           let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
           let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
           let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
           let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
           let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
           let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
           let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
           let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
           let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
           let nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22) in
           nb15)) /\
        (read RCX s =
         word_zx
          (
           let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
           let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
           let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
           let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
           let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
           let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
           let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
           let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
           let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
           let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
           let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
           let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
           let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
           let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
           let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
           nc14)) /\
        (read RDX s =
         word_zx
          (
           let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
           let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
           let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
           let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
           let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
           let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
           let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
           let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
           let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
           let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
           let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
           let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
           let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
           let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
           nd13))
       ==> read RAX s = word_zx (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RBX s = word_zx (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RCX s = word_zx (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RDX s = word_zx (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7)` THEN
  ABBREV_TAC `nd1 = word_add (na0:int32) (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12)` THEN
  ABBREV_TAC `nc2 = word_add (nd1:int32) (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17)` THEN
  ABBREV_TAC `nb3 = word_add (nc2:int32) (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22)` THEN
  ABBREV_TAC `na4 = word_add (nb3:int32) (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7)` THEN
  ABBREV_TAC `nd5 = word_add (na4:int32) (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12)` THEN
  ABBREV_TAC `nc6 = word_add (nd5:int32) (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17)` THEN
  ABBREV_TAC `nb7 = word_add (nc6:int32) (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22)` THEN
  ABBREV_TAC `na8 = word_add (nb7:int32) (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7)` THEN
  ABBREV_TAC `nd9 = word_add (na8:int32) (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12)` THEN
  ABBREV_TAC `nc10 = word_add (nd9:int32) (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17)` THEN
  ABBREV_TAC `nb11 = word_add (nc10:int32) (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22)` THEN
  ABBREV_TAC `na12 = word_add (nb11:int32) (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7)` THEN
  ABBREV_TAC `nd13 = word_add (na12:int32) (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12)` THEN
  ABBREV_TAC `nc14 = word_add (nd13:int32) (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17)` THEN
  ABBREV_TAC `nb15 = word_add (nc14:int32) (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22)` THEN
  MP_TAC(SPECL
    [`[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]:int32 list`;
     `a:int32`;`b:int32`;`c:int32`;`d:int32`;
     `w0:int32`;`w1:int32`;`w2:int32`;`w3:int32`;
     `w4:int32`;`w5:int32`;`w6:int32`;`w7:int32`;
     `w8:int32`;`w9:int32`;`w10:int32`;`w11:int32`;
     `w12:int32`;`w13:int32`;`w14:int32`;`w15:int32`;
     `na0:int32`;`nd1:int32`;`nc2:int32`;`nb3:int32`;
     `na4:int32`;`nd5:int32`;`nc6:int32`;`nb7:int32`;
     `na8:int32`;`nd9:int32`;`nc10:int32`;`nb11:int32`;
     `na12:int32`;`nd13:int32`;`nc14:int32`;`nb15:int32`]
    MD5_COMPRESS_16_F_EL_VALUES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH;ARITH] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      EXPAND_TAC "na0" THEN REFL_TAC;
      EXPAND_TAC "nd1" THEN REFL_TAC;
      EXPAND_TAC "nc2" THEN REFL_TAC;
      EXPAND_TAC "nb3" THEN REFL_TAC;
      EXPAND_TAC "na4" THEN REFL_TAC;
      EXPAND_TAC "nd5" THEN REFL_TAC;
      EXPAND_TAC "nc6" THEN REFL_TAC;
      EXPAND_TAC "nb7" THEN REFL_TAC;
      EXPAND_TAC "na8" THEN REFL_TAC;
      EXPAND_TAC "nd9" THEN REFL_TAC;
      EXPAND_TAC "nc10" THEN REFL_TAC;
      EXPAND_TAC "nb11" THEN REFL_TAC;
      EXPAND_TAC "na12" THEN REFL_TAC;
      EXPAND_TAC "nd13" THEN REFL_TAC;
      EXPAND_TAC "nc14" THEN REFL_TAC;
      EXPAND_TAC "nb15" THEN REFL_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Spec-form retrofit (rounds 1-2): md5_compress 32 W [a;b;c;d] =             *)
(*                               [na28; nb31; nc30; nd29].                   *)
(*                                                                            *)
(* Phase-9 prep round-2 bridge. Truncated 32-step variant of                  *)
(* MD5_COMPRESS_64_VALUES. Each per-step na/nd/nc/nb is bound to its          *)
(* standard MD5 update formula using the round-1 selector md5_F (steps 0..15) *)
(* and the round-2 selector md5_G (steps 16..31).                             *)
(* The conclusion gives the cyclic rotation result after 32 rounds.           *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_32_G_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        na0 nd1 nc2 nb3 na4 nd5 nc6 nb7
        na8 nd9 nc10 nb11 na12 nd13 nc14 nb15
        na16 nd17 nc18 nb19 na20 nd21 nc22 nb23
        na24 nd25 nc26 nb27 na28 nd29 nc30 nb31.
        LENGTH W = 16 /\
        w0 = EL 0 W /\
        w1 = EL 1 W /\
        w2 = EL 2 W /\
        w3 = EL 3 W /\
        w4 = EL 4 W /\
        w5 = EL 5 W /\
        w6 = EL 6 W /\
        w7 = EL 7 W /\
        w8 = EL 8 W /\
        w9 = EL 9 W /\
        w10 = EL 10 W /\
        w11 = EL 11 W /\
        w12 = EL 12 W /\
        w13 = EL 13 W /\
        w14 = EL 14 W /\
        w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T)))
                         7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T)))
                         12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T)))
                         17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T)))
                         22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T)))
                         7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T)))
                         12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T)))
                         17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T)))
                         22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T)))
                         7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T)))
                         12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T)))
                         17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T)))
                         22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T)))
                         7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T)))
                         12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T)))
                         17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T)))
                         22) /\
        na16 = word_add nb15
               (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13))
                                   (word_add w1 (EL 16 md5_T)))
                         5) /\
        nd17 = word_add na16
               (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14))
                                   (word_add w6 (EL 17 md5_T)))
                         9) /\
        nc18 = word_add nd17
               (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15))
                                   (word_add w11 (EL 18 md5_T)))
                         14) /\
        nb19 = word_add nc18
               (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16))
                                   (word_add w0 (EL 19 md5_T)))
                         20) /\
        na20 = word_add nb19
               (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                   (word_add w5 (EL 20 md5_T)))
                         5) /\
        nd21 = word_add na20
               (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                   (word_add w10 (EL 21 md5_T)))
                         9) /\
        nc22 = word_add nd21
               (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                   (word_add w15 (EL 22 md5_T)))
                         14) /\
        nb23 = word_add nc22
               (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                   (word_add w4 (EL 23 md5_T)))
                         20) /\
        na24 = word_add nb23
               (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                   (word_add w9 (EL 24 md5_T)))
                         5) /\
        nd25 = word_add na24
               (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                   (word_add w14 (EL 25 md5_T)))
                         9) /\
        nc26 = word_add nd25
               (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                   (word_add w3 (EL 26 md5_T)))
                         14) /\
        nb27 = word_add nc26
               (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                   (word_add w8 (EL 27 md5_T)))
                         20) /\
        na28 = word_add nb27
               (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                   (word_add w13 (EL 28 md5_T)))
                         5) /\
        nd29 = word_add na28
               (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                   (word_add w2 (EL 29 md5_T)))
                         9) /\
        nc30 = word_add nd29
               (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                   (word_add w7 (EL 30 md5_T)))
                         14) /\
        nb31 = word_add nc30
               (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                   (word_add w12 (EL 31 md5_T)))
                         20)
        ==> md5_compress 32 W [a;b;c;d] =
            [na28; nb31; nc30; nd29]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `32 = 31 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `31 = 30 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `30 = 29 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `29 = 28 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `28 = 27 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `27 = 26 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `26 = 25 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `25 = 24 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `24 = 23 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `23 = 22 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `22 = 21 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `21 = 20 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `20 = 19 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `19 = 18 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `18 = 17 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `17 = 16 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  (* Round 0 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (a:int32)
             (word_add (md5_F b c d) (word_add (EL 0 W) (EL 0 md5_T))) =
    word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na0:int32 =
    word_add b
     (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 1 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (d:int32)
             (word_add (md5_F na0 b c) (word_add (EL 1 W) (EL 1 md5_T))) =
    word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd1:int32 =
    word_add na0
     (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 2 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (c:int32)
             (word_add (md5_F nd1 na0 b) (word_add (EL 2 W) (EL 2 md5_T))) =
    word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc2:int32 =
    word_add nd1
     (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 3 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (b:int32)
             (word_add (md5_F nc2 nd1 na0) (word_add (EL 3 W) (EL 3 md5_T))) =
    word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb3:int32 =
    word_add nc2
     (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 4 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na0:int32)
             (word_add (md5_F nb3 nc2 nd1) (word_add (EL 4 W) (EL 4 md5_T))) =
    word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na4:int32 =
    word_add nb3
     (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 5 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd1:int32)
             (word_add (md5_F na4 nb3 nc2) (word_add (EL 5 W) (EL 5 md5_T))) =
    word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd5:int32 =
    word_add na4
     (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 6 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc2:int32)
             (word_add (md5_F nd5 na4 nb3) (word_add (EL 6 W) (EL 6 md5_T))) =
    word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc6:int32 =
    word_add nd5
     (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 7 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb3:int32)
             (word_add (md5_F nc6 nd5 na4) (word_add (EL 7 W) (EL 7 md5_T))) =
    word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb7:int32 =
    word_add nc6
     (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 8 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na4:int32)
             (word_add (md5_F nb7 nc6 nd5) (word_add (EL 8 W) (EL 8 md5_T))) =
    word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na8:int32 =
    word_add nb7
     (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 9 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd5:int32)
             (word_add (md5_F na8 nb7 nc6) (word_add (EL 9 W) (EL 9 md5_T))) =
    word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd9:int32 =
    word_add na8
     (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 10 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc6:int32)
             (word_add (md5_F nd9 na8 nb7) (word_add (EL 10 W) (EL 10 md5_T))) =
    word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc10:int32 =
    word_add nd9
     (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 11 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb7:int32)
             (word_add (md5_F nc10 nd9 na8) (word_add (EL 11 W) (EL 11 md5_T))) =
    word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb11:int32 =
    word_add nc10
     (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 12 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na8:int32)
             (word_add (md5_F nb11 nc10 nd9) (word_add (EL 12 W) (EL 12 md5_T))) =
    word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na12:int32 =
    word_add nb11
     (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 13 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd9:int32)
             (word_add (md5_F na12 nb11 nc10) (word_add (EL 13 W) (EL 13 md5_T))) =
    word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd13:int32 =
    word_add na12
     (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 14 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc10:int32)
             (word_add (md5_F nd13 na12 nb11) (word_add (EL 14 W) (EL 14 md5_T))) =
    word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc14:int32 =
    word_add nd13
     (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 15 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb11:int32)
             (word_add (md5_F nc14 nd13 na12) (word_add (EL 15 W) (EL 15 md5_T))) =
    word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb15:int32 =
    word_add nc14
     (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 16 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na12:int32)
             (word_add (md5_G nb15 nc14 nd13) (word_add (EL 1 W) (EL 16 md5_T))) =
    word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na16:int32 =
    word_add nb15
     (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 17 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd13:int32)
             (word_add (md5_G na16 nb15 nc14) (word_add (EL 6 W) (EL 17 md5_T))) =
    word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd17:int32 =
    word_add na16
     (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 18 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc14:int32)
             (word_add (md5_G nd17 na16 nb15) (word_add (EL 11 W) (EL 18 md5_T))) =
    word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc18:int32 =
    word_add nd17
     (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 19 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb15:int32)
             (word_add (md5_G nc18 nd17 na16) (word_add (EL 0 W) (EL 19 md5_T))) =
    word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb19:int32 =
    word_add nc18
     (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 20 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na16:int32)
             (word_add (md5_G nb19 nc18 nd17) (word_add (EL 5 W) (EL 20 md5_T))) =
    word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na20:int32 =
    word_add nb19
     (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 21 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd17:int32)
             (word_add (md5_G na20 nb19 nc18) (word_add (EL 10 W) (EL 21 md5_T))) =
    word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd21:int32 =
    word_add na20
     (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 22 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc18:int32)
             (word_add (md5_G nd21 na20 nb19) (word_add (EL 15 W) (EL 22 md5_T))) =
    word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc22:int32 =
    word_add nd21
     (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 23 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb19:int32)
             (word_add (md5_G nc22 nd21 na20) (word_add (EL 4 W) (EL 23 md5_T))) =
    word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb23:int32 =
    word_add nc22
     (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 24 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na20:int32)
             (word_add (md5_G nb23 nc22 nd21) (word_add (EL 9 W) (EL 24 md5_T))) =
    word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na24:int32 =
    word_add nb23
     (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 25 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd21:int32)
             (word_add (md5_G na24 nb23 nc22) (word_add (EL 14 W) (EL 25 md5_T))) =
    word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd25:int32 =
    word_add na24
     (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 26 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc22:int32)
             (word_add (md5_G nd25 na24 nb23) (word_add (EL 3 W) (EL 26 md5_T))) =
    word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc26:int32 =
    word_add nd25
     (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 27 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb23:int32)
             (word_add (md5_G nc26 nd25 na24) (word_add (EL 8 W) (EL 27 md5_T))) =
    word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb27:int32 =
    word_add nc26
     (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 28 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na24:int32)
             (word_add (md5_G nb27 nc26 nd25) (word_add (EL 13 W) (EL 28 md5_T))) =
    word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na28:int32 =
    word_add nb27
     (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 29 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd25:int32)
             (word_add (md5_G na28 nb27 nc26) (word_add (EL 2 W) (EL 29 md5_T))) =
    word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd29:int32 =
    word_add na28
     (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 30 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc26:int32)
             (word_add (md5_G nd29 na28 nb27) (word_add (EL 7 W) (EL 30 md5_T))) =
    word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc30:int32 =
    word_add nd29
     (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 31 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb27:int32)
             (word_add (md5_G nc30 nd29 na28) (word_add (EL 12 W) (EL 31 md5_T))) =
    word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb31:int32 =
    word_add nc30
     (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* EL-form retrofit of MD5_COMPRESS_32_G_VALUES.                              *)
(* Same chain hypotheses; conclusion uses EL k (md5_compress 32 W [a;b;c;d])  *)
(* so callers (e.g. R2->R3 bridge) can match ROUND3's pre-condition without   *)
(* unrolling the let-form list literal in the cut predicate.                  *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_32_G_EL_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        na0 nd1 nc2 nb3 na4 nd5 nc6 nb7
        na8 nd9 nc10 nb11 na12 nd13 nc14 nb15
        na16 nd17 nc18 nb19 na20 nd21 nc22 nb23
        na24 nd25 nc26 nb27 na28 nd29 nc30 nb31.
        LENGTH W = 16 /\
        w0 = EL 0 W /\ w1 = EL 1 W /\ w2 = EL 2 W /\ w3 = EL 3 W /\
        w4 = EL 4 W /\ w5 = EL 5 W /\ w6 = EL 6 W /\ w7 = EL 7 W /\
        w8 = EL 8 W /\ w9 = EL 9 W /\ w10 = EL 10 W /\ w11 = EL 11 W /\
        w12 = EL 12 W /\ w13 = EL 13 W /\ w14 = EL 14 W /\ w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T))) 7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T))) 12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T))) 17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T))) 22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T))) 7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T))) 12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T))) 17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T))) 22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T))) 7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T))) 12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T))) 17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T))) 22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T))) 7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T))) 12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T))) 17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T))) 22) /\
        na16 = word_add nb15
               (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13))
                                   (word_add w1 (EL 16 md5_T))) 5) /\
        nd17 = word_add na16
               (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14))
                                   (word_add w6 (EL 17 md5_T))) 9) /\
        nc18 = word_add nd17
               (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15))
                                   (word_add w11 (EL 18 md5_T))) 14) /\
        nb19 = word_add nc18
               (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16))
                                   (word_add w0 (EL 19 md5_T))) 20) /\
        na20 = word_add nb19
               (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                   (word_add w5 (EL 20 md5_T))) 5) /\
        nd21 = word_add na20
               (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                   (word_add w10 (EL 21 md5_T))) 9) /\
        nc22 = word_add nd21
               (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                   (word_add w15 (EL 22 md5_T))) 14) /\
        nb23 = word_add nc22
               (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                   (word_add w4 (EL 23 md5_T))) 20) /\
        na24 = word_add nb23
               (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                   (word_add w9 (EL 24 md5_T))) 5) /\
        nd25 = word_add na24
               (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                   (word_add w14 (EL 25 md5_T))) 9) /\
        nc26 = word_add nd25
               (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                   (word_add w3 (EL 26 md5_T))) 14) /\
        nb27 = word_add nc26
               (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                   (word_add w8 (EL 27 md5_T))) 20) /\
        na28 = word_add nb27
               (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                   (word_add w13 (EL 28 md5_T))) 5) /\
        nd29 = word_add na28
               (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                   (word_add w2 (EL 29 md5_T))) 9) /\
        nc30 = word_add nd29
               (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                   (word_add w7 (EL 30 md5_T))) 14) /\
        nb31 = word_add nc30
               (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                   (word_add w12 (EL 31 md5_T))) 20)
        ==> EL 0 (md5_compress 32 W [a;b;c;d]) = na28 /\
            EL 1 (md5_compress 32 W [a;b;c;d]) = nb31 /\
            EL 2 (md5_compress 32 W [a;b;c;d]) = nc30 /\
            EL 3 (md5_compress 32 W [a;b;c;d]) = nd29`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL
    [`W:int32 list`; `a:int32`; `b:int32`; `c:int32`; `d:int32`;
     `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`;
     `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`; `w9:int32`;
     `w10:int32`; `w11:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`;
     `na0:int32`; `nd1:int32`; `nc2:int32`; `nb3:int32`;
     `na4:int32`; `nd5:int32`; `nc6:int32`; `nb7:int32`;
     `na8:int32`; `nd9:int32`; `nc10:int32`; `nb11:int32`;
     `na12:int32`; `nd13:int32`; `nc14:int32`; `nb15:int32`;
     `na16:int32`; `nd17:int32`; `nc18:int32`; `nb19:int32`;
     `na20:int32`; `nd21:int32`; `nc22:int32`; `nb23:int32`;
     `na24:int32`; `nd25:int32`; `nc26:int32`; `nb27:int32`;
     `na28:int32`; `nd29:int32`; `nc30:int32`; `nb31:int32`]
    MD5_COMPRESS_32_G_VALUES) THEN
  ANTS_TAC THENL [POP_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MD5_G_LET_TO_EL_4WAY: bridges TEST_R1_R2_R3's let-form post (4 RAX..RDX   *)
(* equations) to EL i (md5_compress 32 ... [a;b;c;d]) form for i = 0,1,2,3. *)
(* Used in MD5_BLOCK_BODY_TEST_R1_R2_R3 segment-1 SUB_T3.                    *)
(*                                                                            *)
(* The helper body uses interleaved ONCE_DEPTH_CONV let_CONV + ABBREV_TAC    *)
(* (32 step pairs) instead of bulk DEPTH_CONV let_CONV. The interleaved      *)
(* recipe keeps peak RSS under ~3 GB (vs >85 GB for the bulk approach on     *)
(* the same 32-let chain) — see session-044 advisor analysis.                *)
(* ------------------------------------------------------------------------- *)

let MD5_G_LET_TO_EL_4WAY = prove
 (`!(s:x86state) (a:int32) b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
        (read RAX s =
           word_zx
            (
            let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
            let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
            let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
            let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
            let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
            let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
            let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
            let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
            let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
            let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
            let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
            let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
            let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
            let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
            let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
            let nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22) in
            let na16 = word_add nb15 (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5) in
            let nd17 = word_add na16 (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9) in
            let nc18 = word_add nd17 (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14) in
            let nb19 = word_add nc18 (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
            let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
            let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
            let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
            let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
            let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
            let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
            let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
            let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
            let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
            na28)) /\
        (read RBX s =
           word_zx
            (
            let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
            let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
            let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
            let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
            let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
            let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
            let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
            let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
            let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
            let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
            let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
            let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
            let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
            let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
            let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
            let nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22) in
            let na16 = word_add nb15 (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5) in
            let nd17 = word_add na16 (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9) in
            let nc18 = word_add nd17 (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14) in
            let nb19 = word_add nc18 (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
            let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
            let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
            let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
            let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
            let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
            let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
            let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
            let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
            let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
            let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
            let nc30 = word_add nd29 (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14) in
            let nb31 = word_add nc30 (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))) 20) in
            nb31)) /\
        (read RCX s =
           word_zx
            (
            let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
            let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
            let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
            let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
            let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
            let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
            let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
            let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
            let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
            let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
            let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
            let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
            let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
            let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
            let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
            let nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22) in
            let na16 = word_add nb15 (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5) in
            let nd17 = word_add na16 (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9) in
            let nc18 = word_add nd17 (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14) in
            let nb19 = word_add nc18 (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
            let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
            let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
            let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
            let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
            let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
            let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
            let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
            let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
            let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
            let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
            let nc30 = word_add nd29 (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14) in
            nc30)) /\
        (read RDX s =
           word_zx
            (
            let na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7) in
            let nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12) in
            let nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17) in
            let nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22) in
            let na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7) in
            let nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12) in
            let nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17) in
            let nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22) in
            let na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7) in
            let nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12) in
            let nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17) in
            let nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22) in
            let na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7) in
            let nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12) in
            let nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17) in
            let nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22) in
            let na16 = word_add nb15 (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5) in
            let nd17 = word_add na16 (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9) in
            let nc18 = word_add nd17 (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14) in
            let nb19 = word_add nc18 (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
            let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
            let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
            let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
            let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
            let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
            let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
            let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
            let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
            let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
            let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
            nd29))
       ==>
        read RAX s = word_zx (EL 0 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
        read RBX s = word_zx (EL 1 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
        read RCX s = word_zx (EL 2 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
        read RDX s = word_zx (EL 3 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd1 = word_add na0 (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc2 = word_add nd1 (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb3 = word_add nc2 (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na4 = word_add nb3 (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd5 = word_add na4 (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc6 = word_add nd5 (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb7 = word_add nc6 (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na8 = word_add nb7 (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd9 = word_add na8 (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc10 = word_add nd9 (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb11 = word_add nc10 (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na12 = word_add nb11 (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd13 = word_add na12 (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc14 = word_add nd13 (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb15 = word_add nc14 (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na16 = word_add nb15 (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd17 = word_add na16 (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc18 = word_add nd17 (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb19 = word_add nc18 (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nc30 = word_add nd29 (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14)` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nb31 = word_add nc30 (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))) 20)` THEN
  MP_TAC(SPECL
    [`[w0:int32;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]:int32 list`;
     `a:int32`;`b:int32`;`c:int32`;`d:int32`;
     `w0:int32`;`w1:int32`;`w2:int32`;`w3:int32`;
     `w4:int32`;`w5:int32`;`w6:int32`;`w7:int32`;
     `w8:int32`;`w9:int32`;`w10:int32`;`w11:int32`;
     `w12:int32`;`w13:int32`;`w14:int32`;`w15:int32`;
     `na0:int32`;`nd1:int32`;`nc2:int32`;`nb3:int32`;
     `na4:int32`;`nd5:int32`;`nc6:int32`;`nb7:int32`;
     `na8:int32`;`nd9:int32`;`nc10:int32`;`nb11:int32`;
     `na12:int32`;`nd13:int32`;`nc14:int32`;`nb15:int32`;
     `na16:int32`;`nd17:int32`;`nc18:int32`;`nb19:int32`;
     `na20:int32`;`nd21:int32`;`nc22:int32`;`nb23:int32`;
     `na24:int32`;`nd25:int32`;`nc26:int32`;`nb27:int32`;
     `na28:int32`;`nd29:int32`;`nc30:int32`;`nb31:int32`]
    MD5_COMPRESS_32_G_EL_VALUES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH;ARITH] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      EXPAND_TAC "na0" THEN REFL_TAC;
      EXPAND_TAC "nd1" THEN REFL_TAC;
      EXPAND_TAC "nc2" THEN REFL_TAC;
      EXPAND_TAC "nb3" THEN REFL_TAC;
      EXPAND_TAC "na4" THEN REFL_TAC;
      EXPAND_TAC "nd5" THEN REFL_TAC;
      EXPAND_TAC "nc6" THEN REFL_TAC;
      EXPAND_TAC "nb7" THEN REFL_TAC;
      EXPAND_TAC "na8" THEN REFL_TAC;
      EXPAND_TAC "nd9" THEN REFL_TAC;
      EXPAND_TAC "nc10" THEN REFL_TAC;
      EXPAND_TAC "nb11" THEN REFL_TAC;
      EXPAND_TAC "na12" THEN REFL_TAC;
      EXPAND_TAC "nd13" THEN REFL_TAC;
      EXPAND_TAC "nc14" THEN REFL_TAC;
      EXPAND_TAC "nb15" THEN REFL_TAC;
      EXPAND_TAC "na16" THEN REFL_TAC;
      EXPAND_TAC "nd17" THEN REFL_TAC;
      EXPAND_TAC "nc18" THEN REFL_TAC;
      EXPAND_TAC "nb19" THEN REFL_TAC;
      EXPAND_TAC "na20" THEN REFL_TAC;
      EXPAND_TAC "nd21" THEN REFL_TAC;
      EXPAND_TAC "nc22" THEN REFL_TAC;
      EXPAND_TAC "nb23" THEN REFL_TAC;
      EXPAND_TAC "na24" THEN REFL_TAC;
      EXPAND_TAC "nd25" THEN REFL_TAC;
      EXPAND_TAC "nc26" THEN REFL_TAC;
      EXPAND_TAC "nb27" THEN REFL_TAC;
      EXPAND_TAC "na28" THEN REFL_TAC;
      EXPAND_TAC "nd29" THEN REFL_TAC;
      EXPAND_TAC "nc30" THEN REFL_TAC;
      EXPAND_TAC "nb31" THEN REFL_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MD5_G_LET_TO_EL_4WAY_V2: bridges TEST_R1_R2's let-form post (16-step      *)
(* G-only chain with EL-headed values) to EL i (md5_compress 32 W [a;b;c;d]) *)
(* form for i = 0,1,2,3.  Used in MD5_BLOCK_BODY_TEST_R1_R2_R3 segment-1     *)
(* SUB_T3.                                                                  *)
(*                                                                          *)
(* The proof internally introduces F-stage abbreviations na0..nb15 to       *)
(* derive md5_compress 16 W [a;b;c;d] = [na12;nb15;nc14;nd13] via            *)
(* MD5_COMPRESS_16_F_EL_VALUES, rewrites the EL_i (md5_compress 16 ...)      *)
(* heads in the ANTE chain, then introduces G-stage abbreviations           *)
(* na16..nb31 and applies MD5_COMPRESS_32_G_EL_VALUES.                      *)
(* ------------------------------------------------------------------------- *)

let MD5_G_LET_TO_EL_4WAY_V2 = prove
 (`!(s:x86state) (a:int32) b c d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15.
        (read RAX s =
         word_zx
          (
           let na16 = word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w1 (EL 16 md5_T))) 5) in
             let nd17 = word_add na16 (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w6 (EL 17 md5_T))) 9) in
             let nc18 = word_add nd17 (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w11 (EL 18 md5_T))) 14) in
             let nb19 = word_add nc18 (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
             let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
             let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
             let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
             let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
             let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
             let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
             let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
             let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
             let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
               na28)) /\
        (read RBX s =
         word_zx
          (
           let na16 = word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w1 (EL 16 md5_T))) 5) in
             let nd17 = word_add na16 (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w6 (EL 17 md5_T))) 9) in
             let nc18 = word_add nd17 (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w11 (EL 18 md5_T))) 14) in
             let nb19 = word_add nc18 (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
             let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
             let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
             let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
             let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
             let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
             let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
             let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
             let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
             let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
             let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
             let nc30 = word_add nd29 (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14) in
             let nb31 = word_add nc30 (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))) 20) in
               nb31)) /\
        (read RCX s =
         word_zx
          (
           let na16 = word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w1 (EL 16 md5_T))) 5) in
             let nd17 = word_add na16 (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w6 (EL 17 md5_T))) 9) in
             let nc18 = word_add nd17 (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w11 (EL 18 md5_T))) 14) in
             let nb19 = word_add nc18 (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
             let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
             let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
             let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
             let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
             let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
             let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
             let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
             let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
             let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
             let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
             let nc30 = word_add nd29 (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14) in
               nc30)) /\
        (read RDX s =
         word_zx
          (
           let na16 = word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w1 (EL 16 md5_T))) 5) in
             let nd17 = word_add na16 (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w6 (EL 17 md5_T))) 9) in
             let nc18 = word_add nd17 (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])))) (word_add w11 (EL 18 md5_T))) 14) in
             let nb19 = word_add nc18 (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20) in
             let na20 = word_add nb19 (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5) in
             let nd21 = word_add na20 (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9) in
             let nc22 = word_add nd21 (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14) in
             let nb23 = word_add nc22 (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20) in
             let na24 = word_add nb23 (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5) in
             let nd25 = word_add na24 (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9) in
             let nc26 = word_add nd25 (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14) in
             let nb27 = word_add nc26 (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20) in
             let na28 = word_add nb27 (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5) in
             let nd29 = word_add na28 (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9) in
               nd29))
       ==> read RAX s = word_zx (EL 0 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RBX s = word_zx (EL 1 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RCX s = word_zx (EL 2 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
           read RDX s = word_zx (EL 3 (md5_compress 32 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `na0 = word_add (b:int32) (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))) 7)` THEN
  ABBREV_TAC `nd1 = word_add (na0:int32) (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))) 12)` THEN
  ABBREV_TAC `nc2 = word_add (nd1:int32) (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))) 17)` THEN
  ABBREV_TAC `nb3 = word_add (nc2:int32) (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))) 22)` THEN
  ABBREV_TAC `na4 = word_add (nb3:int32) (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))) 7)` THEN
  ABBREV_TAC `nd5 = word_add (na4:int32) (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))) 12)` THEN
  ABBREV_TAC `nc6 = word_add (nd5:int32) (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))) 17)` THEN
  ABBREV_TAC `nb7 = word_add (nc6:int32) (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))) 22)` THEN
  ABBREV_TAC `na8 = word_add (nb7:int32) (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))) 7)` THEN
  ABBREV_TAC `nd9 = word_add (na8:int32) (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))) 12)` THEN
  ABBREV_TAC `nc10 = word_add (nd9:int32) (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))) 17)` THEN
  ABBREV_TAC `nb11 = word_add (nc10:int32) (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))) 22)` THEN
  ABBREV_TAC `na12 = word_add (nb11:int32) (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))) 7)` THEN
  ABBREV_TAC `nd13 = word_add (na12:int32) (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))) 12)` THEN
  ABBREV_TAC `nc14 = word_add (nd13:int32) (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))) 17)` THEN
  ABBREV_TAC `nb15 = word_add (nc14:int32) (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))) 22)` THEN
  SUBGOAL_THEN
   `EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]) = na12 /\
    EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]) = nb15 /\
    EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]) = nc14 /\
    EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]) = nd13`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL
      [`[w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]:int32 list`;
       `a:int32`;`b:int32`;`c:int32`;`d:int32`;
       `w0:int32`;`w1:int32`;`w2:int32`;`w3:int32`;
       `w4:int32`;`w5:int32`;`w6:int32`;`w7:int32`;
       `w8:int32`;`w9:int32`;`w10:int32`;`w11:int32`;
       `w12:int32`;`w13:int32`;`w14:int32`;`w15:int32`;
       `na0:int32`;`nd1:int32`;`nc2:int32`;`nb3:int32`;
       `na4:int32`;`nd5:int32`;`nc6:int32`;`nb7:int32`;
       `na8:int32`;`nd9:int32`;`nc10:int32`;`nb11:int32`;
       `na12:int32`;`nd13:int32`;`nc14:int32`;`nb15:int32`]
      MD5_COMPRESS_16_F_EL_VALUES) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LENGTH;ARITH] THEN
      REPEAT CONJ_TAC THENL
       [
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      EXPAND_TAC "na0" THEN REFL_TAC;
      EXPAND_TAC "nd1" THEN REFL_TAC;
      EXPAND_TAC "nc2" THEN REFL_TAC;
      EXPAND_TAC "nb3" THEN REFL_TAC;
      EXPAND_TAC "na4" THEN REFL_TAC;
      EXPAND_TAC "nd5" THEN REFL_TAC;
      EXPAND_TAC "nc6" THEN REFL_TAC;
      EXPAND_TAC "nb7" THEN REFL_TAC;
      EXPAND_TAC "na8" THEN REFL_TAC;
      EXPAND_TAC "nd9" THEN REFL_TAC;
      EXPAND_TAC "nc10" THEN REFL_TAC;
      EXPAND_TAC "nb11" THEN REFL_TAC;
      EXPAND_TAC "na12" THEN REFL_TAC;
      EXPAND_TAC "nd13" THEN REFL_TAC;
      EXPAND_TAC "nc14" THEN REFL_TAC;
      EXPAND_TAC "nb15" THEN REFL_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `na16 = word_add (nb15:int32) (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))) 5)` THEN
  ABBREV_TAC `nd17 = word_add (na16:int32) (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))) 9)` THEN
  ABBREV_TAC `nc18 = word_add (nd17:int32) (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))) 14)` THEN
  ABBREV_TAC `nb19 = word_add (nc18:int32) (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))) 20)` THEN
  ABBREV_TAC `na20 = word_add (nb19:int32) (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))) 5)` THEN
  ABBREV_TAC `nd21 = word_add (na20:int32) (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))) 9)` THEN
  ABBREV_TAC `nc22 = word_add (nd21:int32) (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))) 14)` THEN
  ABBREV_TAC `nb23 = word_add (nc22:int32) (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))) 20)` THEN
  ABBREV_TAC `na24 = word_add (nb23:int32) (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))) 5)` THEN
  ABBREV_TAC `nd25 = word_add (na24:int32) (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))) 9)` THEN
  ABBREV_TAC `nc26 = word_add (nd25:int32) (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))) 14)` THEN
  ABBREV_TAC `nb27 = word_add (nc26:int32) (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))) 20)` THEN
  ABBREV_TAC `na28 = word_add (nb27:int32) (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))) 5)` THEN
  ABBREV_TAC `nd29 = word_add (na28:int32) (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))) 9)` THEN
  ABBREV_TAC `nc30 = word_add (nd29:int32) (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))) 14)` THEN
  ABBREV_TAC `nb31 = word_add (nc30:int32) (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))) 20)` THEN
  MP_TAC(SPECL
    [`[w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15]:int32 list`;
     `a:int32`;`b:int32`;`c:int32`;`d:int32`;
     `w0:int32`;`w1:int32`;`w2:int32`;`w3:int32`;
     `w4:int32`;`w5:int32`;`w6:int32`;`w7:int32`;
     `w8:int32`;`w9:int32`;`w10:int32`;`w11:int32`;
     `w12:int32`;`w13:int32`;`w14:int32`;`w15:int32`;
     `na0:int32`;`nd1:int32`;`nc2:int32`;`nb3:int32`;
     `na4:int32`;`nd5:int32`;`nc6:int32`;`nb7:int32`;
     `na8:int32`;`nd9:int32`;`nc10:int32`;`nb11:int32`;
     `na12:int32`;`nd13:int32`;`nc14:int32`;`nb15:int32`;
     `na16:int32`;`nd17:int32`;`nc18:int32`;`nb19:int32`;
     `na20:int32`;`nd21:int32`;`nc22:int32`;`nb23:int32`;
     `na24:int32`;`nd25:int32`;`nc26:int32`;`nb27:int32`;
     `na28:int32`;`nd29:int32`;`nc30:int32`;`nb31:int32`]
    MD5_COMPRESS_32_G_EL_VALUES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH;ARITH] THEN
    REPEAT CONJ_TAC THENL
     [
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC(RAND_CONV EL_CONV) THEN REFL_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Spec-form retrofit (rounds 1-3): md5_compress 48 W [a;b;c;d] =             *)
(*                               [na44; nb47; nc46; nd45].                   *)
(*                                                                            *)
(* Phase-9 prep round-3 bridge. Truncated 48-step variant of                  *)
(* MD5_COMPRESS_64_VALUES. Each per-step na/nd/nc/nb is bound to its          *)
(* standard MD5 update formula using the round-1 selector md5_F (steps 0..15),*)
(* the round-2 selector md5_G (steps 16..31), and the round-3 selector md5_H *)
(* (steps 32..47). The conclusion gives the cyclic rotation result after 48   *)
(* rounds.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MD5_COMPRESS_48_H_VALUES = prove
 (`!(W:int32 list) (a:int32) b c d
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        na0 nd1 nc2 nb3 na4 nd5 nc6 nb7
        na8 nd9 nc10 nb11 na12 nd13 nc14 nb15
        na16 nd17 nc18 nb19 na20 nd21 nc22 nb23
        na24 nd25 nc26 nb27 na28 nd29 nc30 nb31
        na32 nd33 nc34 nb35 na36 nd37 nc38 nb39
        na40 nd41 nc42 nb43 na44 nd45 nc46 nb47.
        LENGTH W = 16 /\
        w0 = EL 0 W /\
        w1 = EL 1 W /\
        w2 = EL 2 W /\
        w3 = EL 3 W /\
        w4 = EL 4 W /\
        w5 = EL 5 W /\
        w6 = EL 6 W /\
        w7 = EL 7 W /\
        w8 = EL 8 W /\
        w9 = EL 9 W /\
        w10 = EL 10 W /\
        w11 = EL 11 W /\
        w12 = EL 12 W /\
        w13 = EL 13 W /\
        w14 = EL 14 W /\
        w15 = EL 15 W /\
        na0 = word_add b
               (word_rol (word_add (word_add a (md5_F b c d))
                                   (word_add w0 (EL 0 md5_T)))
                         7) /\
        nd1 = word_add na0
               (word_rol (word_add (word_add d (md5_F na0 b c))
                                   (word_add w1 (EL 1 md5_T)))
                         12) /\
        nc2 = word_add nd1
               (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                   (word_add w2 (EL 2 md5_T)))
                         17) /\
        nb3 = word_add nc2
               (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                   (word_add w3 (EL 3 md5_T)))
                         22) /\
        na4 = word_add nb3
               (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                   (word_add w4 (EL 4 md5_T)))
                         7) /\
        nd5 = word_add na4
               (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                   (word_add w5 (EL 5 md5_T)))
                         12) /\
        nc6 = word_add nd5
               (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                   (word_add w6 (EL 6 md5_T)))
                         17) /\
        nb7 = word_add nc6
               (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                   (word_add w7 (EL 7 md5_T)))
                         22) /\
        na8 = word_add nb7
               (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                   (word_add w8 (EL 8 md5_T)))
                         7) /\
        nd9 = word_add na8
               (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                   (word_add w9 (EL 9 md5_T)))
                         12) /\
        nc10 = word_add nd9
               (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                   (word_add w10 (EL 10 md5_T)))
                         17) /\
        nb11 = word_add nc10
               (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                   (word_add w11 (EL 11 md5_T)))
                         22) /\
        na12 = word_add nb11
               (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                   (word_add w12 (EL 12 md5_T)))
                         7) /\
        nd13 = word_add na12
               (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                   (word_add w13 (EL 13 md5_T)))
                         12) /\
        nc14 = word_add nd13
               (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                   (word_add w14 (EL 14 md5_T)))
                         17) /\
        nb15 = word_add nc14
               (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                   (word_add w15 (EL 15 md5_T)))
                         22) /\
        na16 = word_add nb15
               (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13))
                                   (word_add w1 (EL 16 md5_T)))
                         5) /\
        nd17 = word_add na16
               (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14))
                                   (word_add w6 (EL 17 md5_T)))
                         9) /\
        nc18 = word_add nd17
               (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15))
                                   (word_add w11 (EL 18 md5_T)))
                         14) /\
        nb19 = word_add nc18
               (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16))
                                   (word_add w0 (EL 19 md5_T)))
                         20) /\
        na20 = word_add nb19
               (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                   (word_add w5 (EL 20 md5_T)))
                         5) /\
        nd21 = word_add na20
               (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                   (word_add w10 (EL 21 md5_T)))
                         9) /\
        nc22 = word_add nd21
               (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                   (word_add w15 (EL 22 md5_T)))
                         14) /\
        nb23 = word_add nc22
               (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                   (word_add w4 (EL 23 md5_T)))
                         20) /\
        na24 = word_add nb23
               (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                   (word_add w9 (EL 24 md5_T)))
                         5) /\
        nd25 = word_add na24
               (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                   (word_add w14 (EL 25 md5_T)))
                         9) /\
        nc26 = word_add nd25
               (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                   (word_add w3 (EL 26 md5_T)))
                         14) /\
        nb27 = word_add nc26
               (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                   (word_add w8 (EL 27 md5_T)))
                         20) /\
        na28 = word_add nb27
               (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                   (word_add w13 (EL 28 md5_T)))
                         5) /\
        nd29 = word_add na28
               (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                   (word_add w2 (EL 29 md5_T)))
                         9) /\
        nc30 = word_add nd29
               (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                   (word_add w7 (EL 30 md5_T)))
                         14) /\
        nb31 = word_add nc30
               (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                   (word_add w12 (EL 31 md5_T)))
                         20) /\
        na32 = word_add nb31
               (word_rol (word_add (word_add na28 (md5_H nb31 nc30 nd29))
                                   (word_add w5 (EL 32 md5_T)))
                         4) /\
        nd33 = word_add na32
               (word_rol (word_add (word_add nd29 (md5_H na32 nb31 nc30))
                                   (word_add w8 (EL 33 md5_T)))
                         11) /\
        nc34 = word_add nd33
               (word_rol (word_add (word_add nc30 (md5_H nd33 na32 nb31))
                                   (word_add w11 (EL 34 md5_T)))
                         16) /\
        nb35 = word_add nc34
               (word_rol (word_add (word_add nb31 (md5_H nc34 nd33 na32))
                                   (word_add w14 (EL 35 md5_T)))
                         23) /\
        na36 = word_add nb35
               (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33))
                                   (word_add w1 (EL 36 md5_T)))
                         4) /\
        nd37 = word_add na36
               (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34))
                                   (word_add w4 (EL 37 md5_T)))
                         11) /\
        nc38 = word_add nd37
               (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35))
                                   (word_add w7 (EL 38 md5_T)))
                         16) /\
        nb39 = word_add nc38
               (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36))
                                   (word_add w10 (EL 39 md5_T)))
                         23) /\
        na40 = word_add nb39
               (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37))
                                   (word_add w13 (EL 40 md5_T)))
                         4) /\
        nd41 = word_add na40
               (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38))
                                   (word_add w0 (EL 41 md5_T)))
                         11) /\
        nc42 = word_add nd41
               (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39))
                                   (word_add w3 (EL 42 md5_T)))
                         16) /\
        nb43 = word_add nc42
               (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40))
                                   (word_add w6 (EL 43 md5_T)))
                         23) /\
        na44 = word_add nb43
               (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41))
                                   (word_add w9 (EL 44 md5_T)))
                         4) /\
        nd45 = word_add na44
               (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42))
                                   (word_add w12 (EL 45 md5_T)))
                         11) /\
        nc46 = word_add nd45
               (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43))
                                   (word_add w15 (EL 46 md5_T)))
                         16) /\
        nb47 = word_add nc46
               (word_rol (word_add (word_add nb43 (md5_H nc46 nd45 na44))
                                   (word_add w2 (EL 47 md5_T)))
                         23)
        ==> md5_compress 48 W [a;b;c;d] =
            [na44; nb47; nc46; nd45]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `48 = 47 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `47 = 46 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `46 = 45 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `45 = 44 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `44 = 43 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `43 = 42 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `42 = 41 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `41 = 40 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `40 = 39 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `39 = 38 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `38 = 37 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `37 = 36 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `36 = 35 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `35 = 34 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `34 = 33 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `33 = 32 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `32 = 31 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `31 = 30 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `30 = 29 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `29 = 28 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `28 = 27 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `27 = 26 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `26 = 25 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `25 = 24 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `24 = 23 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `23 = 22 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `22 = 21 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `21 = 20 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `20 = 19 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `19 = 18 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `18 = 17 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `17 = 16 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 = 15 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `15 = 14 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `14 = 13 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `13 = 12 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `12 = 11 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `11 = 10 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `10 = 9 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `9 = 8 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `8 = 7 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `7 = 6 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `6 = 5 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `5 = 4 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `4 = 3 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN REWRITE_TAC[md5_compress] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  (* Round 0 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (a:int32)
             (word_add (md5_F b c d) (word_add (EL 0 W) (EL 0 md5_T))) =
    word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na0:int32 =
    word_add b
     (word_rol (word_add (word_add a (md5_F b c d)) (word_add w0 (EL 0 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 1 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (d:int32)
             (word_add (md5_F na0 b c) (word_add (EL 1 W) (EL 1 md5_T))) =
    word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd1:int32 =
    word_add na0
     (word_rol (word_add (word_add d (md5_F na0 b c)) (word_add w1 (EL 1 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 2 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (c:int32)
             (word_add (md5_F nd1 na0 b) (word_add (EL 2 W) (EL 2 md5_T))) =
    word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc2:int32 =
    word_add nd1
     (word_rol (word_add (word_add c (md5_F nd1 na0 b)) (word_add w2 (EL 2 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 3 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (b:int32)
             (word_add (md5_F nc2 nd1 na0) (word_add (EL 3 W) (EL 3 md5_T))) =
    word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb3:int32 =
    word_add nc2
     (word_rol (word_add (word_add b (md5_F nc2 nd1 na0)) (word_add w3 (EL 3 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 4 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na0:int32)
             (word_add (md5_F nb3 nc2 nd1) (word_add (EL 4 W) (EL 4 md5_T))) =
    word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na4:int32 =
    word_add nb3
     (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1)) (word_add w4 (EL 4 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 5 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd1:int32)
             (word_add (md5_F na4 nb3 nc2) (word_add (EL 5 W) (EL 5 md5_T))) =
    word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd5:int32 =
    word_add na4
     (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2)) (word_add w5 (EL 5 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 6 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc2:int32)
             (word_add (md5_F nd5 na4 nb3) (word_add (EL 6 W) (EL 6 md5_T))) =
    word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc6:int32 =
    word_add nd5
     (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3)) (word_add w6 (EL 6 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 7 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb3:int32)
             (word_add (md5_F nc6 nd5 na4) (word_add (EL 7 W) (EL 7 md5_T))) =
    word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb7:int32 =
    word_add nc6
     (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4)) (word_add w7 (EL 7 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 8 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na4:int32)
             (word_add (md5_F nb7 nc6 nd5) (word_add (EL 8 W) (EL 8 md5_T))) =
    word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na8:int32 =
    word_add nb7
     (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5)) (word_add w8 (EL 8 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 9 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd5:int32)
             (word_add (md5_F na8 nb7 nc6) (word_add (EL 9 W) (EL 9 md5_T))) =
    word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd9:int32 =
    word_add na8
     (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6)) (word_add w9 (EL 9 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 10 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc6:int32)
             (word_add (md5_F nd9 na8 nb7) (word_add (EL 10 W) (EL 10 md5_T))) =
    word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc10:int32 =
    word_add nd9
     (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7)) (word_add w10 (EL 10 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 11 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb7:int32)
             (word_add (md5_F nc10 nd9 na8) (word_add (EL 11 W) (EL 11 md5_T))) =
    word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb11:int32 =
    word_add nc10
     (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8)) (word_add w11 (EL 11 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 12 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na8:int32)
             (word_add (md5_F nb11 nc10 nd9) (word_add (EL 12 W) (EL 12 md5_T))) =
    word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na12:int32 =
    word_add nb11
     (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9)) (word_add w12 (EL 12 md5_T)))
               7)`
   (SUBST1_TAC o SYM) THEN
  (* Round 13 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd9:int32)
             (word_add (md5_F na12 nb11 nc10) (word_add (EL 13 W) (EL 13 md5_T))) =
    word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd13:int32 =
    word_add na12
     (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10)) (word_add w13 (EL 13 md5_T)))
               12)`
   (SUBST1_TAC o SYM) THEN
  (* Round 14 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc10:int32)
             (word_add (md5_F nd13 na12 nb11) (word_add (EL 14 W) (EL 14 md5_T))) =
    word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc14:int32 =
    word_add nd13
     (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11)) (word_add w14 (EL 14 md5_T)))
               17)`
   (SUBST1_TAC o SYM) THEN
  (* Round 15 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb11:int32)
             (word_add (md5_F nc14 nd13 na12) (word_add (EL 15 W) (EL 15 md5_T))) =
    word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb15:int32 =
    word_add nc14
     (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12)) (word_add w15 (EL 15 md5_T)))
               22)`
   (SUBST1_TAC o SYM) THEN
  (* Round 16 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na12:int32)
             (word_add (md5_G nb15 nc14 nd13) (word_add (EL 1 W) (EL 16 md5_T))) =
    word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na16:int32 =
    word_add nb15
     (word_rol (word_add (word_add na12 (md5_G nb15 nc14 nd13)) (word_add w1 (EL 16 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 17 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd13:int32)
             (word_add (md5_G na16 nb15 nc14) (word_add (EL 6 W) (EL 17 md5_T))) =
    word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd17:int32 =
    word_add na16
     (word_rol (word_add (word_add nd13 (md5_G na16 nb15 nc14)) (word_add w6 (EL 17 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 18 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc14:int32)
             (word_add (md5_G nd17 na16 nb15) (word_add (EL 11 W) (EL 18 md5_T))) =
    word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc18:int32 =
    word_add nd17
     (word_rol (word_add (word_add nc14 (md5_G nd17 na16 nb15)) (word_add w11 (EL 18 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 19 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb15:int32)
             (word_add (md5_G nc18 nd17 na16) (word_add (EL 0 W) (EL 19 md5_T))) =
    word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb19:int32 =
    word_add nc18
     (word_rol (word_add (word_add nb15 (md5_G nc18 nd17 na16)) (word_add w0 (EL 19 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 20 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na16:int32)
             (word_add (md5_G nb19 nc18 nd17) (word_add (EL 5 W) (EL 20 md5_T))) =
    word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na20:int32 =
    word_add nb19
     (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17)) (word_add w5 (EL 20 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 21 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd17:int32)
             (word_add (md5_G na20 nb19 nc18) (word_add (EL 10 W) (EL 21 md5_T))) =
    word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd21:int32 =
    word_add na20
     (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18)) (word_add w10 (EL 21 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 22 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc18:int32)
             (word_add (md5_G nd21 na20 nb19) (word_add (EL 15 W) (EL 22 md5_T))) =
    word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc22:int32 =
    word_add nd21
     (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19)) (word_add w15 (EL 22 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 23 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb19:int32)
             (word_add (md5_G nc22 nd21 na20) (word_add (EL 4 W) (EL 23 md5_T))) =
    word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb23:int32 =
    word_add nc22
     (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20)) (word_add w4 (EL 23 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 24 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na20:int32)
             (word_add (md5_G nb23 nc22 nd21) (word_add (EL 9 W) (EL 24 md5_T))) =
    word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na24:int32 =
    word_add nb23
     (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21)) (word_add w9 (EL 24 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 25 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd21:int32)
             (word_add (md5_G na24 nb23 nc22) (word_add (EL 14 W) (EL 25 md5_T))) =
    word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd25:int32 =
    word_add na24
     (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22)) (word_add w14 (EL 25 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 26 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc22:int32)
             (word_add (md5_G nd25 na24 nb23) (word_add (EL 3 W) (EL 26 md5_T))) =
    word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc26:int32 =
    word_add nd25
     (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23)) (word_add w3 (EL 26 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 27 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb23:int32)
             (word_add (md5_G nc26 nd25 na24) (word_add (EL 8 W) (EL 27 md5_T))) =
    word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb27:int32 =
    word_add nc26
     (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24)) (word_add w8 (EL 27 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 28 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na24:int32)
             (word_add (md5_G nb27 nc26 nd25) (word_add (EL 13 W) (EL 28 md5_T))) =
    word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na28:int32 =
    word_add nb27
     (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25)) (word_add w13 (EL 28 md5_T)))
               5)`
   (SUBST1_TAC o SYM) THEN
  (* Round 29 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd25:int32)
             (word_add (md5_G na28 nb27 nc26) (word_add (EL 2 W) (EL 29 md5_T))) =
    word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd29:int32 =
    word_add na28
     (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26)) (word_add w2 (EL 29 md5_T)))
               9)`
   (SUBST1_TAC o SYM) THEN
  (* Round 30 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc26:int32)
             (word_add (md5_G nd29 na28 nb27) (word_add (EL 7 W) (EL 30 md5_T))) =
    word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc30:int32 =
    word_add nd29
     (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27)) (word_add w7 (EL 30 md5_T)))
               14)`
   (SUBST1_TAC o SYM) THEN
  (* Round 31 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb27:int32)
             (word_add (md5_G nc30 nd29 na28) (word_add (EL 12 W) (EL 31 md5_T))) =
    word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb31:int32 =
    word_add nc30
     (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28)) (word_add w12 (EL 31 md5_T)))
               20)`
   (SUBST1_TAC o SYM) THEN
  (* Round 32 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na28:int32)
             (word_add (md5_H nb31 nc30 nd29) (word_add (EL 5 W) (EL 32 md5_T))) =
    word_add (word_add na28 (md5_H nb31 nc30 nd29)) (word_add w5 (EL 32 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na32:int32 =
    word_add nb31
     (word_rol (word_add (word_add na28 (md5_H nb31 nc30 nd29)) (word_add w5 (EL 32 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 33 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd29:int32)
             (word_add (md5_H na32 nb31 nc30) (word_add (EL 8 W) (EL 33 md5_T))) =
    word_add (word_add nd29 (md5_H na32 nb31 nc30)) (word_add w8 (EL 33 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd33:int32 =
    word_add na32
     (word_rol (word_add (word_add nd29 (md5_H na32 nb31 nc30)) (word_add w8 (EL 33 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 34 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc30:int32)
             (word_add (md5_H nd33 na32 nb31) (word_add (EL 11 W) (EL 34 md5_T))) =
    word_add (word_add nc30 (md5_H nd33 na32 nb31)) (word_add w11 (EL 34 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc34:int32 =
    word_add nd33
     (word_rol (word_add (word_add nc30 (md5_H nd33 na32 nb31)) (word_add w11 (EL 34 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 35 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb31:int32)
             (word_add (md5_H nc34 nd33 na32) (word_add (EL 14 W) (EL 35 md5_T))) =
    word_add (word_add nb31 (md5_H nc34 nd33 na32)) (word_add w14 (EL 35 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb35:int32 =
    word_add nc34
     (word_rol (word_add (word_add nb31 (md5_H nc34 nd33 na32)) (word_add w14 (EL 35 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 36 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na32:int32)
             (word_add (md5_H nb35 nc34 nd33) (word_add (EL 1 W) (EL 36 md5_T))) =
    word_add (word_add na32 (md5_H nb35 nc34 nd33)) (word_add w1 (EL 36 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na36:int32 =
    word_add nb35
     (word_rol (word_add (word_add na32 (md5_H nb35 nc34 nd33)) (word_add w1 (EL 36 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 37 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd33:int32)
             (word_add (md5_H na36 nb35 nc34) (word_add (EL 4 W) (EL 37 md5_T))) =
    word_add (word_add nd33 (md5_H na36 nb35 nc34)) (word_add w4 (EL 37 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd37:int32 =
    word_add na36
     (word_rol (word_add (word_add nd33 (md5_H na36 nb35 nc34)) (word_add w4 (EL 37 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 38 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc34:int32)
             (word_add (md5_H nd37 na36 nb35) (word_add (EL 7 W) (EL 38 md5_T))) =
    word_add (word_add nc34 (md5_H nd37 na36 nb35)) (word_add w7 (EL 38 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc38:int32 =
    word_add nd37
     (word_rol (word_add (word_add nc34 (md5_H nd37 na36 nb35)) (word_add w7 (EL 38 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 39 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb35:int32)
             (word_add (md5_H nc38 nd37 na36) (word_add (EL 10 W) (EL 39 md5_T))) =
    word_add (word_add nb35 (md5_H nc38 nd37 na36)) (word_add w10 (EL 39 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb39:int32 =
    word_add nc38
     (word_rol (word_add (word_add nb35 (md5_H nc38 nd37 na36)) (word_add w10 (EL 39 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 40 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na36:int32)
             (word_add (md5_H nb39 nc38 nd37) (word_add (EL 13 W) (EL 40 md5_T))) =
    word_add (word_add na36 (md5_H nb39 nc38 nd37)) (word_add w13 (EL 40 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na40:int32 =
    word_add nb39
     (word_rol (word_add (word_add na36 (md5_H nb39 nc38 nd37)) (word_add w13 (EL 40 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 41 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd37:int32)
             (word_add (md5_H na40 nb39 nc38) (word_add (EL 0 W) (EL 41 md5_T))) =
    word_add (word_add nd37 (md5_H na40 nb39 nc38)) (word_add w0 (EL 41 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd41:int32 =
    word_add na40
     (word_rol (word_add (word_add nd37 (md5_H na40 nb39 nc38)) (word_add w0 (EL 41 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 42 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc38:int32)
             (word_add (md5_H nd41 na40 nb39) (word_add (EL 3 W) (EL 42 md5_T))) =
    word_add (word_add nc38 (md5_H nd41 na40 nb39)) (word_add w3 (EL 42 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc42:int32 =
    word_add nd41
     (word_rol (word_add (word_add nc38 (md5_H nd41 na40 nb39)) (word_add w3 (EL 42 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 43 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb39:int32)
             (word_add (md5_H nc42 nd41 na40) (word_add (EL 6 W) (EL 43 md5_T))) =
    word_add (word_add nb39 (md5_H nc42 nd41 na40)) (word_add w6 (EL 43 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb43:int32 =
    word_add nc42
     (word_rol (word_add (word_add nb39 (md5_H nc42 nd41 na40)) (word_add w6 (EL 43 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  (* Round 44 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (na40:int32)
             (word_add (md5_H nb43 nc42 nd41) (word_add (EL 9 W) (EL 44 md5_T))) =
    word_add (word_add na40 (md5_H nb43 nc42 nd41)) (word_add w9 (EL 44 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `na44:int32 =
    word_add nb43
     (word_rol (word_add (word_add na40 (md5_H nb43 nc42 nd41)) (word_add w9 (EL 44 md5_T)))
               4)`
   (SUBST1_TAC o SYM) THEN
  (* Round 45 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nd41:int32)
             (word_add (md5_H na44 nb43 nc42) (word_add (EL 12 W) (EL 45 md5_T))) =
    word_add (word_add nd41 (md5_H na44 nb43 nc42)) (word_add w12 (EL 45 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nd45:int32 =
    word_add na44
     (word_rol (word_add (word_add nd41 (md5_H na44 nb43 nc42)) (word_add w12 (EL 45 md5_T)))
               11)`
   (SUBST1_TAC o SYM) THEN
  (* Round 46 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nc42:int32)
             (word_add (md5_H nd45 na44 nb43) (word_add (EL 15 W) (EL 46 md5_T))) =
    word_add (word_add nc42 (md5_H nd45 na44 nb43)) (word_add w15 (EL 46 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nc46:int32 =
    word_add nd45
     (word_rol (word_add (word_add nc42 (md5_H nd45 na44 nb43)) (word_add w15 (EL 46 md5_T)))
               16)`
   (SUBST1_TAC o SYM) THEN
  (* Round 47 *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MD5_COMPRESS_ROUND_4LIST] THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[md5_round_function; md5_K; md5_S])) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EL_CONV)) THEN
  SUBGOAL_THEN
   `word_add (nb43:int32)
             (word_add (md5_H nc46 nd45 na44) (word_add (EL 2 W) (EL 47 md5_T))) =
    word_add (word_add nb43 (md5_H nc46 nd45 na44)) (word_add w2 (EL 47 md5_T))`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  UNDISCH_THEN
   `nb47:int32 =
    word_add nc46
     (word_rol (word_add (word_add nb43 (md5_H nc46 nd45 na44)) (word_add w2 (EL 47 md5_T)))
               23)`
   (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 prelude: 4-step snapshot MOV stretch from pc+40 to pc+52.          *)
(* The asm at .Lloop (offset 40 in tmc) saves the chaining state:             *)
(*   movl %eax, %r8d   ; movl %ebx, %r9d                                     *)
(*   movl %ecx, %r14d  ; movl %edx, %r15d                                    *)
(* Each is 3 bytes (4*3 = 12 bytes total), bringing us to pc+52 = ROUND1     *)
(* entry. The MOVs zero-extend EAX/EBX/ECX/EDX into R8/R9/R14/R15.           *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_BODY_PRELUDE = prove
 (`!pc data_ptr (a:int32) (b:int32) (c:int32) (d:int32).
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 40) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d)
             (\s. read RIP s = word(pc + 52) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read R8 s = word_zx a /\
                  read R9 s = word_zx b /\
                  read R14 s = word_zx c /\
                  read R15 s = word_zx d)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [R8; R9; R14; R15])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64;
           ARITH_RULE `32 <= 64`; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Phase 9 writeback: 4-step add-back from pc+2225 to pc+2237.                *)
(* The asm at lines 682..685 of md5_block_asm_data_order.S writes back        *)
(* the per-step ROUND4 outputs into the chaining state:                      *)
(*   addl %r8d, %eax   ; addl %r9d, %ebx                                     *)
(*   addl %r14d, %ecx  ; addl %r15d, %edx                                    *)
(* Each ADD is 3 bytes (4*3 = 12 bytes total). EAX/EBX/ECX/EDX hold the      *)
(* zx of na60/nb63/nc62/nd61; R8/R9/R14/R15 hold the zx of the original     *)
(* a/b/c/d. After the ADDs, EAX = zx(na60+a), etc.                          *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_BODY_WRITEBACK = prove
 (`!pc data_ptr (a:int32) (b:int32) (c:int32) (d:int32)
        (a4:int32) (b4:int32) (c4:int32) (d4:int32).
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 2225) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a4 /\
                  read RBX s = word_zx b4 /\
                  read RCX s = word_zx c4 /\
                  read RDX s = word_zx d4 /\
                  read R8 s = word_zx a /\
                  read R9 s = word_zx b /\
                  read R14 s = word_zx c /\
                  read R15 s = word_zx d)
             (\s. read RIP s = word(pc + 2237) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx (word_add a4 a) /\
                  read RBX s = word_zx (word_add b4 b) /\
                  read RCX s = word_zx (word_add c4 c) /\
                  read RDX s = word_zx (word_add d4 d))
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64;
           ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* MD5_BLOCK_BODY_TEST_R1: validated PRELUDE+ROUND1 fragment for [pc+40,     *)
(* pc+569). Composes MD5_BLOCK_BODY_PRELUDE with MD5_ROUND1_CORRECT via a    *)
(* single ENSURES_SEQUENCE_TAC cut at pc+52. Post is in let-form (matches    *)
(* MD5_ROUND1_CORRECT's post directly), with R8/R9/R14/R15 carried through  *)
(* unchanged from PRELUDE. Smoke-tested loadable in session 026.            *)
(*                                                                           *)
(* This is a Phase-9 stepping stone: it covers PRELUDE+R1 of                 *)
(* MD5_BLOCK_BODY_CORRECT. The R1->R2 spec-form bridge (via                  *)
(* MD5_COMPRESS_16_F_VALUES) is deferred to a future session.                *)
(* ------------------------------------------------------------------------- *)

(* Test fragment: pc+40 to pc+569 (MD5_BLOCK_BODY_TEST_R1). *)

let MD5_BLOCK_BODY_TEST_R1 = prove
 (`!pc data_ptr (a:int32) (b:int32) (c:int32) (d:int32)
        (w0:int32) (w1:int32) (w2:int32) (w3:int32) (w4:int32)
        (w5:int32) (w6:int32) (w7:int32) (w8:int32) (w9:int32)
        (w10:int32) (w11:int32) (w12:int32) (w13:int32) (w14:int32) (w15:int32).
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 40) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 569) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (let na0 =
                          word_add b
                           (word_rol (word_add (word_add a (md5_F b c d))
                                               (word_add w0 (EL 0 md5_T)))
                                     7) in
                      let nd1 =
                          word_add na0
                           (word_rol (word_add (word_add d (md5_F na0 b c))
                                               (word_add w1 (EL 1 md5_T)))
                                     12) in
                      let nc2 =
                          word_add nd1
                           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                               (word_add w2 (EL 2 md5_T)))
                                     17) in
                      let nb3 =
                          word_add nc2
                           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                               (word_add w3 (EL 3 md5_T)))
                                     22) in
                      let na4 =
                          word_add nb3
                           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                               (word_add w4 (EL 4 md5_T)))
                                     7) in
                      let nd5 =
                          word_add na4
                           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                               (word_add w5 (EL 5 md5_T)))
                                     12) in
                      let nc6 =
                          word_add nd5
                           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                               (word_add w6 (EL 6 md5_T)))
                                     17) in
                      let nb7 =
                          word_add nc6
                           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                               (word_add w7 (EL 7 md5_T)))
                                     22) in
                      let na8 =
                          word_add nb7
                           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                               (word_add w8 (EL 8 md5_T)))
                                     7) in
                      let nd9 =
                          word_add na8
                           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                               (word_add w9 (EL 9 md5_T)))
                                     12) in
                      let nc10 =
                          word_add nd9
                           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                               (word_add w10 (EL 10 md5_T)))
                                     17) in
                      let nb11 =
                          word_add nc10
                           (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                               (word_add w11 (EL 11 md5_T)))
                                     22) in
                      let na12 =
                          word_add nb11
                           (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                               (word_add w12 (EL 12 md5_T)))
                                     7) in
                      na12) /\
                  read RBX s =
                    word_zx
                      (let na0 =
                          word_add b
                           (word_rol (word_add (word_add a (md5_F b c d))
                                               (word_add w0 (EL 0 md5_T)))
                                     7) in
                      let nd1 =
                          word_add na0
                           (word_rol (word_add (word_add d (md5_F na0 b c))
                                               (word_add w1 (EL 1 md5_T)))
                                     12) in
                      let nc2 =
                          word_add nd1
                           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                               (word_add w2 (EL 2 md5_T)))
                                     17) in
                      let nb3 =
                          word_add nc2
                           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                               (word_add w3 (EL 3 md5_T)))
                                     22) in
                      let na4 =
                          word_add nb3
                           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                               (word_add w4 (EL 4 md5_T)))
                                     7) in
                      let nd5 =
                          word_add na4
                           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                               (word_add w5 (EL 5 md5_T)))
                                     12) in
                      let nc6 =
                          word_add nd5
                           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                               (word_add w6 (EL 6 md5_T)))
                                     17) in
                      let nb7 =
                          word_add nc6
                           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                               (word_add w7 (EL 7 md5_T)))
                                     22) in
                      let na8 =
                          word_add nb7
                           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                               (word_add w8 (EL 8 md5_T)))
                                     7) in
                      let nd9 =
                          word_add na8
                           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                               (word_add w9 (EL 9 md5_T)))
                                     12) in
                      let nc10 =
                          word_add nd9
                           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                               (word_add w10 (EL 10 md5_T)))
                                     17) in
                      let nb11 =
                          word_add nc10
                           (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                               (word_add w11 (EL 11 md5_T)))
                                     22) in
                      let na12 =
                          word_add nb11
                           (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                               (word_add w12 (EL 12 md5_T)))
                                     7) in
                      let nd13 =
                          word_add na12
                           (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                               (word_add w13 (EL 13 md5_T)))
                                     12) in
                      let nc14 =
                          word_add nd13
                           (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                               (word_add w14 (EL 14 md5_T)))
                                     17) in
                      let nb15 =
                          word_add nc14
                           (word_rol (word_add (word_add nb11 (md5_F nc14 nd13 na12))
                                               (word_add w15 (EL 15 md5_T)))
                                     22) in
                      nb15) /\
                  read RCX s =
                    word_zx
                      (let na0 =
                          word_add b
                           (word_rol (word_add (word_add a (md5_F b c d))
                                               (word_add w0 (EL 0 md5_T)))
                                     7) in
                      let nd1 =
                          word_add na0
                           (word_rol (word_add (word_add d (md5_F na0 b c))
                                               (word_add w1 (EL 1 md5_T)))
                                     12) in
                      let nc2 =
                          word_add nd1
                           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                               (word_add w2 (EL 2 md5_T)))
                                     17) in
                      let nb3 =
                          word_add nc2
                           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                               (word_add w3 (EL 3 md5_T)))
                                     22) in
                      let na4 =
                          word_add nb3
                           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                               (word_add w4 (EL 4 md5_T)))
                                     7) in
                      let nd5 =
                          word_add na4
                           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                               (word_add w5 (EL 5 md5_T)))
                                     12) in
                      let nc6 =
                          word_add nd5
                           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                               (word_add w6 (EL 6 md5_T)))
                                     17) in
                      let nb7 =
                          word_add nc6
                           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                               (word_add w7 (EL 7 md5_T)))
                                     22) in
                      let na8 =
                          word_add nb7
                           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                               (word_add w8 (EL 8 md5_T)))
                                     7) in
                      let nd9 =
                          word_add na8
                           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                               (word_add w9 (EL 9 md5_T)))
                                     12) in
                      let nc10 =
                          word_add nd9
                           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                               (word_add w10 (EL 10 md5_T)))
                                     17) in
                      let nb11 =
                          word_add nc10
                           (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                               (word_add w11 (EL 11 md5_T)))
                                     22) in
                      let na12 =
                          word_add nb11
                           (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                               (word_add w12 (EL 12 md5_T)))
                                     7) in
                      let nd13 =
                          word_add na12
                           (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                               (word_add w13 (EL 13 md5_T)))
                                     12) in
                      let nc14 =
                          word_add nd13
                           (word_rol (word_add (word_add nc10 (md5_F nd13 na12 nb11))
                                               (word_add w14 (EL 14 md5_T)))
                                     17) in
                      nc14) /\
                  read RDX s =
                    word_zx
                      (let na0 =
                          word_add b
                           (word_rol (word_add (word_add a (md5_F b c d))
                                               (word_add w0 (EL 0 md5_T)))
                                     7) in
                      let nd1 =
                          word_add na0
                           (word_rol (word_add (word_add d (md5_F na0 b c))
                                               (word_add w1 (EL 1 md5_T)))
                                     12) in
                      let nc2 =
                          word_add nd1
                           (word_rol (word_add (word_add c (md5_F nd1 na0 b))
                                               (word_add w2 (EL 2 md5_T)))
                                     17) in
                      let nb3 =
                          word_add nc2
                           (word_rol (word_add (word_add b (md5_F nc2 nd1 na0))
                                               (word_add w3 (EL 3 md5_T)))
                                     22) in
                      let na4 =
                          word_add nb3
                           (word_rol (word_add (word_add na0 (md5_F nb3 nc2 nd1))
                                               (word_add w4 (EL 4 md5_T)))
                                     7) in
                      let nd5 =
                          word_add na4
                           (word_rol (word_add (word_add nd1 (md5_F na4 nb3 nc2))
                                               (word_add w5 (EL 5 md5_T)))
                                     12) in
                      let nc6 =
                          word_add nd5
                           (word_rol (word_add (word_add nc2 (md5_F nd5 na4 nb3))
                                               (word_add w6 (EL 6 md5_T)))
                                     17) in
                      let nb7 =
                          word_add nc6
                           (word_rol (word_add (word_add nb3 (md5_F nc6 nd5 na4))
                                               (word_add w7 (EL 7 md5_T)))
                                     22) in
                      let na8 =
                          word_add nb7
                           (word_rol (word_add (word_add na4 (md5_F nb7 nc6 nd5))
                                               (word_add w8 (EL 8 md5_T)))
                                     7) in
                      let nd9 =
                          word_add na8
                           (word_rol (word_add (word_add nd5 (md5_F na8 nb7 nc6))
                                               (word_add w9 (EL 9 md5_T)))
                                     12) in
                      let nc10 =
                          word_add nd9
                           (word_rol (word_add (word_add nc6 (md5_F nd9 na8 nb7))
                                               (word_add w10 (EL 10 md5_T)))
                                     17) in
                      let nb11 =
                          word_add nc10
                           (word_rol (word_add (word_add nb7 (md5_F nc10 nd9 na8))
                                               (word_add w11 (EL 11 md5_T)))
                                     22) in
                      let na12 =
                          word_add nb11
                           (word_rol (word_add (word_add na8 (md5_F nb11 nc10 nd9))
                                               (word_add w12 (EL 12 md5_T)))
                                     7) in
                      let nd13 =
                          word_add na12
                           (word_rol (word_add (word_add nd9 (md5_F na12 nb11 nc10))
                                               (word_add w13 (EL 13 md5_T)))
                                     12) in
                      nd13) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = read RDX s /\
                  read R8 s = word_zx (a:int32) /\
                  read R9 s = word_zx (b:int32) /\
                  read R14 s = word_zx (c:int32) /\
                  read R15 s = word_zx (d:int32) /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R8; R9; R10; R11; R12; R14; R15] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
ENSURES_SEQUENCE_TAC `pc + 52`
   `\s. read RSI s = data_ptr /\
        read RAX s = word_zx (a:int32) /\
        read RBX s = word_zx (b:int32) /\
        read RCX s = word_zx (c:int32) /\
        read RDX s = word_zx (d:int32) /\
        read R8 s = word_zx (a:int32) /\
        read R9 s = word_zx (b:int32) /\
        read R14 s = word_zx (c:int32) /\
        read R15 s = word_zx (d:int32) /\
        read (memory :> bytes32 data_ptr) s = w0 /\
        read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
        read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
        read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
        read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
        read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
        read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
        read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
        read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
        read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
        read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
        read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
        read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
        read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
        read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
        read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
CONJ_TAC THENL [
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`]
   MD5_BLOCK_BODY_PRELUDE) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]];
ALL_TAC] THEN
MP_TAC(SPECL
   [`pc:num`; `data_ptr:int64`;
    `a:int32`; `b:int32`; `c:int32`; `d:int32`;
    `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`;
    `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`; `w9:int32`;
    `w10:int32`; `w11:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`]
   MD5_ROUND1_CORRECT) THEN
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL];
REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MD5_BLOCK_BODY_TEST_R1_R2: PRELUDE + ROUND1 + ROUND2 fragment for         *)
(* [pc+40, pc+1185).  Composes MD5_BLOCK_BODY_TEST_R1 with                   *)
(* MD5_ROUND2_CORRECT via a single ENSURES_SEQUENCE_TAC cut at pc+569 in     *)
(* EL-form (using MD5_F_LET_TO_EL_4WAY bridge).                                *)
(* Phase-9 stepping stone toward MD5_BLOCK_BODY_CORRECT.                      *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCK_BODY_TEST_R1_R2 = prove
 (`!pc data_ptr (a:int32) (b:int32) (c:int32) (d:int32)
        (w0:int32) (w1:int32) (w2:int32) (w3:int32) (w4:int32)
        (w5:int32) (w6:int32) (w7:int32) (w8:int32) (w9:int32)
        (w10:int32) (w11:int32) (w12:int32) (w13:int32) (w14:int32) (w15:int32).
       nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                      (data_ptr:int64,64)
       ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (BUTLAST md5_block_asm_data_order_tmc) /\
                  read RIP s = word(pc + 40) /\
                  read RSI s = data_ptr /\
                  read RAX s = word_zx a /\
                  read RBX s = word_zx b /\
                  read RCX s = word_zx c /\
                  read RDX s = word_zx d /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (\s. read RIP s = word(pc + 1185) /\
                  read RSI s = data_ptr /\
                  read RAX s =
                    word_zx
                      (
                      let na16 =
                          word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))
                           (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w1 (EL 16 md5_T)))
                                     5) in
                      let nd17 =
                          word_add na16
                           (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w6 (EL 17 md5_T)))
                                     9) in
                      let nc18 =
                          word_add nd17
                           (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w11 (EL 18 md5_T)))
                                     14) in
                      let nb19 =
                          word_add nc18
                           (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16))
                                               (word_add w0 (EL 19 md5_T)))
                                     20) in
                      let na20 =
                          word_add nb19
                           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                               (word_add w5 (EL 20 md5_T)))
                                     5) in
                      let nd21 =
                          word_add na20
                           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                               (word_add w10 (EL 21 md5_T)))
                                     9) in
                      let nc22 =
                          word_add nd21
                           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                               (word_add w15 (EL 22 md5_T)))
                                     14) in
                      let nb23 =
                          word_add nc22
                           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                               (word_add w4 (EL 23 md5_T)))
                                     20) in
                      let na24 =
                          word_add nb23
                           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                               (word_add w9 (EL 24 md5_T)))
                                     5) in
                      let nd25 =
                          word_add na24
                           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                               (word_add w14 (EL 25 md5_T)))
                                     9) in
                      let nc26 =
                          word_add nd25
                           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                               (word_add w3 (EL 26 md5_T)))
                                     14) in
                      let nb27 =
                          word_add nc26
                           (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                               (word_add w8 (EL 27 md5_T)))
                                     20) in
                      let na28 =
                          word_add nb27
                           (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                               (word_add w13 (EL 28 md5_T)))
                                     5) in
                      na28
                       ) /\
                  read RBX s =
                    word_zx
                      (
                      let na16 =
                          word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))
                           (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w1 (EL 16 md5_T)))
                                     5) in
                      let nd17 =
                          word_add na16
                           (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w6 (EL 17 md5_T)))
                                     9) in
                      let nc18 =
                          word_add nd17
                           (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w11 (EL 18 md5_T)))
                                     14) in
                      let nb19 =
                          word_add nc18
                           (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16))
                                               (word_add w0 (EL 19 md5_T)))
                                     20) in
                      let na20 =
                          word_add nb19
                           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                               (word_add w5 (EL 20 md5_T)))
                                     5) in
                      let nd21 =
                          word_add na20
                           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                               (word_add w10 (EL 21 md5_T)))
                                     9) in
                      let nc22 =
                          word_add nd21
                           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                               (word_add w15 (EL 22 md5_T)))
                                     14) in
                      let nb23 =
                          word_add nc22
                           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                               (word_add w4 (EL 23 md5_T)))
                                     20) in
                      let na24 =
                          word_add nb23
                           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                               (word_add w9 (EL 24 md5_T)))
                                     5) in
                      let nd25 =
                          word_add na24
                           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                               (word_add w14 (EL 25 md5_T)))
                                     9) in
                      let nc26 =
                          word_add nd25
                           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                               (word_add w3 (EL 26 md5_T)))
                                     14) in
                      let nb27 =
                          word_add nc26
                           (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                               (word_add w8 (EL 27 md5_T)))
                                     20) in
                      let na28 =
                          word_add nb27
                           (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                               (word_add w13 (EL 28 md5_T)))
                                     5) in
                      let nd29 =
                          word_add na28
                           (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                               (word_add w2 (EL 29 md5_T)))
                                     9) in
                      let nc30 =
                          word_add nd29
                           (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                               (word_add w7 (EL 30 md5_T)))
                                     14) in
                      let nb31 =
                          word_add nc30
                           (word_rol (word_add (word_add nb27 (md5_G nc30 nd29 na28))
                                               (word_add w12 (EL 31 md5_T)))
                                     20) in
                      nb31
                       ) /\
                  read RCX s =
                    word_zx
                      (
                      let na16 =
                          word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))
                           (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w1 (EL 16 md5_T)))
                                     5) in
                      let nd17 =
                          word_add na16
                           (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w6 (EL 17 md5_T)))
                                     9) in
                      let nc18 =
                          word_add nd17
                           (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w11 (EL 18 md5_T)))
                                     14) in
                      let nb19 =
                          word_add nc18
                           (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16))
                                               (word_add w0 (EL 19 md5_T)))
                                     20) in
                      let na20 =
                          word_add nb19
                           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                               (word_add w5 (EL 20 md5_T)))
                                     5) in
                      let nd21 =
                          word_add na20
                           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                               (word_add w10 (EL 21 md5_T)))
                                     9) in
                      let nc22 =
                          word_add nd21
                           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                               (word_add w15 (EL 22 md5_T)))
                                     14) in
                      let nb23 =
                          word_add nc22
                           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                               (word_add w4 (EL 23 md5_T)))
                                     20) in
                      let na24 =
                          word_add nb23
                           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                               (word_add w9 (EL 24 md5_T)))
                                     5) in
                      let nd25 =
                          word_add na24
                           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                               (word_add w14 (EL 25 md5_T)))
                                     9) in
                      let nc26 =
                          word_add nd25
                           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                               (word_add w3 (EL 26 md5_T)))
                                     14) in
                      let nb27 =
                          word_add nc26
                           (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                               (word_add w8 (EL 27 md5_T)))
                                     20) in
                      let na28 =
                          word_add nb27
                           (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                               (word_add w13 (EL 28 md5_T)))
                                     5) in
                      let nd29 =
                          word_add na28
                           (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                               (word_add w2 (EL 29 md5_T)))
                                     9) in
                      let nc30 =
                          word_add nd29
                           (word_rol (word_add (word_add nc26 (md5_G nd29 na28 nb27))
                                               (word_add w7 (EL 30 md5_T)))
                                     14) in
                      nc30
                       ) /\
                  read RDX s =
                    word_zx
                      (
                      let na16 =
                          word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))
                           (word_rol (word_add (word_add (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w1 (EL 16 md5_T)))
                                     5) in
                      let nd17 =
                          word_add na16
                           (word_rol (word_add (word_add (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w6 (EL 17 md5_T)))
                                     9) in
                      let nc18 =
                          word_add nd17
                           (word_rol (word_add (word_add (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nd17 na16 (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]))))
                                               (word_add w11 (EL 18 md5_T)))
                                     14) in
                      let nb19 =
                          word_add nc18
                           (word_rol (word_add (word_add (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d])) (md5_G nc18 nd17 na16))
                                               (word_add w0 (EL 19 md5_T)))
                                     20) in
                      let na20 =
                          word_add nb19
                           (word_rol (word_add (word_add na16 (md5_G nb19 nc18 nd17))
                                               (word_add w5 (EL 20 md5_T)))
                                     5) in
                      let nd21 =
                          word_add na20
                           (word_rol (word_add (word_add nd17 (md5_G na20 nb19 nc18))
                                               (word_add w10 (EL 21 md5_T)))
                                     9) in
                      let nc22 =
                          word_add nd21
                           (word_rol (word_add (word_add nc18 (md5_G nd21 na20 nb19))
                                               (word_add w15 (EL 22 md5_T)))
                                     14) in
                      let nb23 =
                          word_add nc22
                           (word_rol (word_add (word_add nb19 (md5_G nc22 nd21 na20))
                                               (word_add w4 (EL 23 md5_T)))
                                     20) in
                      let na24 =
                          word_add nb23
                           (word_rol (word_add (word_add na20 (md5_G nb23 nc22 nd21))
                                               (word_add w9 (EL 24 md5_T)))
                                     5) in
                      let nd25 =
                          word_add na24
                           (word_rol (word_add (word_add nd21 (md5_G na24 nb23 nc22))
                                               (word_add w14 (EL 25 md5_T)))
                                     9) in
                      let nc26 =
                          word_add nd25
                           (word_rol (word_add (word_add nc22 (md5_G nd25 na24 nb23))
                                               (word_add w3 (EL 26 md5_T)))
                                     14) in
                      let nb27 =
                          word_add nc26
                           (word_rol (word_add (word_add nb23 (md5_G nc26 nd25 na24))
                                               (word_add w8 (EL 27 md5_T)))
                                     20) in
                      let na28 =
                          word_add nb27
                           (word_rol (word_add (word_add na24 (md5_G nb27 nc26 nd25))
                                               (word_add w13 (EL 28 md5_T)))
                                     5) in
                      let nd29 =
                          word_add na28
                           (word_rol (word_add (word_add nd25 (md5_G na28 nb27 nc26))
                                               (word_add w2 (EL 29 md5_T)))
                                     9) in
                      nd29
                       ) /\
                  read R10 s = (word_zx:int32->int64) (w0:int32) /\
                  read R11 s = read RDX s /\
                  read R12 s = read RDX s /\
                  read R8 s = word_zx (a:int32) /\
                  read R9 s = word_zx (b:int32) /\
                  read R14 s = word_zx (c:int32) /\
                  read R15 s = word_zx (d:int32) /\
                  read (memory :> bytes32 data_ptr) s = w0 /\
                  read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
                  read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
                  read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
                  read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
                  read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
                  read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
                  read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
                  read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
                  read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
                  read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
                  read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
                  read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
                  read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
                  read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
                  read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15)
             (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
              MAYCHANGE [RAX; RBX; RCX; RDX; R8; R9; R10; R11; R12; R14; R15] ,,
              MAYCHANGE SOME_FLAGS)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_SEQUENCE_TAC `pc + 569`
    `\s. read RSI s = data_ptr /\
         read RAX s = word_zx (EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
         read RBX s = word_zx (EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
         read RCX s = word_zx (EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
         read RDX s = word_zx (EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32) /\
         read R10 s = (word_zx:int32->int64) (w0:int32) /\
         read R11 s = read RDX s /\
         read R8 s = word_zx (a:int32) /\
         read R9 s = word_zx (b:int32) /\
         read R14 s = word_zx (c:int32) /\
         read R15 s = word_zx (d:int32) /\
         read (memory :> bytes32 data_ptr) s = w0 /\
         read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1 /\
         read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2 /\
         read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3 /\
         read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4 /\
         read (memory :> bytes32 (word_add data_ptr (word 20))) s = w5 /\
         read (memory :> bytes32 (word_add data_ptr (word 24))) s = w6 /\
         read (memory :> bytes32 (word_add data_ptr (word 28))) s = w7 /\
         read (memory :> bytes32 (word_add data_ptr (word 32))) s = w8 /\
         read (memory :> bytes32 (word_add data_ptr (word 36))) s = w9 /\
         read (memory :> bytes32 (word_add data_ptr (word 40))) s = w10 /\
         read (memory :> bytes32 (word_add data_ptr (word 44))) s = w11 /\
         read (memory :> bytes32 (word_add data_ptr (word 48))) s = w12 /\
         read (memory :> bytes32 (word_add data_ptr (word 52))) s = w13 /\
         read (memory :> bytes32 (word_add data_ptr (word 56))) s = w14 /\
         read (memory :> bytes32 (word_add data_ptr (word 60))) s = w15` THEN
  CONJ_TAC THENL [
    (* Segment 1: pc+40..pc+569 — use TEST_R1 (let-form post) and weaken to EL-form via 4WAY bridge. *)
    MP_TAC(SPECL
      [`pc:num`; `data_ptr:int64`;
       `a:int32`; `b:int32`; `c:int32`; `d:int32`;
       `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`;
       `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`; `w9:int32`;
       `w10:int32`; `w11:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`]
      MD5_BLOCK_BODY_TEST_R1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
      (* SUB_T1: pre weakening *)
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      (* SUB_T2: MAYCHANGE *)
      REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
      (* SUB_T3: post weakening — TEST_R1 boilerplate then let→EL via 4WAY bridge. *)
      REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      RULE_ASSUM_TAC BETA_RULE THEN
      FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
      MP_TAC(SPECL
        [`s':x86state`;
         `a:int32`;`b:int32`;`c:int32`;`d:int32`;
         `w0:int32`;`w1:int32`;`w2:int32`;`w3:int32`;
         `w4:int32`;`w5:int32`;`w6:int32`;`w7:int32`;
         `w8:int32`;`w9:int32`;`w10:int32`;`w11:int32`;
         `w12:int32`;`w13:int32`;`w14:int32`;`w15:int32`]
        MD5_F_LET_TO_EL_4WAY) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[];
                      STRIP_TAC THEN REPEAT CONJ_TAC THEN
                      TRY (FIRST_X_ASSUM ACCEPT_TAC) THEN
                      TRY (ASM_REWRITE_TAC[])];
      (* SUB_T3 ends *)
    ];
    (* Segment 2: pc+569..pc+1185 — use ROUND2_CORRECT specialized to EL_i. *)
    MP_TAC(SPECL
      [`pc:num`; `data_ptr:int64`;
       `EL 0 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32`;
       `EL 1 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32`;
       `EL 2 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32`;
       `EL 3 (md5_compress 16 [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15] [a;b;c;d]):int32`;
       `w0:int32`; `w1:int32`; `w2:int32`; `w3:int32`; `w4:int32`;
       `w5:int32`; `w6:int32`; `w7:int32`; `w8:int32`; `w9:int32`;
       `w10:int32`; `w11:int32`; `w12:int32`; `w13:int32`; `w14:int32`; `w15:int32`]
      MD5_ROUND2_CORRECT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REPEAT CONJ_TAC THENL [
      (* SUB_T1 (seg-2): pre weakening — match cut predicate to ROUND2 pre. *)
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      POP_ASSUM(MP_TAC o BETA_RULE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64;
               ARITH_RULE `32 <= 64`; LE_REFL];
      (* SUB_T2 (seg-2): MAYCHANGE *)
      REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
      (* SUB_T3 (seg-2): post — ROUND2's post matches our outer post (let-chain in EL_i). *)
      REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SOME_FLAGS; SEQ_ID; GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      RULE_ASSUM_TAC BETA_RULE THEN
      FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
      FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update (fst MD5_BLOCK_ASM_DATA_ORDER_EXEC)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[WORD_ZX_TRIVIAL] THEN ASM_REWRITE_TAC[]
    ]
  ]);;

