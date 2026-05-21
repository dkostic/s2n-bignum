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
(* Phase 5: strengthened step-0 lemma exposing R10 = w1 and                  *)
(* R11 = word_zx (word_zx c) in the post (set by MOV r10d, [rsi+4] and       *)
(* MOV r11d, ecx in the tail of step 0's body). Pre adds the message-word    *)
(* w1 from memory at offset 4. Same proof as MD5_1STEP_CORRECT — the         *)
(* enrichment threads through automatically because the stepper records      *)
(* both register writes during steps 1--11.                                  *)
(* ------------------------------------------------------------------------- *)

let MD5_1STEP_CORRECT_STRONG = prove
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
                   read (memory :> bytes32 (word_add data_ptr (word 4))) s = w1)
              (\s. read RIP s = word(pc + 90) /\
                   read RAX s =
                     word_zx (word_add b (word_rol (word_add (word_add a (md5_F b c d))
                                                             (word_add w0 (EL 0 md5_T)))
                                                   7)) /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w1 /\
                   read R11 s = word_zx (word_zx c:int32))
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
(* Phase 5: round-1 step 1 over [pc+90, pc+122). Computes:                   *)
(*   new_d = a + ROL_12(d + md5_F a b c + W[1] + T[1])                       *)
(* RAX/RBX/RCX unchanged. R10/R11 preserved (R11 = word_zx b for next step). *)
(* Step 1's first instruction is XOR r11d, ebx, which reads R11 carried from *)
(* step 0's tail (R11 = word_zx c at pc+90), so the precondition pins R11.   *)
(* ------------------------------------------------------------------------- *)

let MD5_R1_STEP1_CORRECT = prove
 (`!pc data_ptr a b c d w1 w2:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 90) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w1 /\
                   read R11 s = word_zx (word_zx c:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 8))) s = w2)
              (\s. read RIP s = word(pc + 122) /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s =
                     word_zx (word_add a (word_rol (word_add (word_add d (md5_F a b c))
                                                             (word_add w1 (EL 1 md5_T)))
                                                   12)) /\
                   read R10 s = word_zx w2 /\
                   read R11 s = word_zx (word_zx b:int32))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RDX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor c b) (a:int32)) c =
    word_xor (word_and a (word_xor b c)) c`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Round-1 step 2 over [pc+122, pc+154). Computes:                           *)
(*   new_c = d + ROL_17(c + md5_F d a b + W[2] + T[2])                       *)
(* into RCX. RAX/RBX/RDX unchanged. R10 reloaded with W[3], R11 = word_zx a  *)
(* (carries to step 3's preamble XOR r11d, edx).                             *)
(* ------------------------------------------------------------------------- *)

let MD5_R1_STEP2_CORRECT = prove
 (`!pc data_ptr a b c d w2 w3:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 122) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w2 /\
                   read R11 s = word_zx (word_zx b:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 12))) s = w3)
              (\s. read RIP s = word(pc + 154) /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s =
                     word_zx (word_add d (word_rol (word_add (word_add c (md5_F d a b))
                                                             (word_add w2 (EL 2 md5_T)))
                                                   17)) /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w3 /\
                   read R11 s = word_zx (word_zx a:int32))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RCX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor b a) (d:int32)) b =
    word_xor (word_and d (word_xor a b)) b`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Round-1 step 3 over [pc+154, pc+186), the last step of round-1's first    *)
(* quarter. Computes:                                                        *)
(*   new_b = c + ROL_22(b + md5_F c d a + W[3] + T[3])                       *)
(* into RBX. RAX/RCX/RDX unchanged. R10 reloaded with W[4], R11 = word_zx d  *)
(* (carries to step 4's preamble — the start of quarter 2).                  *)
(* ------------------------------------------------------------------------- *)

let MD5_R1_STEP3_CORRECT = prove
 (`!pc data_ptr a b c d w3 w4:int32.
        nonoverlapping (word pc, LENGTH md5_block_asm_data_order_tmc)
                       (data_ptr:int64,64)
        ==> ensures x86
              (\s. bytes_loaded s (word pc)
                     (BUTLAST md5_block_asm_data_order_tmc) /\
                   read RIP s = word(pc + 154) /\
                   read RSI s = data_ptr /\
                   read RAX s = word_zx a /\
                   read RBX s = word_zx b /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w3 /\
                   read R11 s = word_zx (word_zx a:int32) /\
                   read (memory :> bytes32 (word_add data_ptr (word 16))) s = w4)
              (\s. read RIP s = word(pc + 186) /\
                   read RAX s = word_zx a /\
                   read RBX s =
                     word_zx (word_add c (word_rol (word_add (word_add b (md5_F c d a))
                                                             (word_add w3 (EL 3 md5_T)))
                                                   22)) /\
                   read RCX s = word_zx c /\
                   read RDX s = word_zx d /\
                   read R10 s = word_zx w4 /\
                   read R11 s = word_zx (word_zx d:int32))
              (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
               MAYCHANGE [RBX; R10; R11] ,,
               MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_BLOCK_ASM_DATA_ORDER_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  SIMP_TAC[WORD_SX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_RULE `32 <= 64`; LE_REFL] THEN
  REWRITE_TAC[md5_T] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM MD5_F_XOR_AND_FORM] THEN
  SUBGOAL_THEN
   `word_xor (word_and (word_xor a d) (c:int32)) a =
    word_xor (word_and c (word_xor d a)) a`
   SUBST1_TAC THENL [CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[LEA_TRUNC_LEMMA] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* MD5_QUARTER1_CORRECT: round-1 quarter-1 (steps 0..3, 38 instructions).    *)
(*                                                                           *)
(* Direct 38-step symbolic execution from pc+52 to pc+186.                   *)
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
                   read R10 s = word_zx w4)
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
