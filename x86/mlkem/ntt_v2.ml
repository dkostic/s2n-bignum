[
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0x7d; 0x6f; 0x7e; 0x40;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0x56; 0x60;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,96))) *)
  0xc4; 0x41; 0x3d; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm8) (%_% ymm15) *)
  0xc4; 0x41; 0x35; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm9) (%_% ymm15) *)
  0xc4; 0x41; 0x2d; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm10) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xd8;
                           (* VPADDW (%_% ymm3) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe1;
                           (* VPADDW (%_% ymm4) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x55; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xea;
                           (* VPADDW (%_% ymm5) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x4d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xf3;
                           (* VPADDW (%_% ymm6) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x45; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe5;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcd;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xee;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm14) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd6;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf7;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xfd; 0x7f; 0x1f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm11) *)
  0xc5; 0x7d; 0x6f; 0x7e; 0x60;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,128))) *)
  0xc4; 0x41; 0x3d; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm8) (%_% ymm15) *)
  0xc4; 0x41; 0x35; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm9) (%_% ymm15) *)
  0xc4; 0x41; 0x2d; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm10) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xd8;
                           (* VPADDW (%_% ymm3) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xe1;
                           (* VPADDW (%_% ymm4) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x55; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x4d; 0xfd; 0xea;
                           (* VPADDW (%_% ymm5) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x4d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xf3;
                           (* VPADDW (%_% ymm6) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x45; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc4;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe5;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcd;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xee;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm14) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd6;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf7;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc4; 0xc3; 0x55; 0x46; 0xfa; 0x20;
                           (* VPERM2I128 (%_% ymm7) (%_% ymm5) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm5) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xeb; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm6) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0x7d; 0x6f; 0xbe; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,192))) *)
  0xc4; 0x41; 0x45; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x41; 0x2d; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm10) (%_% ymm15) *)
  0xc4; 0x41; 0x55; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm5) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xc5; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0xd5; 0xe5; 0xea;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0xc3; 0x65; 0x46; 0xf0; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm3) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x65; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm3) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd9; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm4) (%_% ymm9) (Imm8 (word 49)) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc5; 0xcd; 0xfd; 0xe7;  (* VPADDW (%_% ymm4) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xc1; 0x3d; 0xfd; 0xf2;
                           (* VPADDW (%_% ymm6) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x65; 0xfd; 0xc5;  (* VPADDW (%_% ymm8) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x35; 0xfd; 0xdb;
                           (* VPADDW (%_% ymm3) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfc;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm12) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf5;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd5;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc6;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm14) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xee;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm14) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdf;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x3d; 0x6c; 0xcd;  (* VPUNPCKLQDQ (%_% ymm9) (%_% ymm8) (%_% ymm5) *)
  0xc5; 0xbd; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm8) (%_% ymm5) *)
  0xc4; 0x41; 0x65; 0x6c; 0xc3;
                           (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x65; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm3) (%_% ymm11) *)
  0xc5; 0x7d; 0x6f; 0xbe; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,256))) *)
  0xc4; 0x41; 0x35; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm9) (%_% ymm15) *)
  0xc4; 0x41; 0x55; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm5) (%_% ymm15) *)
  0xc4; 0x41; 0x3d; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm8) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0xd5; 0xe5; 0xea;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0xdd; 0x6c; 0xdf;  (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm4) (%_% ymm7) *)
  0xc5; 0xdd; 0x6d; 0xff;  (* VPUNPCKHQDQ (%_% ymm7) (%_% ymm4) (%_% ymm7) *)
  0xc4; 0xc1; 0x4d; 0x6c; 0xe2;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x4d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm6) (%_% ymm10) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xf1;
                           (* VPADDW (%_% ymm6) (%_% ymm3) (%_% ymm9) *)
  0xc4; 0x41; 0x65; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm3) (%_% ymm9) *)
  0xc5; 0xc5; 0xfd; 0xdd;  (* VPADDW (%_% ymm3) (%_% ymm7) (%_% ymm5) *)
  0xc5; 0xc5; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm7) (%_% ymm5) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xf8;
                           (* VPADDW (%_% ymm7) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x2d; 0xfd; 0xe3;
                           (* VPADDW (%_% ymm4) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf4;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm12) *)
  0xc4; 0x41; 0x35; 0xfd; 0xcc;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdd;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xed;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xfe;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm14) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc6;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm14) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe7;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc4; 0x41; 0x7e; 0x12; 0xd0;
                           (* VMOVSLDUP (%_% ymm10) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xd2; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm7) (%_% ymm10) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xfb;
                           (* VMOVSLDUP (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm4) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm4) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x6f; 0xbe; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,320))) *)
  0xc4; 0x41; 0x2d; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm10) (%_% ymm15) *)
  0xc4; 0x41; 0x3d; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm8) (%_% ymm15) *)
  0xc4; 0x41; 0x45; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0xc5; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xe1;
                           (* VMOVSLDUP (%_% ymm4) (%_% ymm9) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm6) (%_% ymm4) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm6) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xf5;  (* VMOVSLDUP (%_% ymm6) (%_% ymm5) *)
  0xc4; 0xe3; 0x65; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm3) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xfd; 0xda;
                           (* VPADDW (%_% ymm3) (%_% ymm4) (%_% ymm10) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm4) (%_% ymm10) *)
  0xc4; 0xc1; 0x35; 0xfd; 0xe0;
                           (* VPADDW (%_% ymm4) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xf9; 0xc0;
                           (* VPSUBW (%_% ymm8) (%_% ymm9) (%_% ymm8) *)
  0xc5; 0x4d; 0xfd; 0xcf;  (* VPADDW (%_% ymm9) (%_% ymm6) (%_% ymm7) *)
  0xc5; 0xcd; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm6) (%_% ymm7) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xf3;
                           (* VPADDW (%_% ymm6) (%_% ymm5) (%_% ymm11) *)
  0xc4; 0x41; 0x55; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm5) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdc;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe5;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfd; 0xc5;
                           (* VPADDW (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xf9; 0xce;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfe;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm14) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf7;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xd5; 0x72; 0xf7; 0x10;
                           (* VPSLLD (%_% ymm5) (%_% ymm7) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x35; 0x0e; 0xed; 0xaa;
                           (* VPBLENDW (%_% ymm5) (%_% ymm9) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x72; 0xd1; 0x10;
                           (* VPSRLD (%_% ymm9) (%_% ymm9) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x35; 0x0e; 0xff; 0xaa;
                           (* VPBLENDW (%_% ymm7) (%_% ymm9) (%_% ymm7) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x35; 0x72; 0xf3; 0x10;
                           (* VPSLLD (%_% ymm9) (%_% ymm11) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xc9; 0xaa;
                           (* VPBLENDW (%_% ymm9) (%_% ymm6) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xcd; 0x72; 0xd6; 0x10;
                           (* VPSRLD (%_% ymm6) (%_% ymm6) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x4d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm11) (%_% ymm6) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0x7d; 0x6f; 0xbe; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,384))) *)
  0xc4; 0x41; 0x55; 0xd5; 0xe7;
                           (* VPMULLW (%_% ymm12) (%_% ymm5) (%_% ymm15) *)
  0xc4; 0x41; 0x45; 0xd5; 0xef;
                           (* VPMULLW (%_% ymm13) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x41; 0x35; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm9) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0xd5; 0xe5; 0xea;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0xc5; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0xc1; 0x4d; 0x72; 0xf2; 0x10;
                           (* VPSLLD (%_% ymm6) (%_% ymm10) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x65; 0x0e; 0xf6; 0xaa;
                           (* VPBLENDW (%_% ymm6) (%_% ymm3) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x72; 0xd3; 0x10;
                           (* VPSRLD (%_% ymm3) (%_% ymm3) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x65; 0x0e; 0xd2; 0xaa;
                           (* VPBLENDW (%_% ymm10) (%_% ymm3) (%_% ymm10) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x65; 0x72; 0xf0; 0x10;
                           (* VPSLLD (%_% ymm3) (%_% ymm8) (Imm8 (word 16)) *)
  0xc4; 0xe3; 0x5d; 0x0e; 0xdb; 0xaa;
                           (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm3) (Imm8 (word 170)) *)
  0xc5; 0xdd; 0x72; 0xd4; 0x10;
                           (* VPSRLD (%_% ymm4) (%_% ymm4) (Imm8 (word 16)) *)
  0xc4; 0x43; 0x5d; 0x0e; 0xc0; 0xaa;
                           (* VPBLENDW (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc5; 0xcd; 0xfd; 0xe5;  (* VPADDW (%_% ymm4) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xcd; 0xf9; 0xed;  (* VPSUBW (%_% ymm5) (%_% ymm6) (%_% ymm5) *)
  0xc5; 0xad; 0xfd; 0xf7;  (* VPADDW (%_% ymm6) (%_% ymm10) (%_% ymm7) *)
  0xc5; 0xad; 0xf9; 0xff;  (* VPSUBW (%_% ymm7) (%_% ymm10) (%_% ymm7) *)
  0xc4; 0x41; 0x65; 0xfd; 0xd1;
                           (* VPADDW (%_% ymm10) (%_% ymm3) (%_% ymm9) *)
  0xc4; 0x41; 0x65; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm3) (%_% ymm9) *)
  0xc4; 0xc1; 0x3d; 0xfd; 0xdb;
                           (* VPADDW (%_% ymm3) (%_% ymm8) (%_% ymm11) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm8) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xec;
                           (* VPADDW (%_% ymm5) (%_% ymm5) (%_% ymm12) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf5;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xfd;
                           (* VPADDW (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd6;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x35; 0xfd; 0xce;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm14) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdf;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x7d; 0x6f; 0xb6; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0x7d; 0x6f; 0xbe; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm15) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,512))) *)
  0xc4; 0x41; 0x2d; 0xd5; 0xe6;
                           (* VPMULLW (%_% ymm12) (%_% ymm10) (%_% ymm14) *)
  0xc4; 0x41; 0x65; 0xd5; 0xee;
                           (* VPMULLW (%_% ymm13) (%_% ymm3) (%_% ymm14) *)
  0xc4; 0x41; 0x35; 0xd5; 0xf7;
                           (* VPMULLW (%_% ymm14) (%_% ymm9) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xd5; 0xff;
                           (* VPMULLW (%_% ymm15) (%_% ymm11) (%_% ymm15) *)
  0xc4; 0x41; 0x2d; 0xe5; 0xd0;
                           (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm8) *)
  0xc4; 0xc1; 0x65; 0xe5; 0xd8;
                           (* VPMULHW (%_% ymm3) (%_% ymm3) (%_% ymm8) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xda;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0x41; 0x5d; 0xfd; 0xc2;
                           (* VPADDW (%_% ymm8) (%_% ymm4) (%_% ymm10) *)
  0xc4; 0x41; 0x5d; 0xf9; 0xd2;
                           (* VPSUBW (%_% ymm10) (%_% ymm4) (%_% ymm10) *)
  0xc5; 0xcd; 0xfd; 0xe3;  (* VPADDW (%_% ymm4) (%_% ymm6) (%_% ymm3) *)
  0xc5; 0xcd; 0xf9; 0xdb;  (* VPSUBW (%_% ymm3) (%_% ymm6) (%_% ymm3) *)
  0xc4; 0xc1; 0x55; 0xfd; 0xf1;
                           (* VPADDW (%_% ymm6) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x55; 0xf9; 0xc9;
                           (* VPSUBW (%_% ymm9) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x45; 0xfd; 0xeb;
                           (* VPADDW (%_% ymm5) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x45; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc4;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x41; 0x2d; 0xfd; 0xd4;
                           (* VPADDW (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe5;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfd; 0xdd;
                           (* VPADDW (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf6;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0x41; 0x35; 0xfd; 0xce;
                           (* VPADDW (%_% ymm9) (%_% ymm9) (%_% ymm14) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xef;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm15) *)
  0xc4; 0x41; 0x25; 0xfd; 0xdf;
                           (* VPADDW (%_% ymm11) (%_% ymm11) (%_% ymm15) *)
  0xc5; 0x7d; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0x7d; 0x7f; 0x57; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x5f; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;
