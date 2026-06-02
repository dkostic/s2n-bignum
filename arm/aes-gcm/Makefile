#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# If actually on an ARM8 machine, just use the GNU assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). The aarch64
# cross-assembling version can be installed manually by something like:
#
#  sudo apt-get install binutils-aarch64-linux-gnu

OSTYPE_RESULT=$(shell uname -s)
ARCHTYPE_RESULT=$(shell uname -m)

ifeq ($(ARCHTYPE_RESULT),aarch64)
GAS=as
else
ifeq ($(OSTYPE_RESULT),Darwin)
GAS=as -arch arm64
OBJDUMP=otool -tvV
else
GAS=aarch64-linux-gnu-as
endif
endif

# List of object files
#
# aes_gcm.o is the verbatim aws-lc reference (AES-128/192/256 +
# encrypt/decrypt); kept for objdump comparison and as the base for
# follow-on AES-192/256 / decrypt verification work.
#
# aes_gcm_enc_kernel_aes128.o is the AES-128-only fork that the
# project actually verifies (the AES-192/256 dispatch branches are
# statically removed; the decrypt kernel is dropped).

OBJ = aes_gcm.o \
      aes_gcm_enc_kernel_aes128.o \
      aes4way_round.o \
      aes4way_round_mem.o \
      aes_load_block.o \
      ghash_modulo.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
