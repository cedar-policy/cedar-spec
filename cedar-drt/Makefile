.PHONY: all run test

all:
	cd ../cedar-lean && lake build DiffTest:static Std:static Aesop:static ProofWidgets:static Qq:static Mathlib:static Cedar:static
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo build
	cd fuzz && LEAN_LIB_DIR=`lean --print-libdir` cargo build

test: all
	DYLD_LIBRARY_PATH=`lean --print-libdir`:${DYLD_LIBRARY_PATH} \
	LD_LIBRARY_PATH=`lean --print-libdir`:`lean --print-prefix`/lib/glibc/libm.so:${LD_LIBRARY_PATH} \
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo test