.PHONY: all run test

all:
	cd ../cedar-lean && lake build Cedar:static DiffTest:static Std:static Mathlib:static Qq:static Aesop:static ProofWidgets:static
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo build
	cd fuzz && LEAN_LIB_DIR=`lean --print-libdir` cargo build

test: all
	DYLD_LIBRARY_PATH=`lean --print-libdir`:${DYLD_LIBRARY_PATH} \
	LD_LIBRARY_PATH=`lean --print-libdir`:`lean --print-prefix`/lib/glibc/libm.so:${LD_LIBRARY_PATH} \
	LEAN_LIB_DIR=`lean --print-libdir` \
	RUST_BACKTRACE=1 \
	cargo test -- --nocapture
