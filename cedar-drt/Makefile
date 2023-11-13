.PHONY: all run test

all:
	cd ../cedar-lean && lake build Cedar DiffTest Std:static
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo build;
	LEAN_LIB_DIR=`lean --print-libdir` \
	cd fuzz && LEAN_LIB_DIR=`lean --print-libdir` cargo build

test: all
	DYLD_LIBRARY_PATH=`lean --print-libdir` \
	LD_LIBRARY_PATH=`lean --print-libdir` \
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo test

run: all
	DYLD_LIBRARY_PATH=`lean --print-libdir` \
	LD_LIBRARY_PATH=`lean --print-libdir` \
	LEAN_LIB_DIR=`lean --print-libdir` \
	cargo fuzz run -s none $(target)