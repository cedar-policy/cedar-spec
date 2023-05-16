# For now, we assume that `dotnet` is on the PATH and Dafny is set up to use 
# the correct Z3 (there are a few options for how that can be achieved). 
# Maybe more similar assumptions.

# To typecheck your code, but not run the verifier, do
#    $ make DAFNY_VERIFY=0
# This is much faster to iterate when you're just refactoring.

# Make `all` the default target.
all:

clean:
	rm -rf build

export DOTNET_CLI_TELEMETRY_OPTOUT := 1

export DOTNET_SYSTEM_GLOBALIZATION_INVARIANT := 1

# Make `dotnet` install Dafny into the current directory instead of the user's
# home directory to keep things self-contained. The files that get created are
# `.dotnet`, `.local/share/NuGet`, and `.nuget`.
export DOTNET_CLI_HOME := $(PWD)

uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')

# Assumes that we have `dotnet` installed and on the PATH locally
DOTNET = dotnet

restore-dafny:
	dotnet tool restore

# If GEN_STATS is set to 1, compilation will generate statistics in a `TestResults` directory.
GEN_STATS ?= 0
ifeq ($(GEN_STATS), 1)
clean-test-results:
	rm -rf TestResults/*.csv TestResults/*.trx
DAFNY_ARGS = /dafnyVerify:1 /compile:0 /warnShadowing /warningsAsErrors /vcsLoad:1 /definiteAssignment:3 /verificationLogger:csv
else
clean-test-results:
DAFNY_ARGS = /compile:0 /warnShadowing /warningsAsErrors /vcsLoad:1 /definiteAssignment:3
endif

SOURCEDIR := .
TEST_SOURCEDIR := ./test
SOURCES := $(shell find $(SOURCEDIR) -path $(TEST_SOURCEDIR) -prune -o -name '*.dfy' -print | grep -v flycheck)
PACKAGE_BUILD_ROOT := build

DAFNY_VERIFY ?= 1

# Currently, the name of the target that verifies an individual Dafny file is
# just the path of that file. This design is awkward because the files already
# exist and hence the targets have to be marked `.PHONY` (below); it would be
# better to add a prefix or suffix to the file path. However, by now, all our
# users are used to passing plain Dafny file paths as arguments, and it doesn't
# seem worth the disruption to change this.
$(SOURCES): restore-dafny clean-test-results
	$(DOTNET) tool run dafny /dafnyVerify:$(DAFNY_VERIFY) $(DAFNY_ARGS) $@

verify: $(SOURCES)

TEST_SOURCES := $(shell find $(TEST_SOURCEDIR) -name '*.dfy' | grep -v flycheck)
DAFNY_TEST_ARGS := /compile:4 /runAllTests:1 /noVerify

$(TEST_SOURCES): restore-dafny
	$(DOTNET) tool run dafny $(DAFNY_TEST_ARGS) $@

test: $(TEST_SOURCES)

# The actual path of the output directory consists of the `/out` path plus
# `-java`. Dafny also generates a jar at the `/out` path plus `.jar`. We set
# the `DIFFTEST_*` variables below accordingly.
DIFFTEST_COMPILE_OUT := $(PACKAGE_BUILD_ROOT)/private/compile-difftest
DIFFTEST_JAVA_DIR := $(DIFFTEST_COMPILE_OUT)-java
DIFFTEST_JAR_FROM_DAFNY := $(DIFFTEST_COMPILE_OUT).jar
DIFFTEST_JAR_EXPORTED := $(PACKAGE_BUILD_ROOT)/lib/CedarDafny-difftest.jar
compile-difftest: restore-dafny
	mkdir -p $(PACKAGE_BUILD_ROOT)/private
	rm -rf $(DIFFTEST_COMPILE_OUT)* $(DIFFTEST_JAR_EXPORTED)
	$(DOTNET) tool run dafny /noVerify /compile:2 /compileTarget:java \
		/out:$(DIFFTEST_COMPILE_OUT) difftest/main.dfy
	mkdir -p $(PACKAGE_BUILD_ROOT)/lib
	cp $(DIFFTEST_JAR_FROM_DAFNY) $(DIFFTEST_JAR_EXPORTED)

all: verify test compile-difftest

.PHONY: $(SOURCES) $(TEST_SOURCES) verify compile-difftest all test
