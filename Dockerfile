FROM amazonlinux:2 AS prepare

RUN yum update -y \
  && yum install -y \
  curl clang tar zip unzip python3 git xz \
  make wget \
  && yum clean all

# Setup Rust toolchain
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > /tmp/rustup.sh \
  && chmod +x /tmp/rustup.sh \
  && /tmp/rustup.sh -y \
  && . ~/.profile; rustup component add llvm-tools-preview rust-src

# Install cargo-fuzz
RUN . ~/.profile; cargo install cargo-fuzz

# Install Lean
RUN wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh && sh elan-init.sh -y --default-toolchain none

FROM prepare AS build

ENV CEDAR_SPEC_ROOT=/opt/src/cedar-spec
COPY . $CEDAR_SPEC_ROOT

# Clone `cedar` repository
WORKDIR $CEDAR_SPEC_ROOT
RUN git clone --depth 1 https://github.com/cedar-policy/cedar

# Build the Lean formalization and extract to static C libraries
WORKDIR $CEDAR_SPEC_ROOT/cedar-lean
RUN source /root/.profile && source ../cedar-drt/set_env_vars.sh && elan default "$(cat lean-toolchain)" && ../cedar-drt/build_lean_lib.sh

# Build DRT
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
RUN source /root/.profile && source ./set_env_vars.sh && cargo build

# Initialize corpus for all targets. No-op for target that don't need initilization.
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
RUN source /root/.profile &&  ./initialize_corpus.sh --all

ENTRYPOINT ["/usr/bin/bash", "--rcfile", "../rcfile"]
