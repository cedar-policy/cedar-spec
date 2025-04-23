FROM amazonlinux:2023 AS prepare

RUN yum update -y \
  && yum install -y \
  curl-minimal clang tar zip unzip python3 git xz \
  make wget gcc gcc-c++ \
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

# Install protoc
RUN wget https://github.com/protocolbuffers/protobuf/releases/download/v29.0/protoc-29.0-linux-x86_64.zip && unzip protoc-29.0-linux-x86_64.zip && rm protoc-29.0-linux-x86_64.zip

FROM prepare AS build

ENV CEDAR_SPEC_ROOT=/opt/src/cedar-spec
COPY . $CEDAR_SPEC_ROOT

# Clone `cedar` repository
WORKDIR $CEDAR_SPEC_ROOT
RUN git clone --depth 1 -b release/4.4.x https://github.com/cedar-policy/cedar

# Build the Lean formalization and extract to static C libraries
WORKDIR $CEDAR_SPEC_ROOT/cedar-lean
RUN source /root/.profile \
  && elan default "$(cat lean-toolchain)" \
  && source ../cedar-drt/set_env_vars.sh \
  && ../cedar-drt/build_lean_lib.sh

# Build DRT
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
RUN source /root/.profile && source ./set_env_vars.sh && cargo fuzz build -s none

# Initialize corpus for all targets. No-op for target that don't need initilization.
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
RUN source /root/.profile &&  ./initialize_corpus.sh --all

ENTRYPOINT ["/usr/bin/bash", "--rcfile", "../rcfile"]
