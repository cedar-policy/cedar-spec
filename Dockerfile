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
  && . ~/.profile; rustup toolchain install nightly \
  && . ~/.profile; rustup component add --toolchain nightly llvm-tools-preview rust-src

# Install cargo-fuzz
RUN . ~/.profile; cargo install cargo-fuzz

# Install Lean
RUN wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh && sh elan-init.sh -y

FROM prepare AS build

ENV CEDAR_SPEC_ROOT=/opt/src/cedar-spec
COPY . $CEDAR_SPEC_ROOT

# Clone `cedar` repository
WORKDIR $CEDAR_SPEC_ROOT
RUN git clone https://github.com/cedar-policy/cedar

# Build the Lean formalization and extract to static C libraries
WORKDIR $CEDAR_SPEC_ROOT/cedar-lean
RUN source /root/.profile && lake build Cedar:static DiffTest:static Std:static

# Build DRT
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
RUN source /root/.profile && source ./set_env_vars.sh && cargo build