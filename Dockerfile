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

# Build DRT
WORKDIR $CEDAR_SPEC_ROOT
RUN source /root/.profile && ./build.sh

# Prepare DRT
WORKDIR $CEDAR_SPEC_ROOT/cedar-drt
