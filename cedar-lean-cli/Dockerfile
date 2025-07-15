FROM amazonlinux:2023 AS prepare

RUN yum update -y \
  && yum install -y \
  curl-minimal clang tar zip unzip python3 git xz \
  make wget gcc gcc-c++ protobuf-compiler \
  && yum clean all

# Setup Rust toolchain
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > /tmp/rustup.sh \
  && chmod +x /tmp/rustup.sh \
  && /tmp/rustup.sh -y \
  && . ~/.profile; rustup component add llvm-tools-preview rust-src

# Install Lean
RUN wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh && sh elan-init.sh -y --default-toolchain none

# Install CVC5
RUN ARCH=$(uname -m) && \
    if [ "$ARCH" = "x86_64" ]; then \
        ARCH_NAME="x86_64"; \
    elif [ "$ARCH" = "aarch64" ] || [ "$ARCH" = "arm64" ]; then \
        ARCH_NAME="arm64"; \
    else \
        echo "Unsupported architecture: $ARCH" && \
        exit 1; \
    fi && \
    wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-${ARCH_NAME}-static.zip && \
    unzip cvc5-Linux-${ARCH_NAME}-static.zip && \
    chmod +x cvc5-Linux-${ARCH_NAME}-static/bin/cvc5 && \
    mv cvc5-Linux-${ARCH_NAME}-static/bin/cvc5 /usr/local/bin/

ENV CVC5=cvc5

FROM prepare AS build

ENV CEDAR_SPEC_ROOT=/opt/src/cedar-spec
COPY . $CEDAR_SPEC_ROOT

# Build the Lean formalization and extract to static C libraries
WORKDIR $CEDAR_SPEC_ROOT/cedar-lean-ffi
RUN source /root/.profile \
  && elan default "$(cat ../lean-toolchain)" \
  && ./build_lean_lib.sh

# Build CLI
WORKDIR $CEDAR_SPEC_ROOT/cedar-lean-cli
RUN source /root/.profile \
  && source ../cedar-lean-ffi/set_env_vars.sh \
  && cargo install --path .

ENTRYPOINT ["/usr/bin/bash", "--rcfile", "../rcfile"]
