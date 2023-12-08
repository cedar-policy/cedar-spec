FROM amazonlinux:2 AS prepare


RUN yum update -y \
  && yum install -y \
	curl clang tar zip unzip python3 git xz java-1.8.0-openjdk-devel.x86_64 \
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

# Setup DOTNET toolchain
RUN mkdir /opt/dotnet \
  && wget -q https://dot.net/v1/dotnet-install.sh -O /opt/dotnet/dotnet-install.sh \
  && chmod +x /opt/dotnet/dotnet-install.sh \
  && /opt/dotnet/dotnet-install.sh --channel 6.0
ENV PATH="/root/.dotnet/:$PATH"

# Setup Java/Gradle toolchain
RUN mkdir /opt/gradle \
  && wget -q "https://services.gradle.org/distributions/gradle-8.1.1-bin.zip" -O /opt/gradle/gradle.zip \
  && unzip /opt/gradle/gradle.zip -d /opt/gradle/
ENV PATH="/opt/gradle/gradle-8.1.1/bin/:$PATH"

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
