ARG GAME_DIR

FROM ubuntu:18.04

WORKDIR /

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y git curl libatomic1

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
RUN ./elan-init -y --default-toolchain leanprover/lean4:nightly-2022-09-23
# TODO: Read out lean version from lean-toolchain file
ENV PATH="${PATH}:/root/.elan/bin"

# Copy lean files
COPY lake-packages/GameServer/server/GameServer ./GameServer
COPY lake-packages/GameServer/server/Main.lean ./Main
COPY lake-packages/GameServer/server/lakefile.lean ./lakefile.lean
COPY lake-packages/GameServer/server/lake-manifest.json ./lake-manifest.json
COPY lake-packages/GameServer/server/lean-toolchain ./lean-toolchain

# Copy the game to `nng`
COPY NNG ./nng/NNG
COPY NNG.lean ./nng/NNG.lean
COPY lakefile.lean ./nng/lakefile.lean
COPY lake-manifest.json ./nng/lake-manifest.json
COPY lean-toolchain ./nng/lean-toolchain

WORKDIR /
RUN rm -f ./build/bin/gameserver
RUN lake build

WORKDIR /build/bin/
