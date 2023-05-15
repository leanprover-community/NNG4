FROM ubuntu:22.04

WORKDIR /

RUN apt-get update && apt-get install -y git curl libatomic1

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz \
  && ./elan-init -y --default-toolchain none
ENV PATH="${PATH}:/root/.elan/bin"

# Copy the game to `game`
COPY . ./game

WORKDIR /game
RUN lake update
# && lake exe cache get
# # TODO: cache is currently only in mathlib, add it once its in Std

WORKDIR /game/lake-packages/GameServer/server/
RUN lake clean && lake build

WORKDIR /game
RUN lake clean && lake build

WORKDIR /game/lake-packages/GameServer/server/build/bin/

CMD ./gameserver --server /game/
