FROM ubuntu:22.04

WORKDIR /

RUN apt-get update
RUN apt-get install -y git curl libatomic1

# Install elan
RUN curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz\
  && ./elan-init -y --default-toolchain none
ENV PATH="${PATH}:/root/.elan/bin"

# Copy the game to `game`
COPY . ./game

# Update the game
WORKDIR /game
RUN lake update
RUN lake clean
RUN lake exe cache get

# Build the gameserver first
WORKDIR /game/lake-packages/GameServer/server/
RUN lake clean
RUN lake build

# Build the game
WORKDIR /game
RUN lake build

# Remove the cache from the docker container
RUN rm -rf /root/.cache

WORKDIR /game/lake-packages/GameServer/server/build/bin/
CMD ./gameserver --server /game/
