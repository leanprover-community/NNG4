FROM node:20

WORKDIR /

ENV ELAN_HOME=/usr/local/elan \
  PATH=/usr/local/elan/bin:$PATH \
  LEAN_VERSION=leanprover/lean4:v4.0.0-rc4
  # TODO: read toolchain from `lean-toolchain`

SHELL ["/bin/bash", "-euxo", "pipefail", "-c"]

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION; \
  chmod -R a+w $ELAN_HOME; \
  elan --version; \
  lean --version; \
  leanc --version; \
  lake --version;

USER node

WORKDIR /home/node
RUN git clone https://github.com/leanprover-community/lean4game.git
