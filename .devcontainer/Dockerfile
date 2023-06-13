FROM node:20

WORKDIR /

ENV ELAN_HOME=/usr/local/elan \
  PATH=/usr/local/elan/bin:$PATH \
  LEAN_VERSION=leanprover/lean4:nightly

SHELL ["/bin/bash", "-euxo", "pipefail", "-c"]

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain $LEAN_VERSION; \
  chmod -R a+w $ELAN_HOME; \
  elan --version; \
  lean --version; \
  leanc --version; \
  lake --version;

WORKDIR /
RUN git clone https://github.com/leanprover-community/lean4game.git

WORKDIR /lean4game
RUN npm install

EXPOSE 3000
