FROM ubuntu:24.04 AS build
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git zstd build-essential pkg-config librabbitmq-dev \
    libpq-dev libsqlite3-dev freetds-dev default-libmysqlclient-dev \
    && rm -rf /var/lib/apt/lists/*
ARG TARGETARCH
ARG LEAN_VERSION
RUN set -eu; \
    case "$TARGETARCH" in arm64) platform=linux_aarch64 ;; amd64) platform=linux ;; *) exit 1 ;; esac; \
    curl -fL --retry 3 "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-${platform}.tar.zst" \
      | tar --zstd -x -C /opt; \
    ln -s "/opt/lean-${LEAN_VERSION}-${platform}" /opt/lean
ENV PATH="/opt/lean/bin:${PATH}"
COPY --from=node_assets node.c /tmp/node.c
RUN cc -O2 -Wall -Wextra -Werror /tmp/node.c -o /usr/local/bin/cloud-node
# SDK_CONTEXT
WORKDIR /src
COPY . .
ARG APP_TARGET
# BUILD_APP

FROM rabbitmq:4.3
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl openssl libsqlite3-0 librabbitmq4 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data && chown worker:worker /data
COPY --from=build /out/app /usr/local/bin/cloud-app
ENV RABBITMQ_DEFAULT_USER=cloud RABBITMQ_DEFAULT_PASS=local-cloud \
    RABBITMQ_SERVER_ADDITIONAL_ERL_ARGS="+S 2:2 +sbwt none +sbwtdcpu none +sbwtdio none"
COPY --from=node_assets rabbitmq.conf /etc/rabbitmq/rabbitmq.conf
COPY --from=build /usr/local/bin/cloud-node /usr/local/bin/cloud-node
LABEL lean-cloud.node="mailbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=10s --retries=40 CMD ["cloud-node", "health"]
ENTRYPOINT ["cloud-node"]
