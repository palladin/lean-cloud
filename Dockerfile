FROM ubuntu:24.04 AS toolchain
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git zstd build-essential libpq-dev \
    libsqlite3-dev freetds-dev default-libmysqlclient-dev pkg-config \
    && rm -rf /var/lib/apt/lists/*
ARG TARGETARCH
RUN set -eux; \
    case "$TARGETARCH" in arm64) platform=linux_aarch64 ;; amd64) platform=linux ;; *) exit 1 ;; esac; \
    curl -fL --retry 3 "https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-${platform}.tar.zst" \
      | tar --zstd -x -C /opt; \
    ln -s "/opt/lean-4.34.1-${platform}" /opt/lean
ENV PATH="/opt/lean/bin:${PATH}"
RUN apt-get update && apt-get install -y --no-install-recommends librabbitmq-dev \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /src

FROM toolchain AS node-build
COPY LeanCloudCli/Templates/node.c /tmp/node.c
RUN cc -O2 -Wall -Wextra -Werror /tmp/node.c -o /usr/local/bin/cloud-node

FROM toolchain AS build
COPY . .
WORKDIR /src/runtime
RUN --mount=type=cache,id=lean-cloud-runtime,target=/src/runtime/.lake,sharing=locked --mount=type=cache,target=/src/.lake \
    lake build cloud_demo && mkdir -p /out && cp .lake/build/bin/cloud_demo /out/cloud_demo

FROM build AS integration-build
RUN --mount=type=cache,id=lean-cloud-runtime,target=/src/runtime/.lake,sharing=locked --mount=type=cache,target=/src/.lake \
    lake build cloud_integration_tests && cp .lake/build/bin/cloud_integration_tests /out/cloud_integration_tests

FROM ubuntu:24.04 AS runner
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl openssl libsqlite3-0 librabbitmq4 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data && chown worker:worker /data
USER worker

FROM runner AS integration
COPY --from=integration-build /out/cloud_integration_tests /usr/local/bin/cloud-integration-tests
ENTRYPOINT ["cloud-integration-tests"]

FROM rabbitmq:4.3 AS worker
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl openssl libsqlite3-0 librabbitmq4 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data && chown worker:worker /data
ENV RABBITMQ_DEFAULT_USER=cloud RABBITMQ_DEFAULT_PASS=local-cloud \
    RABBITMQ_SERVER_ADDITIONAL_ERL_ARGS="+S 2:2 +sbwt none +sbwtdcpu none +sbwtdio none"
COPY deploy/rabbitmq.conf /etc/rabbitmq/rabbitmq.conf
COPY --from=node-build /usr/local/bin/cloud-node /usr/local/bin/cloud-node
LABEL lean-cloud.node="mailbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=10s --retries=40 CMD ["cloud-node", "health"]
COPY --from=build /out/cloud_demo /usr/local/bin/cloud-demo
COPY --from=build /out/cloud_demo /usr/local/bin/cloud-app
ENTRYPOINT ["cloud-node"]
