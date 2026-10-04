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

FROM runner AS worker
COPY --from=build /out/cloud_demo /usr/local/bin/cloud-demo
COPY --from=build /out/cloud_demo /usr/local/bin/cloud-app
ENTRYPOINT ["cloud-app"]
