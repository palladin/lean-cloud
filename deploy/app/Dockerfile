FROM ubuntu:24.04 AS toolchain
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git zstd build-essential libpq-dev \
    libsqlite3-dev freetds-dev default-libmysqlclient-dev pkg-config \
    && rm -rf /var/lib/apt/lists/*
ARG TARGETARCH
ARG LEAN_VERSION
RUN set -eu; \
    case "$TARGETARCH" in arm64) platform=linux_aarch64 ;; amd64) platform=linux ;; *) exit 1 ;; esac; \
    curl -fL --retry 3 --connect-timeout 20 --max-time 180 --retry-max-time 180 \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-${platform}.tar.zst" \
      | tar --zstd -x -C /opt; \
    ln -s "/opt/lean-${LEAN_VERSION}-${platform}" /opt/lean
ENV PATH="/opt/lean/bin:${PATH}"
RUN apt-get update && apt-get install -y --no-install-recommends libcurl4-openssl-dev \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /src

FROM toolchain AS build
COPY --from=node_assets node.c /tmp/node.c
RUN cc -O2 -Wall -Wextra -Werror /tmp/node.c -o /usr/local/bin/cloud-node
COPY --from=sdk lean-toolchain lakefile.lean lake-manifest.json /opt/lean-cloud/
COPY --from=sdk runtime/lakefile.lean runtime/lake-manifest.json /opt/lean-cloud/runtime/
WORKDIR /src
COPY lakefile.lean lean-toolchain ./
RUN lake -KleanCloudSdk=/opt/lean-cloud update lean_cloud_runtime && \
    lake -KleanCloudSdk=/opt/lean-cloud build LeanEff LeanLinq LeanLinq.Driver.Sqlite
COPY --from=sdk LeanCloud.lean /opt/lean-cloud/
COPY --from=sdk LeanCloud /opt/lean-cloud/LeanCloud
COPY --from=sdk LeanCloudCli /opt/lean-cloud/LeanCloudCli
COPY --from=sdk native /opt/lean-cloud/native
COPY --from=sdk runtime/LeanCloudRuntime.lean /opt/lean-cloud/runtime/
COPY --from=sdk runtime/LeanCloudRuntime /opt/lean-cloud/runtime/LeanCloudRuntime
COPY --from=sdk runtime/native /opt/lean-cloud/runtime/native
RUN lake -KleanCloudSdk=/opt/lean-cloud build LeanCloudRuntime

WORKDIR /src
COPY . .
ARG APP_TARGET
RUN lake -KleanCloudSdk=/opt/lean-cloud build "$APP_TARGET" && mkdir -p /out && cp ".lake/build/bin/$APP_TARGET" /out/app

FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl openssl tzdata libsqlite3-0 libcurl4t64 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data /mailbox && chown worker:worker /data /mailbox
COPY --from=build /out/app /usr/local/bin/cloud-app
COPY --from=build /usr/local/bin/cloud-node /usr/local/bin/cloud-node
LABEL lean-cloud.node="http-inbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=10s --retries=40 CMD ["cloud-node", "health"]
ENTRYPOINT ["cloud-node"]
