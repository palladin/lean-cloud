ARG APPLICATION_IMAGE=lean-cloud-build-app:dev
FROM ubuntu:24.04 AS source
ARG TARGETARCH
ARG SOURCE_LEAN_VERSION=4.35.0
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl zstd \
    && rm -rf /var/lib/apt/lists/*
RUN set -eu; \
    case "$TARGETARCH" in arm64) platform=linux_aarch64 ;; amd64) platform=linux ;; *) exit 1 ;; esac; \
    curl -fL --retry 3 --connect-timeout 20 --max-time 300 \
      "https://github.com/leanprover/lean4/releases/download/v${SOURCE_LEAN_VERSION}/lean-${SOURCE_LEAN_VERSION}-${platform}.tar.zst" \
      | tar --zstd -x -C /opt; \
    mv "/opt/lean-${SOURCE_LEAN_VERSION}-${platform}" /opt/build-lean
FROM ${APPLICATION_IMAGE} AS application

# Keep the large toolchain layer independent of application-code changes.
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    git build-essential bubblewrap ca-certificates curl openssl tzdata libsqlite3-0 libcurl4t64 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data /mailbox && chown worker:worker /data /mailbox
COPY --from=source /opt/build-lean /opt/build-lean
COPY Helper.lean /opt/lean-build/Helper.lean
# Fail at image build time if a selected source release changes the helper APIs.
RUN /opt/build-lean/bin/lean /opt/lean-build/Helper.lean
COPY --from=application /usr/local/bin/cloud-app /usr/local/bin/cloud-app
COPY --from=application /usr/local/bin/cloud-node /usr/local/bin/cloud-node
ENV LEAN_BUILD_TOOLCHAIN=/opt/build-lean
ENV LEAN_BUILD_HELPER=/opt/lean-build/Helper.lean
# The default image checks trusted source in an isolated worker deployment.
# Opt in to bubblewrap's nested namespaces with
# LEAN_BUILD_SANDBOX=1 only on a host configured to support nested namespaces.
ENV LEAN_BUILD_SANDBOX=0
LABEL lean-cloud.node="http-inbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=10s --retries=40 CMD ["cloud-node", "health"]
ENTRYPOINT ["cloud-node"]
