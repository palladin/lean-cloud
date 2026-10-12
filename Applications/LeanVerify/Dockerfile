ARG APPLICATION_IMAGE=lean-cloud-verify-app:dev
FROM ubuntu:24.04 AS checker
ARG TARGETARCH
ARG VERIFY_LEAN_VERSION=4.34.1
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl zstd \
    && rm -rf /var/lib/apt/lists/*
RUN set -eu; \
    case "$TARGETARCH" in arm64) platform=linux_aarch64 ;; amd64) platform=linux ;; *) exit 1 ;; esac; \
    curl -fL --retry 3 --connect-timeout 20 --max-time 300 \
      "https://github.com/leanprover/lean4/releases/download/v${VERIFY_LEAN_VERSION}/lean-${VERIFY_LEAN_VERSION}-${platform}.tar.zst" \
      | tar --zstd -x -C /opt; \
    mv "/opt/lean-${VERIFY_LEAN_VERSION}-${platform}" /opt/verify-lean
FROM ${APPLICATION_IMAGE} AS application

# Keep the large toolchain layer independent of application-code changes.
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    git build-essential ca-certificates curl openssl tzdata libsqlite3-0 libcurl4t64 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data /mailbox && chown worker:worker /data /mailbox
COPY --from=checker /opt/verify-lean /opt/verify-lean
COPY Helper.lean /opt/lean-verify/Helper.lean
COPY LICENSE-LeanChecker /opt/lean-verify/LICENSE-LeanChecker
COPY --from=application /usr/local/bin/cloud-app /usr/local/bin/cloud-app
COPY --from=application /usr/local/bin/cloud-node /usr/local/bin/cloud-node
ENV LEAN_VERIFY_TOOLCHAIN=/opt/verify-lean
ENV LEAN_VERIFY_HELPER=/opt/lean-verify/Helper.lean
LABEL lean-cloud.node="http-inbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=10s --retries=40 CMD ["cloud-node", "health"]
ENTRYPOINT ["cloud-node"]
