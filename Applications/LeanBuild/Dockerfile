ARG APPLICATION_IMAGE=lean-cloud-build-app:dev
FROM ${APPLICATION_IMAGE} AS application

# Workers download the pinned toolchain directly; it is not shipped in the image.
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    git build-essential ca-certificates curl openssl tzdata libsqlite3-0 libcurl4t64 zstd \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 10001 worker \
    && mkdir /data /mailbox && chown worker:worker /data /mailbox
COPY Helper.lean /opt/lean-build/Helper.lean
ARG TARGETARCH
ARG SOURCE_LEAN_VERSION=4.35.0
ARG LEAN_LINUX_SHA256
ARG LEAN_ARM64_SHA256
RUN set -eu; \
    case "$TARGETARCH" in \
      arm64) platform=linux_aarch64; digest="$LEAN_ARM64_SHA256" ;; \
      amd64) platform=linux; digest="$LEAN_LINUX_SHA256" ;; *) exit 1 ;; esac; \
    test "${#digest}" = 64; case "$digest" in *[!a-f0-9]*) exit 1 ;; esac; \
    printf '{"version":"%s","platform":"%s","sha256":"%s"}\n' \
      "$SOURCE_LEAN_VERSION" "$platform" "$digest" > /opt/lean-build/toolchain.json
COPY --from=application /usr/local/bin/cloud-app /usr/local/bin/cloud-app
COPY --from=application /usr/local/bin/cloud-node /usr/local/bin/cloud-node
ENV LEAN_BUILD_RELEASE=/opt/lean-build/toolchain.json
ENV LEAN_BUILD_TOOLCHAINS=/data/toolchains
ENV LEAN_BUILD_HELPER=/opt/lean-build/Helper.lean
ENV LEAN_BUILD_CACHE=/data/build-cache
LABEL lean-cloud.node="http-inbox-v1"
HEALTHCHECK --interval=3s --timeout=5s --start-period=12m --retries=40 CMD ["cloud-node", "health"]
ENTRYPOINT ["cloud-node"]
