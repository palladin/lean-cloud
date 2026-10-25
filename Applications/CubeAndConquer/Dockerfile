ARG APPLICATION_IMAGE=lean-cloud-sat-app:dev
FROM ubuntu:24.04 AS tools
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /build
COPY build-tools.sh tools.lock ./
RUN bash build-tools.sh /opt/sat-tools

FROM ${APPLICATION_IMAGE}
COPY --from=tools /opt/sat-tools/bin /opt/sat-tools/bin
COPY --from=tools /opt/sat-tools/tools.lock /opt/sat-tools/bin.sha256 /opt/sat-tools/
# Preserve the exact corresponding upstream sources and license notices.
COPY --from=tools /opt/sat-tools/downloads /opt/sat-tools/sources
ENV LEAN_CLOUD_SAT_TOOLS=/opt/sat-tools/bin LEAN_CLOUD_SAT_CACHE=/data/sat-input
