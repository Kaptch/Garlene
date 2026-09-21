FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends curl git ca-certificates zstd tzdata

ARG LEAN_VERSION=4.33.1
RUN curl -sSfL "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" -o /tmp/lean.tar.zst \
    && tar --zstd -xf /tmp/lean.tar.zst -C /opt && rm /tmp/lean.tar.zst
ENV PATH="/opt/lean-4.33.1-linux/bin:${PATH}"

ARG OVSC_VERSION=1.103.1
RUN curl -sSfL "https://github.com/gitpod-io/openvscode-server/releases/download/openvscode-server-v${OVSC_VERSION}/openvscode-server-v${OVSC_VERSION}-linux-x64.tar.gz" \
        | tar -xz -C /opt \
    && ln -s "/opt/openvscode-server-v${OVSC_VERSION}-linux-x64/bin/openvscode-server" /usr/local/bin/openvscode-server

RUN useradd -m reviewer

WORKDIR /artifact
COPY --chown=reviewer:reviewer . .
RUN chown reviewer:reviewer /artifact
USER reviewer

RUN lake exe cache get
RUN lake build && lake build Examples
RUN openvscode-server --install-extension leanprover.lean4

EXPOSE 8080
CMD ["openvscode-server", "--host", "0.0.0.0", "--port", "8080", \
     "--without-connection-token", "--default-folder", "/artifact"]
