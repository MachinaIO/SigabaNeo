# The environment image (docs/GITHUB_PLATFORM.md, "Environments"): Lean, Mathlib, cslib-frontier,
# the core and SigabaNeoStd built, and the verifier. The DAG's CI runs it without network, token
# or secrets:
#
#   docker run --rm --network none --read-only --cap-drop ALL --cap-add SETUID --cap-add SETGID \
#     --user 0:0 -e SIGABA_LEAN_UID=1000 --tmpfs /work:exec,mode=1777 … IMAGE \
#     verify --dag /base --new /new --out - --env ENV --revision SHA --records /records \
#     --workdir /work/ws > result.json
#
# The gate runs it as root without capabilities except changing users, so that Lean runs as uid
# 1000 apart from the verifier. The default user (1000) suits agents running it locally.
#
# Build from the repository root: docker build -f docker/Dockerfile -t sigaba-neo-env .
# The base image is pinned by digest; update the digest deliberately.
FROM ubuntu:24.04@sha256:562111b88caa79c71391c0c4d3c2114a7d5c35915c20561fd893cb1e07929e6b

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git python3 \
 && rm -rf /var/lib/apt/lists/* \
 && git config --system --add safe.directory '*'
# Lake asks git about the packages; they belong to root and the verifier runs as uid 1000.

ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH HOME=/tmp
COPY lean-toolchain /core/lean-toolchain
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/v4.4.0/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain "$(cat /core/lean-toolchain)" \
 && rm /tmp/elan-init.sh

WORKDIR /core
COPY lakefile.toml lake-manifest.json ./
# The packages and their build caches (docs/M0.md): Mathlib's, then cslib-frontier's.
# `lake exe cache get` resolves the pinned manifest (it never updates it) and fetches Mathlib's cache.
RUN lake exe cache get
RUN LAKE_CACHE_ARTIFACT_ENDPOINT=https://storage.googleapis.com/complexitylib-lake-cache/a0 \
    LAKE_CACHE_REVISION_ENDPOINT=https://storage.googleapis.com/complexitylib-lake-cache/r0 \
    lake cache get --package=cslib-frontier --repo=cslib-community/complexitylib || true

COPY SigabaNeo.lean SigabaNeoStd.lean ./
COPY SigabaNeo ./SigabaNeo
COPY SigabaNeoStd ./SigabaNeoStd
COPY python ./python
COPY schemas ./schemas
# The core's targets, and every module of the packages a DAG node may import from (`IMPORT_ROOTS`
# in python/dag.py) that the core itself does not import: the image's core is read only, so a module
# not built here cannot be imported. Mathlib (and with it Batteries, Aesop, Qq, ...) comes whole from
# its cache; Cslib and CslibFrontier are built from theirs.
RUN lake build SigabaNeo SigabaNeoStd Cslib CslibFrontier \
 && rm -rf python/tests python/__pycache__ \
 && chmod -R a+rX /core /opt/elan

USER 1000:1000
ENTRYPOINT ["python3", "/core/python/dag_verify.py"]
