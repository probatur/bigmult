# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd
#
# One command: docker build .   (with BuildKit, add --progress=plain to see every line of the check)
# The build runs check.sh; the build fails if any check fails. The base is the public Coq 8.20.1 image,
# pinned by digest so every rebuild uses the same checker.
FROM coqorg/coq:8.20.1@sha256:e50d77c4c5a9aa0d76ae1b343d79c5f922da3a75054b79c5dc635895438e4674
WORKDIR /home/coq/bigmult
COPY --chown=coq:coq coq/ coq/
COPY --chown=coq:coq check.sh ./
ARG JOBS=2
RUN JOBS=${JOBS} ./check.sh
