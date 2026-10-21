# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd
#
# One command: docker build .   (with BuildKit, add --progress=plain to see every line of the check)
# The build runs check.sh; the build fails if any check fails. The base is the public Rocq 9.2 image,
# pinned by digest so every rebuild uses the same checker. The Coq 8.20.1 version is checked by Dockerfile.legacy.
FROM rocq/rocq-prover:9.2@sha256:33926fb3757b2b560c3844157bd64173a26b6d338a256be1ae5eec8df2019025
WORKDIR /home/rocq/bigmult
COPY --chown=rocq:rocq coq/ coq/
COPY --chown=rocq:rocq check.sh ./
ARG JOBS=2
RUN JOBS=${JOBS} ./check.sh
