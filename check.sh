#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd
#
# Rebuilds every proof from source, then re-checks the whole development with coqchk, Coq's independent
# kernel checker, including the parts of Coq's standard library it uses. Exits non-zero unless every file
# compiles, coqchk accepts everything, and coqchk reports no axioms and no disabled kernel check.
set -euo pipefail
cd "$(dirname "$0")/coq/constraints"
JOBS="${JOBS:-2}"
Q=(-Q . Constraints -Q gen Generated -Q ../spec "")

echo "== 1/3 compile"
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile -j"$JOBS"

echo "== 2/3 independent kernel re-check (coqchk)"
if ! coqchk -o "${Q[@]}" Constraints.bm_adequacy > coqchk.log 2>&1; then
  cat coqchk.log; echo "FAIL: coqchk rejected the development"; exit 1
fi
summary="$(sed -n '/CONTEXT SUMMARY/,$p' coqchk.log)"
[ -n "$summary" ] || { cat coqchk.log; echo "FAIL: coqchk printed no context summary"; exit 1; }
printf '%s\n' "$summary"
for field in "Axioms" "Constants/Inductives relying on type-in-type" \
             "Constants/Inductives relying on unsafe (co)fixpoints" "Inductives whose positivity is assumed"; do
  grep -qF "* $field: <none>" <<<"$summary" || { echo "FAIL: coqchk does not report '$field: <none>'"; exit 1; }
done

echo "== 3/3 the theorem, as the kernel states it, and the two definitions it is stated with"
tmp="$(mktemp -d)"
printf '%s\n' 'Require Import Constraints.bm_adequacy.' 'Check policy_adequacy_bm.' \
              'Print bm_rule.adequate.' 'Print accepts_bm.' \
              'Print Assumptions policy_adequacy_bm.' > "$tmp/Statement.v"
coqc "${Q[@]}" "$tmp/Statement.v"
echo "OK: all checks passed"
