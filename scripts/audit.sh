#!/usr/bin/env bash
# audit.sh — mechanical realisation of the thesis contribution audit.
#
# Two checks, both of which must pass:
#
#   1. Source sweep: no Admitted, admit, or Axiom outside comments in the
#      thesis sources (src/Finger*.v). The vendored Clairvoyance library is
#      deliberately excluded — it is upstream code, not a thesis artefact.
#
#   2. Assumption audit: compile src/Audit.v, which runs Print Assumptions
#      on every headline theorem, and fail if any assumption other than
#      Classical_Prop.classic (inherited from the vendored library) appears.
#
# Run via `make audit` (which builds the development first). Requires the
# .vo files to be up to date.

set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

echo "== [1/2] Source sweep: Admitted / admit / Axiom in src/Finger*.v =="
# Strip (possibly nested) Coq comments, then grep what remains. A hit inside
# a comment is documentation; a hit outside one is an unproven obligation.
sweep=$(perl -ne '
  BEGIN { $d = 0 }
  my $code = "";
  while (/(\(\*|\*\)|[^(*]+|[(*])/g) {
    my $t = $1;
    if    ($t eq "(*") { $d++ }
    elsif ($t eq "*)") { $d-- if $d > 0 }
    elsif ($d == 0)    { $code .= $t }
  }
  print "$ARGV:$.: $_" if $code =~ /\b(Admitted|admit|Axiom)\b/;
  close ARGV if eof;
' src/Finger*.v) || true
if [ -n "$sweep" ]; then
  printf '%s\n' "$sweep"
  echo "FAIL: unexpected Admitted/admit/Axiom in thesis sources."
  fail=1
else
  echo "OK: no Admitted, admit, or Axiom outside comments."
fi

echo
echo "== [2/2] Assumption audit: Print Assumptions on headline theorems =="
out=$("${COQBIN:-}coqc" -Q src Clairvoyance src/Audit.v)
printf '%s\n' "$out"
# Print Assumptions lists each axiom as "<name> : <type>" starting in column
# 0 (continuation lines are indented). Anything not on the allowlist fails.
bad=$(printf '%s\n' "$out" | grep -E '^[^[:space:]]+ : ' | grep -vE '^Classical_Prop\.classic : ') || true
if [ -n "$bad" ]; then
  echo "FAIL: assumptions outside the allowlist:"
  printf '%s\n' "$bad"
  fail=1
else
  echo "OK: every headline theorem is closed modulo Classical_Prop.classic."
fi

exit "$fail"
