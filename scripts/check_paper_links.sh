#!/usr/bin/env bash
# Fetch every source link in a paper and report the ones that do not resolve.
#
#   bash scripts/check_paper_links.sh papers/lpar-queens/sat-queens.tex
#
# The links are built from \repoowner and \reporef in the preamble, so a 404 means one of:
#   * \reporef is not reachable from any ref pushed to \repoowner (the usual cause: not pushed);
#   * the file was renamed or removed at that commit;
#   * \repoowner is the wrong repository.
# Line anchors are not checked here -- GitHub returns 200 for an out-of-range #L anchor. Use
# scripts/check_paper_anchors.py for those.
set -uo pipefail

tex=${1:-papers/lpar-queens/sat-queens.tex}
[ -f "$tex" ] || { echo "no such file: $tex" >&2; exit 2; }

owner=$(grep -o '\\newcommand{\\repoowner}{[^}]*}' "$tex" | sed 's/.*{\(.*\)}/\1/')
ref=$(grep -o '\\newcommand{\\reporef}{[^}]*}'   "$tex" | sed 's/.*{\(.*\)}/\1/')
base="https://github.com/$owner/blob/$ref"
echo "repository : $owner"
echo "commit     : $ref"
echo

# \qsrc{file}{line} and \qusrc{file}{line} expand to the two directories; \src{path} is a bare path.
paths=$( { grep -o '\\qsrc{[^}]*}'  "$tex" | sed 's/.*{\(.*\)}/HopfieldNet\/QUBO\/Instances\/Queens\/\1/'
           grep -o '\\qusrc{[^}]*}' "$tex" | sed 's/.*{\(.*\)}/HopfieldNet\/QUBO\/\1/'
           grep -o '\\src{[^}]*}'   "$tex" | sed 's/.*{\(.*\)}/\1/'; } | sort -u )

[ -n "$paths" ] || { echo "no source links found"; exit 0; }

fail=0 n=0
while read -r p; do
  [ -n "$p" ] || continue
  n=$((n+1))
  code=$(curl -s -o /dev/null -w '%{http_code}' -L --max-time 20 "$base/$p")
  if [ "$code" = "200" ]; then
    printf '  %-4s %s\n' "ok" "$p"
  else
    printf '  %-4s %s\n' "$code" "$p"
    fail=$((fail+1))
  fi
done <<< "$paths"

echo
if [ "$fail" -eq 0 ]; then
  echo "all $n distinct source files resolve"
else
  echo "$fail of $n distinct source files do NOT resolve"
  echo
  echo "check whether the commit is pushed:"
  echo "  git branch -r --contains $ref"
  echo "  git ls-remote --heads https://github.com/$owner.git"
fi
exit $fail
