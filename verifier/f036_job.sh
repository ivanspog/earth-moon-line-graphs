#!/bin/zsh
# One F-036 job: $1 = n, $2 = evals, $3 = seed, $4 = mode, $5 = start.
cd "$(dirname "$0")/.."
tag="n$1-$4-s$3"
.venv/bin/python -u verifier/f036_fracsearch.py --n $1 --evals $2 --seed $3 --mode $4 --start $5 --tag $tag \
  > population/f036/$tag.stderr 2>&1
rc=$?
last=$(grep -h -E "# DONE|ALERT" population/f036/$tag.log 2>/dev/null | tail -1)
echo "$(date +%FT%T) finished $tag exit=$rc: $last" >> population/f036/summary.log
