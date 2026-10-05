#!/bin/zsh
# F-035: SAT on the circulant-join members that survive every count, xargs -P throttle
# (`jobs -r` does NOT work in non-interactive zsh), perl-alarm box per member.
# Input: population/f035-sat-queue.txt, one "s m S1,S2,.. [--no-sym]" per line.
cd "$(dirname "$0")/.."
BOX=${BOX:-7200}
P=${P:-2}
mkdir -p population/f035-sat
cat population/f035-sat-queue.txt |
  xargs -P $P -L 1 zsh -c 'tag="K$1vC$2($3)${4:+_nosym}"; log="population/f035-sat/$tag.log";
    perl -e "alarm '"$BOX"'; exec @ARGV" .venv/bin/python -u verifier/f035_sat_one.py "$@" > "$log" 2>&1;
    out=$(grep "^RESULT" "$log"); echo "$(date +%FT%T) ${out:-TIMEOUT $tag (box '"$BOX"' s)}" >> population/f035-sat/summary.log' 0
echo "$(date +%FT%T) # DONE" >> population/f035-sat/summary.log
