#!/bin/zsh
# F-036 (C-h6 step F3) main run: every line of population/f036/jobs.txt
# ("n evals seed mode start"), P at a time via xargs -P (`jobs -r` does not work in a
# non-interactive zsh).  Workers exit early if population/f036/ALERT appears.
cd "$(dirname "$0")/.."
: ${F036_CORPUS:?set F036_CORPUS to Patil data/graphs}
export F036_CORPUS
P=${P:-3}
xargs -P $P -L 1 zsh verifier/f036_job.sh < ${JOBS:-population/f036/jobs.txt}
echo "$(date +%FT%T) # ALL JOBS DONE" >> population/f036/summary.log
