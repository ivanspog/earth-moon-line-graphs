#!/bin/sh
# f034_a4_certify.sh <index> — Lean certification of one A4 UNSAT (P-008 A(ii)).
#
#   1. replay   f034_a4_line_graph_sat.py <i> --dump: the untrusted clause
#               generator. It must reproduce the original run's final `stats:`
#               line (population/f034-a4/member-<i>.log) exactly.
#   2. resolve  lean_static_resolve.py (streaming): static formula unit +
#               counters + lex + dumped clauses, CaDiCaL LRAT, external
#               lrat-check, and the LRAT core (witnesses.txt, core.json with the
#               counter_free flag).
#   3. lean     (A, under the Lean lock) lean_instance.py + registry entry; an
#               independent check that the Lean graph is L(M)
#               (f038_lean_graph_check.py); `biplanar-export` writes the
#               Lean-defined F. (B, unlocked) tautology scan; lex differential
#               check; CaDiCaL LRAT on that F; lrat-check. (C, under the lock)
#               `lake build` of the theorem module (accepted on build status,
#               never on the axiom line alone). The lock serialises only the
#               registry edits and lake; the solve runs outside it (F-038 §7.2).
#
# Disk: the dump, every LRAT, both CNFs and the theorem .olean (it embeds the
# certificate) are deleted once their check has passed. What stays: the
# verdicts, the SHA-256s (MANIFEST.txt, summary.json), the checker outputs,
# witnesses.txt and the Lean files. The script stops with exit 3 if a step
# could leave less than 10 GB free.
#
# Metrics go to population/f034-a4-cert/metrics.tsv (member, metric, value).
set -e
cd "$(dirname "$0")/.."
[ -n "$1" ] || { echo "usage: f034_a4_certify.sh <index>"; exit 2; }
i=$(printf %02d "$1")
# F034_TAG (optional, e.g. "t"): a scratch copy under key a4_m<i><tag>, name
# A4M<i><TAG> and dir m<i><tag>, for testing the chain on a certified member
tag=${F034_TAG:-}
key=a4_m$i$tag
name=A4M$i$(echo "$tag" | tr a-z A-Z)
ROOT=$(pwd)   # absolute paths below: step 4 runs inside lean/
top=$ROOT/population/f034-a4-cert
out=$top/m$i$tag
PY=$ROOT/.venv/bin/python
LRATCHECK=$ROOT/tools/drat-trim/lrat-check
mkdir -p "$out"

log() { echo "[cert $i$tag] $(date '+%F %T') $*"; }
metric() { printf '%s\t%s\t%s\n' "$i$tag" "$1" "$2" >> "$top/metrics.tsv"; log "metric $1 = $2"; }
free_gb() { df -k . | tail -1 | awk '{printf "%d", $4 / 1048576}'; }
need() {  # need <GB>: stop if writing about <GB> more would leave < 10 GB free
  f=$(free_gb)
  if [ $((f - $1)) -lt 10 ]; then
    log "DISK STOP: $f GB free, next step may write ~$1 GB"; exit 3
  fi
}
bytes() { stat -f %z "$1"; }
gb_of() { echo $(( ($1 + 1073741823) / 1073741824 )); }
sha() { shasum -a 256 "$1" | cut -d' ' -f1; }

log "start; $(free_gb) GB free"
metric free_gb_start "$(free_gb)"

locked=0
lock() { until mkdir "$top/lean.lock" 2>/dev/null; do sleep 20; done; locked=1; }
unlock() { rmdir "$top/lean.lock" 2>/dev/null; locked=0; }
trap '[ "$locked" = 1 ] && rmdir "$top/lean.lock" 2>/dev/null' EXIT

res=$out/resolve
if [ -f "$res/core.json" ] && [ -f "$res/summary.json" ] && [ ! -f "$out/dump.jsonl" ]; then
  # resume: steps 1-2 finished earlier (their outputs and metrics are on disk)
  log "resuming at step 3 (core already extracted)"
else
# ---- 1. replay with dump --------------------------------------------------
need 2
t0=$(date +%s)
$PY -u verifier/f034_a4_line_graph_sat.py "$1" --dump "$out/dump.jsonl" > "$out/replay.log" 2>&1 \
  || { log "replay crashed"; tail -5 "$out/replay.log"; exit 1; }
t1=$(date +%s)
grep -q '^RESULT .* UNSAT' "$out/replay.log" || { log "replay did not end UNSAT"; tail -3 "$out/replay.log"; exit 1; }
orig=$(grep 'stats:' "population/f034-a4/member-$i.log" | tail -1 | sed 's/^.*stats: //')
new=$(grep 'stats:' "$out/replay.log" | tail -1 | sed 's/^.*stats: //')
if [ "$orig" != "$new" ]; then log "REPLAY DIVERGED: original $orig / replay $new"; exit 1; fi
log "replay UNSAT, identical stats $new"
metric replay_s $((t1 - t0))
metric replay_stats "$new"
dump_b=$(bytes "$out/dump.jsonl")
metric dump_bytes "$dump_b"
metric dump_sha256 "$(sha "$out/dump.jsonl")"

# ---- 2. static re-solve + core (Python-side formula, external lrat-check) --
need $(( 3 * $(gb_of "$dump_b") + 1 ))
t0=$(date +%s)
$PY -u verifier/lean_static_resolve.py "$out/dump.jsonl" --out "$res" > "$out/resolve.out" 2>&1 \
  || { log "static re-solve crashed (or lrat-check failed)"; tail -5 "$out/resolve.out"; exit 1; }
t1=$(date +%s)
grep -q 'DONE: UNSAT certified externally' "$out/resolve.out" || { log "static re-solve failed"; tail -5 "$out/resolve.out"; exit 1; }
grep -q 'c VERIFIED' "$res/resolve.log" || { log "no lrat-check VERIFIED line"; exit 1; }
metric resolve_wall_s $((t1 - t0))
metric resolve_lrat_bytes "$(bytes "$res/F.lrat")"
metric resolve_cnf_bytes "$(bytes "$res/F.cnf")"
metric core_witnesses "$(wc -l < "$res/witnesses.txt" | tr -d ' ')"
metric counter_free "$($PY -c "import json,sys; print(json.load(open(sys.argv[1]))['counter_free'])" "$res/core.json")"
# the dump and the Python-side certificate have done their job: record, delete
rm -f "$out/dump.jsonl" "$res/F.lrat" "$res/F.cnf" "$res/dump_core.jsonl"
log "deleted dump + Python-side CNF/LRAT (hashes in $res/summary.json)"
fi
rlrat_b=$($PY -c "import json,sys; print(json.load(open(sys.argv[1]))['rounds'][-1]['lrat_bytes'])" "$res/summary.json")
cf=$($PY -c "import json,sys; print(json.load(open(sys.argv[1]))['counter_free'])" "$res/core.json")
nwit=$(wc -l < "$res/witnesses.txt" | tr -d ' ')

# ---- 3A. Lean instance, registry, export (under the lock) ------------------
lock
mults=$(sed -n 's/^# A4 member [0-9]*: .*mults=\[\([^]]*\)\].*/\1/p' "$out/replay.log")
nc=""; lexc="--counters"
if [ "$cf" = True ]; then nc="--no-counters"; lexc=""; fi
$PY verifier/lean_instance.py "$res" --key "$key" --name "$name" $nc \
  --doc "A4 member $i of F-034: the line graph L(M) of the 7-vertex multigraph M with multiplicities [$mults] (n = 28); P-008 A(ii) rests on its non-biplanarity" \
  > "$out/instance.out"
$PY verifier/lean_registry.py add "$key" "$name"
# the Lean statement must be about L(M): independent of build(), before any Lean compute
$PY verifier/f038_lean_graph_check.py --file "lean/Biplanar/Instances/$name/Defs.lean" > "$out/graph-check.txt" 2>&1 \
  || { log "LEAN GRAPH IS NOT L(M)"; cat "$out/graph-check.txt"; exit 1; }
cat "$out/graph-check.txt"

cd lean
export PATH="$HOME/.elan/bin:$PATH"
d=data/$key
need 3
t0=$(date +%s)
lake build Biplanar.Instances biplanar-export > "$out/lake-export.log" 2>&1 \
  || { log "registry/exporter build failed"; tail -20 "$out/lake-export.log"; exit 1; }
lake exe biplanar-export "$key" "$d/F.cnf" >> "$out/lake-export.log" 2>&1 \
  || { log "biplanar-export refused"; tail -5 "$out/lake-export.log"; exit 1; }
t1=$(date +%s)
metric lean_export_s $((t1 - t0))
metric lean_cnf_bytes "$(bytes "$d/F.cnf")"
cd ..
unlock

# ---- 3B. checks and the Lean-side solve (unlocked) --------------------------
# independent tautology scan of the exported formula (the tautology trap)
$PY verifier/cnf_tautology_scan.py "lean/$d/F.cnf" > "$out/taut.out" 2>&1 \
  || { log "TAUTOLOGY in exported F"; cat "$out/taut.out"; exit 1; }
cat "$out/taut.out"
$PY verifier/lex_encoding_diff.py --key "$key" --graph "$res/graph.json" $lexc > "$out/lexdiff.out" 2>&1 \
  || { log "lex differential check FAILED"; cat "$out/lexdiff.out"; exit 1; }
cat "$out/lexdiff.out"

cd lean
lrat_guess=$(( 2 * $(gb_of "$rlrat_b") + 1 ))   # Python-side LRAT size as the yardstick
need "$lrat_guess"
t0=$(date +%s)
set +e
cadical --lrat --no-binary --no-factor "$d/F.cnf" "$d/F.lrat" > "$d/cadical.log" 2>&1
rc=$?
set -e
t1=$(date +%s)
if [ "$rc" -ne 20 ]; then log "Lean-side cadical exit $rc (20 = UNSAT expected)"; exit 1; fi
metric lean_cadical_s $((t1 - t0))
metric lean_lrat_bytes "$(stat -f %z "$d/F.lrat")"
t0=$(date +%s)
$LRATCHECK "$d/F.cnf" "$d/F.lrat" > "$out/lratcheck.out" 2>&1 || true
t1=$(date +%s)
grep -q '^c VERIFIED' "$out/lratcheck.out" || { log "lrat-check did NOT verify"; cat "$out/lratcheck.out"; exit 1; }
metric lean_lratcheck_s $((t1 - t0))
cp "$d/cadical.log" "$out/lean-cadical.log"
cd ..

# ---- 3C. build the theorem module (under the lock) -------------------------
lock
cd lean
need "$lrat_guess"   # the theorem .olean embeds the certificate
t0=$(date +%s)
set +e
/usr/bin/time -l lake build "Biplanar.Instances.$name" > "$out/lean-build.log" 2>&1
brc=$?
set -e
t1=$(date +%s)
nerr=$(grep -c 'error' "$out/lean-build.log" || true)
if [ "$brc" -ne 0 ] || [ "$nerr" -ne 0 ] || ! grep -q 'Build completed successfully' "$out/lean-build.log"; then
  log "LEAN BUILD FAILED (rc $brc, $nerr error lines) — the axiom line below is NOT a result"
  grep -E 'error|axioms' "$out/lean-build.log" | head -10; exit 1
fi
metric lean_build_s $((t1 - t0))
metric lean_build_maxrss_bytes "$(awk '/maximum resident set size/ {print $1}' "$out/lean-build.log")"
awk '/depends on axioms/,/\]/' "$out/lean-build.log" | tr -s ' \n' ' ' > "$out/axioms.txt"
echo >> "$out/axioms.txt"
log "axioms: $(cat "$out/axioms.txt")"
{
  echo "# $(date)  cadical $(cadical --version)  lean $(cat lean-toolchain)  (f034_a4_certify.sh)"
  echo "# member $i: $name, counter_free=$cf, $nwit witnesses"
  shasum -a 256 "$d/witnesses.txt" "$d/F.cnf" "$d/F.lrat"
} > "$d/MANIFEST.txt"
cp "$d/MANIFEST.txt" "$out/MANIFEST.txt"
metric lean_lrat_sha256 "$(shasum -a 256 "$d/F.lrat" | cut -d' ' -f1)"
metric lean_cnf_sha256 "$(shasum -a 256 "$d/F.cnf" | cut -d' ' -f1)"
# delete the certificate and its embedded copy; a rebuild regenerates both
# (lake exe biplanar-export + cadical, see lean/README.md)
rm -f "$d/F.lrat" "$d/F.cnf"
rm -f .lake/build/lib/lean/Biplanar/Instances/$name.olean* \
      .lake/build/lib/lean/Biplanar/Instances/$name.ilean* \
      .lake/build/lib/lean/Biplanar/Instances/$name.trace
cd ..
unlock
cmp -s "$res/witnesses.txt" "lean/$d/witnesses.txt" && rm -f "$res/witnesses.txt"
metric free_gb_end "$(free_gb)"
log "CERTIFIED: Biplanar.$name.not_biplanar (lrat-check VERIFIED, lake build OK)"
