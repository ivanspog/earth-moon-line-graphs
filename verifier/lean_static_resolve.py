"""Static re-solve of a clause dump (Lean-verification milestone, P1 step 2).

Input: a JSONL clause dump written by `biplanar_sat_prop.py --dump-clauses`
(pre-seeds + every propagator/model Kuratowski clause, each with an explicit
subdivision certificate). The propagator run itself is UNTRUSTED here: it
is only a heuristic clause generator. What gets certified is the STATIC
formula

    F := {edge0 -> part1} ∪ cube units ∪ card(part2 <= 3n-6)
         ∪ card(part1 <= 3n-6) ∪ lex blocks ∪ dumped Kuratowski clauses

re-solved from scratch by the CaDiCaL binary with native LRAT output
(`cadical --lrat --no-binary --no-factor`, the LRAT-Catcher recipe), then
checked externally by `lrat-check` (drat-trim repo) BEFORE Lean sees it.

The LRAT certificate's hint graph gives the UNSAT CORE: the set of original
clauses actually used. Only the dumped clauses in the core are kept
(`dump_core.jsonl`, `witnesses.txt`), which is what the Lean side imports;
`core.json` records which base clauses the core used (`counter_free`: only
units and lex, so the Lean side may use `mkCNFSym₀` and drop (H1)).
`--iterate` repeats solve → core until the core stops shrinking. Every
round re-solves and re-checks, so the final (F.cnf, F.lrat, witnesses.txt)
triple is self-consistent and checksummed in `summary.json`.

Options for the split route (F-038 §8): `--cube L1 L2 …` adds unit clauses
(DIMACS literals on the edge variables) after the part-swap unit, so each
cube of a cube-and-conquer split is re-solved separately and gets its own
core; `--no-counters` leaves the two cardinality counters out (valid
whenever the refutation never needs Euler's bound — every A4 core so far).

Memory (F-038 §7.2): the dump is STREAMED. One pass de-duplicates,
re-validates every certificate and writes the DIMACS lines of the distinct
clauses straight to disk; per clause only a compact de-duplication key and
the byte offset of its dump line stay in memory, and the certificates of the
core are re-read by offset at the end. The LRAT core is a bitmap scan. (The
previous version held every clause with its certificate, ~2.5 KB each.)

Why the Python base encoding here may differ from the Lean encoder's:
both are exact encodings of the same cardinality constraints on the edge
variables (Sinz sequential counter in both cases), so their projections to
the edge variables coincide; UNSAT of base_py ∪ D therefore implies UNSAT
of base_lean ∪ D for any dumped subset D. The Lean side re-solves ITS OWN
exported F and imports that certificate — this script's certificate is a
pre-check and a core reducer, never the one Lean trusts.

Usage:
  .venv/bin/python verifier/lean_static_resolve.py DUMP.jsonl --out DIR \
      [--iterate 3] [--allow-sym] [--no-counters] [--cube L1 L2 ...]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import resource
import shutil
import subprocess
import sys
import time
from array import array

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

sys.path.insert(0, os.path.dirname(__file__))
from biplanar_sat import lex_leq  # noqa: E402
from kuratowski_cert import cert_to_lean_line, certificate_valid  # noqa: E402

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
DEFAULT_LRAT_CHECK = os.path.join(ROOT, "tools", "drat-trim", "lrat-check")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Dumped:
    """The distinct, re-validated clauses of a dump, held as the byte offsets
    of their dump lines (8 bytes each). Indexing re-reads the line and returns
    {"pol", "e", "c", "t"}; indices are in first-occurrence (dump) order."""

    def __init__(self, path, offsets):
        self.path = path
        self.off = offsets
        self._f = None

    def __len__(self):
        return len(self.off)

    def __getitem__(self, i):
        if self._f is None:
            self._f = open(self.path, "rb")
        self._f.seek(self.off[i])
        obj = json.loads(self._f.readline())
        return {"pol": int(obj["pol"]), "e": list(obj["e"]), "c": obj["c"],
                "t": obj.get("t")}

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def subset(self, idxs):
        return Dumped(self.path, array("Q", (self.off[i] for i in idxs)))


def clause_line(pol, e):
    sign = -1 if pol else 1
    return " ".join(str(sign * (i + 1)) for i in e) + " 0\n"


def read_dump(path, body=None):
    """Stream the dump: header, the distinct re-validated clauses (first
    occurrence of each (polarity, edge set) wins) as a `Dumped`, footer, raw
    line count. With `body`, also write the DIMACS line of every distinct
    clause, in order, to that file."""
    header, footer = None, None
    edges, m = None, 0
    seen = set()
    off = array("Q")
    raw = bad = 0
    out = open(body, "w") if body else None
    with open(path, "rb") as f:
        pos = 0
        for line in f:
            start = pos
            pos += len(line)
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            t = obj.get("type")
            if t == "header":
                header = obj
                edges = [tuple(e) for e in header["edges"]]
                m = len(edges)
                continue
            if t == "footer":
                footer = obj
                continue
            assert header is not None, "clause line before header"
            raw += 1
            e = obj["e"]
            assert all(0 <= i < m for i in e), f"edge index out of range: {obj}"
            pol = int(obj["pol"])
            se = sorted(e)
            key = bytes([pol]) + bytes(se) if m < 256 else (pol, tuple(se))
            if key in seen:
                continue
            seen.add(key)
            if not certificate_valid(obj["c"], {edges[i] for i in e}):
                bad += 1
                continue  # reject: never let an unverified clause through
            off.append(start)
            if out:
                out.write(clause_line(pol, e))
    if out:
        out.close()
    assert header is not None, "dump has no header"
    assert bad == 0, f"{bad} dumped clauses failed certificate re-validation"
    return header, edges, Dumped(path, off), footer, raw


class _CollectSolver:
    """Minimal `solver` shim so `lex_leq` can be reused verbatim."""

    def __init__(self, out):
        self.out = out

    def add_clause(self, cl):
        self.out.append(list(cl))


def base_formula(header, edges, counters=True, cube=()):
    """Base clauses exactly as biplanar_sat_prop.solve() lays them out: the
    part-swap unit, unit clauses (the header's cube units, then `cube`), both
    counters (unless `counters` is False), one lex block per recorded
    generator. Returns (clauses, num_vars, layout); layout gives 1-based id
    ranges per block and `num_base`."""
    m = len(edges)
    cap = header["cap"]
    assert cap == 3 * header["n"] - 6
    pool = IDPool(start_from=m + 1)
    x = list(range(1, m + 1))
    cls = [[-x[0]]]
    layout = {"unit": [1, 1]}
    units = [int(u) for u in (header.get("extra_units") or [])] + [int(u) for u in cube]
    assert all(0 < abs(u) <= m for u in units), "cube literals must be edge variables"
    for lit in units:
        cls.append([lit])
    if units:
        layout["extra_units"] = [2, len(cls)]
    if counters:
        lo = len(cls) + 1
        for cnf in (CardEnc.atmost(lits=x, bound=cap, vpool=pool,
                                   encoding=EncType.seqcounter),
                    CardEnc.atleast(lits=x, bound=max(0, m - cap), vpool=pool,
                                    encoding=EncType.seqcounter)):
            cls.extend(cnf.clauses)
        layout["counters"] = [lo, len(cls)]
    gens = header.get("gens") or []
    if gens:
        lo = len(cls) + 1
        for gi, g in enumerate(gens):
            ep = g["eperm"]
            assert sorted(ep) == list(range(m)), \
                f"generator {gi}: eperm is not a permutation of the edge indices"
            lex_leq(_CollectSolver(cls), pool, x, [x[ep[i]] for i in range(m)],
                    ("lex", gi))
        layout["lex"] = [lo, len(cls)]
    layout["num_base"] = len(cls)
    return cls, max(pool.top, m), layout


def build_formula(header, edges, dumped, counters=True, cube=()):
    """Base + dumped clauses as one in-memory list (small inputs, and the
    layout-only call `build_formula(header, edges, [])` of lrat_tools)."""
    cls, nv, layout = base_formula(header, edges, counters, cube)
    for d in dumped:
        sign = -1 if d["pol"] else 1
        cls.append([sign * (i + 1) for i in d["e"]])
    return cls, nv, layout


def write_dimacs(path, base_cls, nv, body, n_body):
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(base_cls) + n_body}\n")
        for c in base_cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    with open(path, "ab") as f, open(body, "rb") as b:
        shutil.copyfileobj(b, f, 1 << 22)


def run(cmd, log):
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    dt = time.time() - t0
    with open(log, "a") as f:
        f.write(f"$ {' '.join(cmd)}\n{p.stdout}{p.stderr}\n[rc={p.returncode} "
                f"{dt:.1f}s]\n")
    return p.returncode, dt, p.stdout


def _reverse_lines(path, chunk=1 << 22):
    """Yield the lines of a text file from last to first without loading it."""
    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        pos = f.tell()
        rest = b""
        while pos > 0:
            size = min(chunk, pos)
            pos -= size
            f.seek(pos)
            buf = f.read(size) + rest
            lines = buf.split(b"\n")
            rest = lines[0]
            for ln in reversed(lines[1:]):
                if ln:
                    yield ln.decode()
        if rest:
            yield rest.decode()


def lrat_core(lrat_path, num_orig):
    """(sorted original clause ids reachable from the empty clause through the
    LRAT hint graph, number of LRAT lines). One forward scan (empty-clause id,
    largest id), one reverse scan over bitmaps (hints only reference earlier
    ids), so memory is two bytes per clause id. RAT hints (negative ids) are
    taken by absolute value, which can only enlarge the core (sound)."""
    empty_id = max_id = nlines = 0
    with open(lrat_path, "rb") as f:
        for line in f:
            nlines += 1
            toks = line.split()
            if len(toks) < 2 or toks[1] == b"d":
                continue
            cid = int(toks[0])
            if cid > max_id:
                max_id = cid
            if len(toks) >= 3 and toks[1] == b"0":
                empty_id = cid            # "id 0 hints... 0": empty clause
    assert empty_id, "LRAT has no empty-clause step"
    need = bytearray(max(max_id, num_orig) + 1)
    need[empty_id] = 1
    core = bytearray(num_orig + 1)
    for line in _reverse_lines(lrat_path):
        toks = line.split()
        if len(toks) < 2 or toks[1] == "d":
            continue
        cid = int(toks[0])
        if not need[cid]:
            continue
        need[cid] = 0
        i = 1
        while toks[i] != "0":          # skip literals
            i += 1
        i += 1
        while i < len(toks) and toks[i] != "0":
            h = abs(int(toks[i]))
            if h <= num_orig:
                core[h] = 1
            else:
                need[h] = 1
            i += 1
    return [i for i in range(1, num_orig + 1) if core[i]], nlines


def solve_round(header, edges, dumped, outdir, cadical, lrat_check, log,
                counters=True, cube=(), body=None):
    """One static solve of base ∪ `dumped`. `body` is a ready DIMACS file of
    the dumped clauses (round 0); otherwise it is written from `dumped`."""
    os.makedirs(outdir, exist_ok=True)
    base_cls, nv, layout = base_formula(header, edges, counters, cube)
    num_base = layout["num_base"]
    cnf = os.path.join(outdir, "F.cnf")
    lrat = os.path.join(outdir, "F.lrat")
    if body is None:
        body = os.path.join(outdir, "body.cnf")
        with open(body, "w") as f:
            for d in dumped:
                f.write(clause_line(d["pol"], d["e"]))
    write_dimacs(cnf, base_cls, nv, body, len(dumped))
    os.remove(body)
    num_clauses = num_base + len(dumped)
    rc, dt_solve, _ = run([cadical, "--lrat", "--no-binary", "--no-factor",
                           cnf, lrat], log)
    if rc == 10:
        return {"verdict": "SAT", "num_clauses": num_clauses, "num_vars": nv,
                "num_base": num_base, "layout": layout,
                "solve_s": round(dt_solve, 1)}
    assert rc == 20, f"cadical exit code {rc} (see {log})"
    rc2, dt_check, out = run([lrat_check, cnf, lrat], log)
    verified = rc2 == 0 and "VERIFIED" in out
    assert verified, f"lrat-check did NOT verify {lrat} (see {log})"
    core, nlines = lrat_core(lrat, num_clauses)
    core_dumped = [i - num_base - 1 for i in core if i > num_base]
    core_base_ids = [i for i in core if i <= num_base]
    return {"verdict": "UNSAT", "num_clauses": num_clauses, "num_vars": nv,
            "num_base": num_base, "layout": layout, "num_dumped": len(dumped),
            "solve_s": round(dt_solve, 1), "check_s": round(dt_check, 1),
            "lrat_lines": nlines,
            "lrat_bytes": os.path.getsize(lrat),
            "core_base": len(core_base_ids), "core_dumped": len(core_dumped),
            "core_dumped_idx": core_dumped, "core_base_ids": core_base_ids,
            "cnf": cnf, "lrat": lrat}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dump")
    ap.add_argument("--out", required=True)
    ap.add_argument("--cadical", default=shutil.which("cadical") or "cadical")
    ap.add_argument("--lrat-check", default=DEFAULT_LRAT_CHECK)
    ap.add_argument("--iterate", type=int, default=1,
                    help="max solve→core rounds (stops early at a fixpoint)")
    ap.add_argument("--allow-sym", action="store_true",
                    help="accept a sym-on dump that records NO generators "
                         "(NOT liftable to Lean; mechanics tests only). "
                         "Sym-on dumps that do record generators are accepted "
                         "without this flag and lift under (H3).")
    ap.add_argument("--no-counters", action="store_true",
                    help="leave the two cardinality counters out of the formula")
    ap.add_argument("--cube", nargs="*", type=int, default=[],
                    help="DIMACS unit literals on edge variables added after the "
                         "part-swap unit (one cube of a split)")
    args = ap.parse_args()
    counters = not args.no_counters

    os.makedirs(args.out, exist_ok=True)
    body0 = os.path.join(args.out, "body0.cnf")
    header, edges, dumped, footer, nraw = read_dump(args.dump, body=body0)
    if header.get("sym_on") and not header.get("gens") and not args.allow_sym:
        os.remove(body0)
        sys.exit("REFUSED: dump comes from a sym-on run and records no "
                 "generators, so its lex clauses cannot be reconstructed or "
                 "proved sound (the Lift lemma would be false). Re-run the "
                 "solver with --no-sym, or with a version that records "
                 "generators in the dump header.")
    if header.get("gens"):
        print(f"[resolve] sym-on dump with {len(header['gens'])} recorded "
              f"generators: the static formula includes their lex blocks; the "
              f"Lean theorem will carry hypothesis (H3).", flush=True)
    if footer is None:
        print("[resolve] WARNING: dump has no footer (run still going or killed);"
              " the static formula is likely satisfiable", flush=True)
    log = os.path.join(args.out, "resolve.log")
    open(log, "w").write(f"# lean_static_resolve {time.strftime('%F %T')}\n"
                         f"# dump={args.dump} raw={nraw} dedup={len(dumped)}"
                         f" footer={footer}\n"
                         + (f"# counters=False\n" if not counters else "")
                         + (f"# cube={args.cube}\n" if args.cube else ""))
    print(f"[resolve] {args.dump}: {nraw} dumped lines, {len(dumped)} "
          f"distinct valid clauses; n={header['n']} m={len(edges)} "
          f"cap={header['cap']} units={header.get('extra_units')}", flush=True)
    if args.cube or not counters:
        print(f"[resolve] cube={args.cube} counters={counters}", flush=True)

    rounds = []
    current = dumped
    body = body0
    for r in range(args.iterate):
        solved = current  # the list the final round's core indices refer to
        res = solve_round(header, edges, current, os.path.join(args.out, f"round-{r}"),
                          args.cadical, args.lrat_check, log, counters=counters,
                          cube=args.cube, body=body)
        body = None
        rounds.append({k: v for k, v in res.items()
                       if k not in ("core_dumped_idx", "core_base_ids")})
        print(f"[resolve] round {r}: {res['verdict']} | clauses={res['num_clauses']} "
              f"vars={res['num_vars']} solve={res['solve_s']}s"
              + (f" check={res['check_s']}s lrat={res['lrat_lines']} lines "
                 f"core: base {res['core_base']}/{res['num_base']}, dumped "
                 f"{res['core_dumped']}/{res['num_dumped']}"
                 if res["verdict"] == "UNSAT" else ""), flush=True)
        if res["verdict"] == "SAT":
            print("[resolve] STATIC FORMULA IS SATISFIABLE — the dump does not "
                  "refute the instance (incomplete run, or the instance is "
                  "biplanar). Nothing to certify.", flush=True)
            json.dump({"verdict": "SAT", "rounds": rounds, "dump": args.dump,
                       "cube": args.cube, "counters": counters},
                      open(os.path.join(args.out, "summary.json"), "w"), indent=1)
            return 1
        if len(res["core_dumped_idx"]) == len(current):
            break
        current = current.subset(res["core_dumped_idx"])
    # final round's artifacts are the deliverable
    final = res
    core_dumped = solved.subset(final["core_dumped_idx"])
    with open(os.path.join(args.out, "dump_core.jsonl"), "w") as f, \
            open(os.path.join(args.out, "witnesses.txt"), "w") as fw:
        f.write(json.dumps({**header, "type": "header",
                            "derived_from": os.path.abspath(args.dump),
                            "core_of": os.path.abspath(final["cnf"])}) + "\n")
        for d in core_dumped:
            f.write(json.dumps({"t": d["t"], "pol": d["pol"], "e": d["e"],
                                "c": d["c"]}, separators=(",", ":")) + "\n")
            fw.write(cert_to_lean_line(d["pol"], d["e"], d["c"]) + "\n")
    layout = final["layout"]
    units_hi = (layout.get("extra_units") or [1, 1])[1]
    lex_lo, lex_hi = layout.get("lex") or (0, -1)
    counter_free = all(i <= units_hi or lex_lo <= i <= lex_hi
                       for i in final["core_base_ids"])
    with open(os.path.join(args.out, "graph.json"), "w") as f:
        json.dump({"name": header["name"], "n": header["n"],
                   "edges": [list(e) for e in edges], "cap": header["cap"],
                   "extra_units": header.get("extra_units") or [],
                   "gens": header.get("gens") or [],
                   "layout": layout, "cube": args.cube, "counters": counters}, f)
    with open(os.path.join(args.out, "core.json"), "w") as f:
        json.dump({"num_orig": final["num_clauses"], "num_base": final["num_base"],
                   "core_base_ids": final["core_base_ids"],
                   "core_dumped": len(core_dumped), "dumped": len(solved),
                   "counter_free": counter_free, "layout": layout,
                   "cube": args.cube, "counters": counters, "footer": footer}, f, indent=1)
    # move, not copy: a copy doubles the disk peak of a multi-GB certificate
    # (F-038); the round directory keeps its log lines, not the files
    os.replace(final["cnf"], os.path.join(args.out, "F.cnf"))
    os.replace(final["lrat"], os.path.join(args.out, "F.lrat"))
    summary = {"verdict": "UNSAT", "dump": os.path.abspath(args.dump),
               "dump_sha256": sha256(args.dump), "rounds": rounds,
               "final_core_dumped": len(core_dumped), "counter_free": counter_free,
               "cube": args.cube, "counters": counters,
               "files": {fn: sha256(os.path.join(args.out, fn)) for fn in
                         ("F.cnf", "F.lrat", "dump_core.jsonl",
                          "witnesses.txt", "graph.json")},
               "python_maxrss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
               * (1 if sys.platform == "darwin" else 1024),   # Linux reports KB
               "cadical": args.cadical, "lrat_check": args.lrat_check,
               "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    json.dump(summary, open(os.path.join(args.out, "summary.json"), "w"), indent=1)
    print(f"[resolve] DONE: UNSAT certified externally; core keeps "
          f"{len(core_dumped)} dumped clauses -> {args.out}/witnesses.txt "
          f"(counter_free={counter_free})", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
