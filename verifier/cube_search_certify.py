#!/usr/bin/env python3
"""F-038 §10: certify a heavy A4 member by PER-CUBE SEARCH (cube-and-conquer from the
propagator up), for the cloud batch.

The split route (a4_split_certify.py) first REPLAYS the member's original
single-threaded search to get one big clause dump, which for member 11 alone is
~20 h on any machine. The solver is only an untrusted clause generator, so
that replay is not needed: here every cube runs its OWN propagator search with
the cube's literals as unit clauses, dumping its own clauses, and a cube that
does not finish within the time limit is split in two and searched again.
Everything downstream is the split route's: per-cube static re-solve and core
(its own witness set), per-cube Lean leaf, cover certificate, and
`Biplanar.not_biplanar_of_cover` (LEAN-2's Sym.lean) composing the per-cube
statements under (H2) and (H3).

Jobs (a work queue, `--workers` at a time):
  search(cube)   f034_a4_line_graph_sat.py <i> --cube … --dump …, time limit
                 `--limit` s.  UNSAT -> static(cube) on that dump.  Timeout ->
                 two search jobs on cube ± e, e = the edge most frequent in the
                 partial dump (not edge 0, not already in the cube).  SAT ->
                 STOP EVERYTHING: a cube SAT would mean the member is biplanar,
                 contradicting the original UNSAT; it needs a human.
  static(cube)   lean_static_resolve.py --no-counters (the dump header carries
                 the search cube; extra literals via --cube).  If its certificate
                 exceeds `--leaf-max` bytes, the cube is bisected STATICALLY on
                 the same dump (no new search).  Otherwise it is a leaf.
The initial cubes come from a short probe of the whole instance
(`--probe` s, `--initial-depth` most frequent pairwise vertex-disjoint edges).
The cubes form a binary tree, so the leaves cover every assignment; the
cover's LRAT certificate checks that anyway.

State is saved after every job (`state.json`); a restart re-queues the jobs
that were running. Disk: new jobs wait while free space < `--floor` GB.

Usage:
  .venv/bin/python -u verifier/cube_search_certify.py 11 --workers 60 --limit 1800 \
      [--probe 300 --initial-depth 6 --leaf-max 1e9 --lean-jobs 12 --floor 20]
"""
import argparse
import hashlib
import itertools
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
PY = os.path.join(ROOT, ".venv", "bin", "python")
LEAN = os.path.join(ROOT, "lean")
LRATCHECK = os.path.join(ROOT, "tools", "drat-trim", "lrat-check")
CERT = os.path.join(ROOT, "population", "f034-a4-cert")
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
DARWIN = sys.platform == "darwin"

STOP = threading.Event()
PROCS = {}            # running child processes, killed on STOP
PROCS_LOCK = threading.Lock()


def log(*a):
    print(f"[cs] {time.strftime('%F %T')}", *a, flush=True)


def free_gb():
    st = os.statvfs(ROOT)
    return st.f_bavail * st.f_frsize / 2 ** 30


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def cid(cube):
    return "root" if not cube else "_".join(f"{'p' if l > 0 else 'n'}{abs(l)}" for l in cube)


def run(cmd, logfile, cwd=ROOT, timeout=None):
    """Run a child process; returns (rc or 'TIMEOUT', seconds). Killable on STOP."""
    t0 = time.time()
    with open(logfile, "w") as f:
        p = subprocess.Popen(cmd, cwd=cwd, env=ENV, stdout=f, stderr=subprocess.STDOUT,
                             start_new_session=True)
        with PROCS_LOCK:
            PROCS[p.pid] = p
        try:
            rc = p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            rc = "TIMEOUT"
        finally:
            with PROCS_LOCK:
                PROCS.pop(p.pid, None)
    if STOP.is_set() and rc != 0:
        rc = "STOPPED"
    return rc, time.time() - t0


def kill_all():
    with PROCS_LOCK:
        for pid in list(PROCS):
            try:
                os.killpg(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


def edge_counts(dump):
    """Edge frequencies over the dumped clauses (a partial dump may end mid-line)."""
    cnt, edges = Counter(), None
    with open(dump) as f:
        for line in f:
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                break
            if obj.get("type") == "header":
                edges = [tuple(e) for e in obj["edges"]]
            elif "e" in obj:
                cnt.update(obj["e"])
    return cnt, edges


def split_edge(dump, cube):
    cnt, _ = edge_counts(dump)
    used = {abs(l) - 1 for l in cube}
    for e, _ in cnt.most_common():
        if e != 0 and e not in used:
            return e
    return None


def initial_edges(dump, k):
    cnt, edges = edge_counts(dump)
    chosen, used = [], set()
    for e, _ in cnt.most_common():
        if e == 0 or used & set(edges[e]):
            continue
        chosen.append(e)
        used |= set(edges[e])
        if len(chosen) == k:
            break
    return chosen


def time_cmd(target):
    return (["/usr/bin/time", "-l"] if DARWIN else ["/usr/bin/time", "-v"]) + target


def parse_rss(out):
    m = re.search(r"(\d+)\s+maximum resident set size", out)
    if m:
        return int(m.group(1))
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", out)
    return int(m.group(1)) * 1024 if m else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("member", type=int)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--limit", type=float, default=1800, help="search time limit per cube (s)")
    ap.add_argument("--probe", type=float, default=300, help="probe of the whole instance (s)")
    ap.add_argument("--initial-depth", type=int, default=4)
    ap.add_argument("--leaf-max", type=float, default=1e9,
                    help="bisect a leaf statically while its Python-side LRAT exceeds this (bytes)")
    ap.add_argument("--min-shrink", type=float, default=0.75,
                    help="bisect a statically split cube again only if its certificate came out "
                         "below this fraction of its parent's")
    ap.add_argument("--max-depth", type=int, default=24)
    ap.add_argument("--lean-jobs", type=int, default=1,
                    help="leaves per `lake build` call, built concurrently by lake (1 = one at a "
                         "time, deleting each certificate after its build)")
    ap.add_argument("--floor", type=float, default=10, help="free-disk floor (GB)")
    ap.add_argument("--from-dump", help="certify from a finished replay's dump (no search)")
    ap.add_argument("--replay-log", help="that replay's log (its stats must match the original run)")
    ap.add_argument("--static-depth", type=int, default=0,
                    help="with --from-dump: initial static split on this many edges")
    ap.add_argument("--key")
    ap.add_argument("--name")
    a = ap.parse_args()
    i = f"{a.member:02d}"
    key = a.key or f"a4_m{i}c"
    name = a.name or f"A4M{i}C"
    top = os.path.join(CERT, f"cs-{key}")
    for d in ("s", "r", "w"):
        os.makedirs(os.path.join(top, d), exist_ok=True)
    ddir = os.path.join(LEAN, "data", key)
    os.makedirs(ddir, exist_ok=True)
    spath = os.path.join(top, "state.json")
    S = json.load(open(spath)) if os.path.exists(spath) else {
        "member": i, "key": key, "name": name, "args": vars(a), "jobs": [], "running": [],
        "leaves": [], "splits": [], "dumps": {}, "stats": {"search_s": 0, "static_s": 0,
                                                          "searches": 0, "timeouts": 0}}
    lock = threading.Lock()

    def save():
        tmp = spath + ".tmp"
        json.dump(S, open(tmp, "w"), indent=1)
        os.replace(tmp, spath)

    log(f"member {i} -> {name} ({key}); {free_gb():.1f} GB free; workers {a.workers}, "
        f"limit {a.limit:.0f}s, leaf-max {a.leaf_max / 1e9:.2f} GB")

    # ---- or: start from a finished replay's dump (static route, no search) ---------
    if a.from_dump and "probe_done" not in S:
        rl = open(a.replay_log).read()
        orig = open(os.path.join(ROOT, "population", "f034-a4", f"member-{i}.log")).read()
        s_orig = orig.split("stats: ")[-1].splitlines()[0]
        s_new = rl.split("stats: ")[-1].splitlines()[0]
        assert re.search(r"^RESULT \S+ UNSAT", rl, re.M), "replay did not end UNSAT"
        assert s_orig == s_new, f"REPLAY DIVERGED: {s_orig} / {s_new}"
        edges = initial_edges(a.from_dump, a.static_depth) if a.static_depth else []
        cubes = [[(e + 1) * sg for e, sg in zip(edges, signs)]
                 for signs in itertools.product((1, -1), repeat=len(edges))]
        S["jobs"] = [{"t": "static", "cube": c, "dump": a.from_dump, "extra": c} for c in cubes]
        S["dumps"][a.from_dump] = len(cubes)
        S.update(probe_done=True, from_dump=a.from_dump, replay_log=a.replay_log,
                 replay_stats=s_new, initial_edges=edges)
        save()
        log(f"from dump {a.from_dump}: replay stats identical to the original run ({s_new}); "
            f"{len(cubes)} initial static cubes on edges {edges}")
    # ---- initial cubes from a probe ---------------------------------------------
    if not S["jobs"] and not S["leaves"] and not S["running"] and "probe_done" not in S:
        pdump = os.path.join(top, "probe.dump.jsonl")
        rc, dt = run([PY, "-u", "verifier/f034_a4_line_graph_sat.py", str(a.member), "--dump", pdump],
                     os.path.join(top, "probe.log"), timeout=a.probe)
        if rc == 0 and "UNSAT" in open(os.path.join(top, "probe.log")).read():
            # finished inside the probe: the whole instance is one search leaf
            S["jobs"] = [{"t": "static", "cube": [], "dump": pdump, "extra": []}]
            S["dumps"][pdump] = 1
        else:
            assert rc == "TIMEOUT", f"probe: rc {rc}"
            edges = initial_edges(pdump, a.initial_depth)
            os.remove(pdump)
            S["initial_edges"] = edges
            S["jobs"] = [{"t": "search", "cube": [(e + 1) * s for e, s in zip(edges, signs)]}
                         for signs in itertools.product((1, -1), repeat=len(edges))]
        S["probe_done"] = True
        save()
        log(f"probe {dt:.0f}s -> {len(S['jobs'])} initial jobs (edges {S.get('initial_edges')})")
    # re-queue jobs that were running when the driver last stopped
    if S["running"]:
        log(f"resuming: re-queue {len(S['running'])} interrupted jobs")
        S["jobs"] = S["running"] + S["jobs"]
        S["running"] = []
        save()

    def do_search(job):
        cube = job["cube"]
        d = os.path.join(top, "s", cid(cube))
        os.makedirs(d, exist_ok=True)
        dump = os.path.join(d, "dump.jsonl")
        lg = os.path.join(d, "search.log")
        rc, dt = run([PY, "-u", "verifier/f034_a4_line_graph_sat.py", str(a.member), "--dump", dump,
                      "--cube", *map(str, cube)], lg, timeout=a.limit)
        out = open(lg).read()
        if rc == 0 and re.search(r"^RESULT \S+ UNSAT", out, re.M):
            return ("unsat", job, dump, dt)
        if rc == 0 and re.search(r"^RESULT \S+ SAT", out, re.M):
            return ("SAT", job, dump, dt)
        if rc == "TIMEOUT":
            return ("timeout", job, dump, dt)
        return ("error", job, lg, dt)

    def do_static(job):
        cube, dump, extra = job["cube"], job["dump"], job["extra"]
        d = os.path.join(top, "r", cid(cube))
        if os.path.exists(d):
            shutil.rmtree(d)
        lg = d + ".out"
        cmd = [PY, "-u", "verifier/lean_static_resolve.py", dump, "--out", d, "--no-counters"]
        if extra:
            cmd += ["--cube", *map(str, extra)]
        rc, dt = run(cmd, lg)
        sp = os.path.join(d, "summary.json")
        s = json.load(open(sp)) if os.path.exists(sp) else {"verdict": f"CRASH rc={rc}"}
        return ("static", job, s, dt)

    def worker(job):
        if STOP.is_set():
            return ("stopped", job, None, 0)
        return do_search(job) if job["t"] == "search" else do_static(job)

    def release(dump):
        S["dumps"][dump] -= 1
        if S["dumps"][dump] <= 0:
            del S["dumps"][dump]
            if os.path.exists(dump):
                os.remove(dump)

    def handle(res):
        kind, job, x, dt = res
        cube = job["cube"]
        if kind == "unsat":
            S["stats"]["searches"] += 1
            S["stats"]["search_s"] += dt
            S["dumps"][x] = S["dumps"].get(x, 0) + 1
            S["jobs"].append({"t": "static", "cube": cube, "dump": x, "extra": []})
            log(f"search {cid(cube)}: UNSAT {dt:.0f}s")
        elif kind == "timeout":
            S["stats"]["timeouts"] += 1
            S["stats"]["search_s"] += dt
            e = split_edge(x, cube)
            os.remove(x)
            assert e is not None and len(cube) < a.max_depth, f"cannot split {cube}"
            for s in (1, -1):
                S["jobs"].append({"t": "search", "cube": cube + [(e + 1) * s]})
            S["splits"].append({"cube": cube, "edge": e, "why": "timeout", "after_s": round(dt)})
            log(f"search {cid(cube)}: TIMEOUT {dt:.0f}s -> split on edge {e}")
        elif kind == "SAT":
            STOP.set()
            open(os.path.join(top, "ALERT"), "w").write(f"cube {cube} SAT — see {x}\n")
            log(f"!!! cube {cid(cube)} is SAT — STOPPING EVERYTHING (contradicts the original "
                f"UNSAT; needs a human). Dump {x}")
        elif kind == "error":
            STOP.set()
            log(f"!!! search {cid(cube)} crashed — see {x}; STOPPING")
        elif kind == "static":
            s = x
            S["stats"]["static_s"] += dt
            if s["verdict"] != "UNSAT":
                STOP.set()
                log(f"!!! static {cid(cube)}: {s['verdict']} (a counter-free static re-solve of a "
                    f"search-UNSAT cube should be UNSAT; see r/{cid(cube)}.out) — STOPPING")
                return
            r = s["rounds"][-1]
            d = os.path.join(top, "r", cid(cube))
            # bisect while too big AND still shrinking: below some size a cube's
            # certificate stops shrinking (lex/base overhead), so a pure size limit
            # would recurse to --max-depth (F-038 §10: member 14 at 10 MB)
            parent = job.get("parent_lrat")
            shrinking = parent is None or r["lrat_bytes"] < a.min_shrink * parent
            if r["lrat_bytes"] > a.leaf_max and not shrinking:
                log(f"static {cid(cube)}: {r['lrat_bytes'] / 1e9:.2f} GB > leaf-max but not "
                    f"< {a.min_shrink} x parent ({parent / 1e9:.2f} GB) -> accepted as a leaf")
            if r["lrat_bytes"] > a.leaf_max and shrinking and len(cube) < a.max_depth:
                e = split_edge(job["dump"], cube)
                if e is not None:
                    for sg in (1, -1):
                        S["jobs"].append({"t": "static", "cube": cube + [(e + 1) * sg],
                                          "dump": job["dump"], "extra": job["extra"] + [(e + 1) * sg],
                                          "parent_lrat": r["lrat_bytes"]})
                    S["dumps"][job["dump"]] += 2
                    S["splits"].append({"cube": cube, "edge": e, "why": "leaf-too-big",
                                        "lrat_bytes": r["lrat_bytes"]})
                    log(f"static {cid(cube)}: certificate {r['lrat_bytes'] / 1e9:.2f} GB > leaf-max "
                        f"-> bisect on edge {e} (same dump)")
                    shutil.rmtree(d)
                    release(job["dump"])
                    return
            w = os.path.join(top, "w", cid(cube) + ".txt")
            shutil.move(os.path.join(d, "witnesses.txt"), w)
            for fn in ("F.lrat", "F.cnf", "dump_core.jsonl"):
                if os.path.exists(os.path.join(d, fn)):
                    os.remove(os.path.join(d, fn))
            S["leaves"].append({"cube": cube, "w": w, "py_solve_s": r["solve_s"],
                                "py_lrat_bytes": r["lrat_bytes"], "core": s["final_core_dumped"],
                                "dumped": r["num_dumped"], "graph": os.path.join(d, "graph.json")})
            release(job["dump"])
            log(f"static {cid(cube)}: leaf ({s['final_core_dumped']} witnesses, "
                f"{r['lrat_bytes'] / 1e9:.2f} GB, solve {r['solve_s']:.0f}s)")

    # ---- the work queue --------------------------------------------------------------
    if "search_done" not in S:
        t0 = time.time()
        futs = {}
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            while (S["jobs"] or futs) and not STOP.is_set():
                while S["jobs"] and len(futs) < a.workers and not STOP.is_set():
                    if free_gb() < a.floor:
                        log(f"disk {free_gb():.1f} GB < floor {a.floor} GB: holding new jobs")
                        break
                    job = S["jobs"].pop(0)
                    S["running"].append(job)
                    futs[ex.submit(worker, job)] = job
                save()
                if not futs:
                    time.sleep(30)
                    continue
                done, _ = wait(futs, timeout=60, return_when=FIRST_COMPLETED)
                for f in done:
                    job = futs.pop(f)
                    with lock:
                        S["running"].remove(job)
                        handle(f.result())
                        save()
            if STOP.is_set():
                kill_all()
        if STOP.is_set():
            save()
            sys.exit("[cs] STOPPED — see the log and population/f034-a4-cert/cs-%s/" % key)
        S["search_done"] = True
        S["stats"]["queue_wall_s"] = round(time.time() - t0)
        save()
        log(f"all cubes refuted: {len(S['leaves'])} leaves, {S['stats']['searches']} searches, "
            f"{S['stats']['timeouts']} timeouts, {len(S['splits'])} splits; queue wall "
            f"{S['stats']['queue_wall_s']}s")

    # ---- Lean stage (as the split route, variable-length cubes) ----------------------
    leaves = sorted(S["leaves"], key=lambda x: x["cube"])
    L = len(leaves)
    cpath = os.path.join(top, "cubes.json")
    mod = f"Biplanar.Instances.{name}"
    if "export_done" not in S:
        for j, lf in enumerate(leaves, 1):
            shutil.copy(lf["w"], os.path.join(ddir, f"w{j}.txt"))
        json.dump([lf["cube"] for lf in leaves], open(cpath, "w"))
        mlog = S.get("replay_log") or os.path.join(top, "probe.log")
        mults = re.search(r"mults=\[([^\]]*)\]", open(mlog).read()).group(1)
        doc = (f"A4 member {i} of F-034: the line graph L(M) of the 7-vertex multigraph M with "
               f"multiplicities [{mults}] (n = 28); P-008 A(ii) rests on its non-biplanarity")
        graph = leaves[0]["graph"]
        for cmd, lg in (([PY, "verifier/lean_split_modules.py", "--key", key, "--name", name,
                          "--graph", graph, "--cubes", cpath, "--doc", doc, "--no-registry"], "modules.out"),
                        ([PY, "verifier/f038_lean_graph_check.py", "--file",
                          os.path.join(LEAN, "Biplanar", "Instances", name, "Base.lean")], "graph-check.txt")):
            rc, _ = run(cmd, os.path.join(top, lg))
            assert rc == 0, f"{lg}: rc {rc}"
        for j, lf in enumerate(leaves, 1):
            cnf = os.path.join(ddir, f"leaf{j}.cnf")
            for cmd, lg in (([PY, "verifier/lean_cnf_writer.py", "--graph", graph, "--witnesses",
                              os.path.join(ddir, f"w{j}.txt"), "--out", cnf, "--cube",
                              *map(str, lf["cube"])], f"export{j}.log"),
                            ([PY, "verifier/cnf_tautology_scan.py", cnf], f"taut{j}.out"),
                            ([PY, "verifier/lex_encoding_diff.py", "--key", key, "--cnf", cnf, "--skip",
                              str(len(lf["cube"])), "--graph", graph], f"lexdiff{j}.out")):
                rc, _ = run(cmd, os.path.join(top, lg))
                assert rc == 0, f"{lg}: rc {rc}"
        with open(os.path.join(ddir, "negcubes.cnf"), "w") as f:
            nv = max([abs(l) for lf in leaves for l in lf["cube"]] + [1])
            f.write(f"p cnf {nv} {L}\n")
            for lf in leaves:
                f.write(" ".join(str(-l) for l in lf["cube"]) + " 0\n")
        S["export_done"] = True
        save()
        log(f"Lean modules for {L} leaves generated; graph check OK; 0 tautologies; lex MATCH")

    def lean_solve(j):
        tag = "cover" if j == 0 else f"leaf{j}"
        cnf = os.path.join(ddir, "negcubes.cnf" if j == 0 else f"leaf{j}.cnf")
        lrat = os.path.join(ddir, f"{tag}.lrat")
        chk = os.path.join(top, f"{tag}.lratcheck")
        if os.path.exists(chk) and "c VERIFIED" in open(chk).read() and os.path.exists(lrat):
            return tag, None
        rc, dt = run(["cadical", "--lrat", "--no-binary", "--no-factor", cnf, lrat],
                     os.path.join(top, f"{tag}.cadical.log"))
        assert rc == 20, f"{tag}: cadical rc {rc}"
        rc2, dtc = run([LRATCHECK, cnf, lrat], chk)
        assert "c VERIFIED" in open(chk).read(), f"{tag}: lrat-check did NOT verify"
        return tag, {"cadical_s": round(dt, 1), "lratcheck_s": round(dtc, 1),
                     "lrat_bytes": os.path.getsize(lrat), "lrat_sha256": sha(lrat), "cnf_sha256": sha(cnf)}

    if "lean_solved" not in S:
        t0 = time.time()
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            for tag, st in ex.map(lean_solve, list(range(1, L + 1)) + [0]):
                if st:
                    S.setdefault("lean", {})[tag] = st
        S["lean_solve_wall_s"] = round(time.time() - t0)
        S["lean_solved"] = True
        save()
        log(f"Lean-side CaDiCaL + lrat-check VERIFIED for {L} leaves and the cover "
            f"({S['lean_solve_wall_s']}s wall)")

    def build(targets, logname):
        """One `lake build` call; lake builds the given targets concurrently (it has no
        -j flag in v4.30), so callers batch the leaves to bound memory."""
        t0 = time.time()
        p = subprocess.run(time_cmd(["lake", "build", *targets]), cwd=LEAN, env=ENV,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        out = p.stdout
        open(os.path.join(top, logname), "w").write(out)
        nerr = out.count("error")
        if p.returncode or nerr or "Build completed successfully" not in out:
            sys.exit(f"[cs] LEAN BUILD FAILED: {targets[:3]}… (rc {p.returncode}, {nerr} 'error') — "
                     f"any axiom line printed is NOT a result; see {logname}")
        return time.time() - t0, parse_rss(out), out

    if "built" not in S:
        t0 = time.time()
        if a.lean_jobs > 1:
            # batches of --lean-jobs leaves per lake call (each leaf import needs ~5-6 GB)
            done_b = S.setdefault("leaf_batches_done", 0)
            batches = [list(range(b, min(b + a.lean_jobs, L + 1))) for b in range(1, L + 1, a.lean_jobs)]
            for bi, batch in enumerate(batches):
                if bi < done_b:
                    continue
                dt, rss, _ = build([f"{mod}.Leaf{j}" for j in batch], f"build-leaves-{bi + 1}.log")
                S["leaf_batches_done"] = bi + 1
                S.setdefault("leaf_build", []).append({"leaves": batch, "wall_s": round(dt), "maxrss": rss})
                save()
                log(f"leaves {batch[0]}..{batch[-1]} built ({dt:.0f}s, max RSS {rss / 1e9:.1f} GB)")
        else:
            for j in range(1, L + 1):
                dt, rss, _ = build([f"{mod}.Leaf{j}"], f"build-leaf{j}.log")
                S["lean"][f"leaf{j}"].update(build_s=round(dt), build_maxrss=rss)
                for fn in (f"leaf{j}.lrat", f"leaf{j}.cnf"):
                    os.remove(os.path.join(ddir, fn))
                save()
        build([f"{mod}.Cover"], "build-cover.log")
        _, _, out = build([mod], "build-main.log")
        ax = re.search(r"depends on axioms: \[(.*?)\]", out.replace("\n", " "))
        axioms = [x.strip() for x in ax.group(1).split(",")] if ax else []
        assert axioms and not any("sorryAx" in x for x in axioms), f"axioms: {axioms}"
        S["axioms"] = axioms
        with open(os.path.join(ddir, "MANIFEST.txt"), "w") as f:
            f.write(f"# {time.ctime()}  per-cube search route, {L} leaves (cube_search_certify.py)\n")
            for j in range(1, L + 1):
                t = S["lean"][f"leaf{j}"]
                f.write(f"{sha(os.path.join(ddir, f'w{j}.txt'))}  data/{key}/w{j}.txt\n"
                        f"{t['cnf_sha256']}  data/{key}/leaf{j}.cnf (deleted)\n"
                        f"{t['lrat_sha256']}  data/{key}/leaf{j}.lrat (deleted)\n")
            f.write(f"{S['lean']['cover']['lrat_sha256']}  data/{key}/cover.lrat\n")
        for j in range(1, L + 1):
            for fn in (f"leaf{j}.lrat", f"leaf{j}.cnf"):
                if os.path.exists(os.path.join(ddir, fn)):
                    os.remove(os.path.join(ddir, fn))
        lib = os.path.join(LEAN, ".lake", "build", "lib", "lean", "Biplanar", "Instances", name)
        for fn in os.listdir(lib):
            if re.match(r"Leaf\d+\.(olean|ilean|trace)", fn):
                os.remove(os.path.join(lib, fn))
        S["built"] = True
        S["build_wall_s"] = round(time.time() - t0)
        S["free_gb_end"] = round(free_gb(), 1)
        save()
    nd = sum(1 for x in S["axioms"] if "native_decide" in x)
    log(f"CERTIFIED: Biplanar.{name}.not_biplanar via {L} leaves (axioms: standard + {nd} native_decide)")


if __name__ == "__main__":
    main()
