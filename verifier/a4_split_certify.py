#!/usr/bin/env python3
"""F-038 §8: the SPLIT route for the heavy A4 members.

The monolithic chain (f034_a4_certify.sh) does one static solve of the whole
dump and imports one certificate into one Lean module. For the six heaviest
members that is infeasible on this machine (F-038 §7.3): Lean imports cost
~12x their certificate in memory, and the static solve grows as C^2.3. The
split route cuts the problem into 2^k cubes on k edge variables and treats
every cube as its own instance, end to end:

  0. dump     replay `f034_a4_line_graph_sat.py <i> --dump` (untrusted clause
              generator; final stats must equal the original run's)
  1. cubes    k edge variables (most frequent in the dumped clauses, pairwise
              vertex-disjoint in L(M), edge 0 excluded — it is fixed by the
              part-swap unit), all 2^k sign patterns
  2. solve    per cube: lean_static_resolve.py --no-counters --cube …
              (CaDiCaL LRAT, lrat-check, the cube's own LRAT core = its
              witness set); certificates deleted after each cube
  3. lean     lean_split_modules.py (Base, Cubes, W<j>, Leaf<j>, Cover, main;
              one registry entry per leaf); graph check G ≅ L(M); per leaf:
              `biplanar-export` of cube j ++ F_j, tautology scan, lex check;
              CaDiCaL LRAT + lrat-check (unlocked, in parallel); negated-cubes
              formula + LRAT; `lake build` of each leaf, the cover and the main
              module one at a time (under the shared Lean lock), each leaf's LRAT
              and CNF deleted after its build. The leaf .oleans (which embed the
              certificates) must coexist until the main module is built, then go.

Soundness is unchanged: every leaf theorem comes from
`not_biplanar_on_cube_of_unsat_sym₀` and the composition from
`not_biplanar_of_cover` (LEAN-2's Sym.lean), under (H2) and (H3).

Usage:
  .venv/bin/python -u verifier/a4_split_certify.py 17 --k 3 [--workers 2] \
      [--edges 12 40 77] [--key a4_m17s --name A4M17S]
Resumable: finished stages are skipped (their outputs are on disk).
"""
import argparse
import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
PY = os.path.join(ROOT, ".venv", "bin", "python")
LEAN = os.path.join(ROOT, "lean")
LRATCHECK = os.path.join(ROOT, "tools", "drat-trim", "lrat-check")
CERT = os.path.join(ROOT, "population", "f034-a4-cert")
LOCK = os.path.join(CERT, "lean.lock")
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
FLOOR_GB = 10


def log(*a):
    print(f"[split] {time.strftime('%F %T')}", *a, flush=True)


def free_gb():
    st = os.statvfs(ROOT)
    return st.f_bavail * st.f_frsize / 2 ** 30


def need(gb, what):
    f = free_gb()
    if f - gb < FLOOR_GB:
        log(f"DISK STOP before {what}: {f:.1f} GB free, step may write ~{gb:.1f} GB")
        sys.exit(3)


def run(cmd, logfile=None, cwd=ROOT, check=True):
    t0 = time.time()
    with open(logfile, "w") if logfile else open(os.devnull, "w") as f:
        p = subprocess.run(cmd, cwd=cwd, env=ENV, stdout=f, stderr=subprocess.STDOUT)
    if check and p.returncode != 0:
        tail = open(logfile).read()[-2000:] if logfile else ""
        sys.exit(f"[split] FAILED ({p.returncode}): {' '.join(map(str, cmd))}\n{tail}")
    return p.returncode, time.time() - t0


class Lock:
    def __enter__(self):
        while True:
            try:
                os.mkdir(LOCK)
                return self
            except FileExistsError:
                time.sleep(20)

    def __exit__(self, *exc):
        os.rmdir(LOCK)


def lrat_verified(cnf, lrat, out):
    t0 = time.time()
    p = subprocess.run([LRATCHECK, cnf, lrat], capture_output=True, text=True)
    open(out, "w").write(p.stdout + p.stderr)
    return p.returncode == 0 and "c VERIFIED" in p.stdout + p.stderr, time.time() - t0


def sha(path):
    return subprocess.check_output(["shasum", "-a", "256", path], text=True).split()[0]


def choose_edges(dump, k):
    """k edge variables for the split: most frequent in the dumped clauses,
    pairwise vertex-disjoint in L(M), edge 0 excluded."""
    cnt = Counter()
    edges = None
    with open(dump) as f:
        for line in f:
            obj = json.loads(line)
            if obj.get("type") == "header":
                edges = [tuple(e) for e in obj["edges"]]
            elif "e" in obj:
                cnt.update(obj["e"])
    chosen, used = [], set()
    for e, _ in cnt.most_common():
        if e == 0 or used & set(edges[e]):
            continue
        chosen.append(e)
        used |= set(edges[e])
        if len(chosen) == k:
            break
    return chosen, {e: cnt[e] for e in chosen}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("member", type=int)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--edges", nargs="*", type=int, help="override the split edges (0-based)")
    ap.add_argument("--key")
    ap.add_argument("--name")
    ap.add_argument("--lean-export", action="store_true",
                    help="export the leaves with `lake exe biplanar-export` (registry "
                         "entries per leaf) instead of lean_cnf_writer.py")
    a = ap.parse_args()
    i = f"{a.member:02d}"
    key = a.key or f"a4_m{i}s"
    name = a.name or f"A4M{i}S"
    top = os.path.join(CERT, f"split-m{i}")
    os.makedirs(top, exist_ok=True)
    os.makedirs(os.path.join(LEAN, "data", key), exist_ok=True)
    mpath = os.path.join(top, "split_metrics.json")
    M = json.load(open(mpath)) if os.path.exists(mpath) else {"member": i, "key": key, "name": name}

    def save():
        json.dump(M, open(mpath, "w"), indent=1)

    dump = os.path.join(top, "dump.jsonl")
    replay = os.path.join(top, "replay.log")
    log(f"member {i} -> {name} ({key}); {free_gb():.1f} GB free")

    # ---- 0. dump -------------------------------------------------------------
    if "replay_stats" not in M:
        if not (os.path.exists(replay) and "RESULT" in open(replay).read()):
            need(2, "replay")
            _, dt = run([PY, "-u", "verifier/f034_a4_line_graph_sat.py", str(a.member),
                         "--dump", dump], replay)
            M["replay_wall_s"] = round(dt)
        r = open(replay).read()
        assert re.search(r"^RESULT \S+ UNSAT", r, re.M), "replay did not end UNSAT"
        orig = open(os.path.join(ROOT, "population", "f034-a4", f"member-{i}.log")).read()
        s_orig = orig.split("stats: ")[-1].splitlines()[0]
        s_new = r.split("stats: ")[-1].splitlines()[0]
        assert s_orig == s_new, f"REPLAY DIVERGED: {s_orig} / {s_new}"
        M["replay_stats"] = s_new
        M["replay_solve_s"] = float(re.search(r"^RESULT \S+ UNSAT ([\d.]+)s", r, re.M).group(1))
        M["dump_bytes"] = os.path.getsize(dump)
        M["dump_sha256"] = sha(dump)
        save()
        log(f"replay UNSAT, identical stats {s_new}")

    # ---- 1. cubes ------------------------------------------------------------
    cpath = os.path.join(top, "cubes.json")
    if not os.path.exists(cpath):
        if a.edges:
            chosen, freq = a.edges, {}
        else:
            chosen, freq = choose_edges(dump, a.k)
        cubes = [[(e + 1) * s for e, s in zip(chosen, signs)]
                 for signs in itertools.product((1, -1), repeat=len(chosen))]
        json.dump(cubes, open(cpath, "w"))
        M["split_edges"] = chosen
        M["split_edge_freq"] = freq
        save()
    cubes = json.load(open(cpath))
    L = len(cubes)
    log(f"{L} cubes on edges {M.get('split_edges')}: {cubes}")

    # ---- 2. per-cube static solve + core ------------------------------------
    def solve_cube(j):
        d = os.path.join(top, f"c{j}")
        w = os.path.join(LEAN, "data", key, f"w{j}.txt")
        sp = os.path.join(d, "summary.json")
        if os.path.exists(sp) and json.load(open(sp))["verdict"] == "UNSAT" and os.path.exists(w):
            return j
        need(1.5 * M.get("dump_bytes", 0) / 2 ** 30 + 1, f"cube {j} solve")
        _, dt = run([PY, "-u", "verifier/lean_static_resolve.py", dump, "--out", d,
                     "--no-counters", "--cube", *map(str, cubes[j - 1])],
                    os.path.join(d + ".out"), check=False)
        s = json.load(open(sp)) if os.path.exists(sp) else {"verdict": "CRASH"}
        if s["verdict"] != "UNSAT":
            sys.exit(f"[split] cube {j} {cubes[j - 1]}: {s['verdict']} — see {d}.out "
                     f"(SAT without counters would need the counter route)")
        assert "c VERIFIED" in open(os.path.join(d, "resolve.log")).read()
        shutil.copy(os.path.join(d, "witnesses.txt"), w)
        for fn in ("F.lrat", "F.cnf", "dump_core.jsonl", "witnesses.txt"):
            if os.path.exists(os.path.join(d, fn)):
                os.remove(os.path.join(d, fn))
        r = s["rounds"][-1]
        log(f"cube {j}/{L} {cubes[j - 1]}: UNSAT solve {r['solve_s']}s check {r['check_s']}s "
            f"LRAT {r['lrat_bytes'] / 1e9:.2f} GB core {s['final_core_dumped']} "
            f"py-mem {s['python_maxrss_bytes'] / 1e6:.0f} MB wall {dt:.0f}s")
        return j

    if "cubes_done" not in M:
        t0 = time.time()
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            list(ex.map(solve_cube, range(1, L + 1)))
        M["py_stage_wall_s"] = round(time.time() - t0)
        M["cubes"] = {}
        for j in range(1, L + 1):
            s = json.load(open(os.path.join(top, f"c{j}", "summary.json")))
            r = s["rounds"][-1]
            M["cubes"][j] = {"cube": cubes[j - 1], "py_solve_s": r["solve_s"],
                             "py_check_s": r["check_s"], "py_lrat_bytes": r["lrat_bytes"],
                             "core": s["final_core_dumped"], "dumped": r["num_dumped"],
                             "py_maxrss": s["python_maxrss_bytes"]}
        M["cubes_done"] = True
        save()
    if os.path.exists(dump):
        os.remove(dump)
        log("deleted the dump (sha256 in split_metrics.json)")

    # ---- 3. Lean ---------------------------------------------------------------
    mults = re.search(r"mults=\[([^\]]*)\]", open(replay).read()).group(1)
    doc = (f"A4 member {i} of F-034: the line graph L(M) of the 7-vertex multigraph M "
           f"with multiplicities [{mults}] (n = 28); P-008 A(ii) rests on its non-biplanarity")
    ddir = os.path.join(LEAN, "data", key)
    mod = f"Biplanar.Instances.{name}"
    if "export_done" not in M:
        with Lock():
            run([PY, "verifier/lean_split_modules.py", "--key", key, "--name", name,
                 "--graph", os.path.join(top, "c1", "graph.json"), "--cubes", cpath,
                 "--doc", doc] + ([] if a.lean_export else ["--no-registry"]),
                os.path.join(top, "modules.out"))
            run([PY, "verifier/f038_lean_graph_check.py", "--file",
                 os.path.join(LEAN, "Biplanar", "Instances", name, "Base.lean")],
                os.path.join(top, "graph-check.txt"))
            if a.lean_export:
                need(3, "exporter build")
                _, dt = run(["lake", "build", "Biplanar.Instances", "biplanar-export"],
                            os.path.join(top, "lake-export.log"), cwd=LEAN)
                M["exporter_build_s"] = round(dt)
                for j in range(1, L + 1):
                    run(["lake", "exe", "biplanar-export", f"{key}_{j}", f"data/{key}/leaf{j}.cnf",
                         *map(str, cubes[j - 1])], os.path.join(top, f"export{j}.log"), cwd=LEAN)
        if not a.lean_export:
            # the Lean exporter initialises EVERY registered instance per call
            # (~60 s, ~5 GB); lean_cnf_writer.py prints the same bytes (selftest:
            # 20/20 identical). Lean re-checks each certificate against its own
            # term, so the writer is not trusted.
            t0 = time.time()
            for j in range(1, L + 1):
                run([PY, "verifier/lean_cnf_writer.py", "--graph", os.path.join(top, "c1", "graph.json"),
                     "--witnesses", os.path.join(ddir, f"w{j}.txt"), "--out",
                     os.path.join(ddir, f"leaf{j}.cnf"), "--cube", *map(str, cubes[j - 1])],
                    os.path.join(top, f"export{j}.log"))
            M["writer_s"] = round(time.time() - t0)
        M["exported_by"] = "lean" if a.lean_export else "writer"
        for j in range(1, L + 1):
            cnf = os.path.join(ddir, f"leaf{j}.cnf")
            run([PY, "verifier/cnf_tautology_scan.py", cnf], os.path.join(top, f"taut{j}.out"))
            run([PY, "verifier/lex_encoding_diff.py", "--key", key, "--cnf", cnf, "--skip",
                 str(len(cubes[j - 1])), "--graph", os.path.join(top, "c1", "graph.json")],
                os.path.join(top, f"lexdiff{j}.out"))
        # the negated-cubes formula: one clause per cube, literals negated, in
        # order (LRATCatcher.negCubesCNF / Cube.negClause)
        with open(os.path.join(ddir, "negcubes.cnf"), "w") as f:
            nv = max(abs(l) for c in cubes for l in c)
            f.write(f"p cnf {nv} {L}\n")
            for c in cubes:
                f.write(" ".join(str(-l) for l in c) + " 0\n")
        M["export_done"] = True
        save()
        log("modules generated, graph check OK, leaves exported (0 tautologies, lex MATCH)")

    def lean_solve(j):
        tag = "cover" if j == 0 else f"leaf{j}"
        cnf = os.path.join(ddir, "negcubes.cnf" if j == 0 else f"leaf{j}.cnf")
        lrat = os.path.join(ddir, f"{tag}.lrat")
        ok_file = os.path.join(top, f"{tag}.lratcheck")
        if os.path.exists(ok_file) and "c VERIFIED" in open(ok_file).read() and os.path.exists(lrat):
            return
        if j:
            need(2 * M["cubes"][str(j) if str(j) in M["cubes"] else j]["py_lrat_bytes"] / 2 ** 30 + 1,
                 f"{tag} solve")
        rc, dt = run(["cadical", "--lrat", "--no-binary", "--no-factor", cnf, lrat],
                     os.path.join(top, f"{tag}.cadical.log"), check=False)
        assert rc == 20, f"{tag}: cadical rc {rc}"
        ok, dtc = lrat_verified(cnf, lrat, ok_file)
        assert ok, f"{tag}: lrat-check did NOT verify"
        M.setdefault("lean", {})[tag] = {"exported_by": M.get("exported_by", "lean"),
                                         "cadical_s": round(dt, 1), "lratcheck_s": round(dtc, 1),
                                         "lrat_bytes": os.path.getsize(lrat),
                                         "lrat_sha256": sha(lrat), "cnf_sha256": sha(cnf)}
        log(f"{tag}: Lean-side CaDiCaL {dt:.0f}s, {os.path.getsize(lrat) / 1e9:.2f} GB, "
            f"lrat-check VERIFIED {dtc:.0f}s")

    if "lean_solved" not in M:
        t0 = time.time()
        with ThreadPoolExecutor(max_workers=a.workers) as ex:
            list(ex.map(lean_solve, list(range(1, L + 1)) + [0]))
        M["lean_solve_wall_s"] = round(time.time() - t0)
        M["lean_solved"] = True
        save()

    def build(target, logname):
        t0 = time.time()
        p = subprocess.run(["/usr/bin/time", "-l", "lake", "build", target], cwd=LEAN, env=ENV,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        out = p.stdout
        open(os.path.join(top, logname), "w").write(out)
        nerr = out.count("error")
        if p.returncode or nerr or "Build completed successfully" not in out:
            sys.exit(f"[split] LEAN BUILD FAILED: {target} (rc {p.returncode}, {nerr} 'error' "
                     f"lines) — any axiom line printed is NOT a result; see {logname}")
        rss = int(re.search(r"(\d+)\s+maximum resident set size", out).group(1))
        return time.time() - t0, rss, out

    if "built" not in M:
        with Lock():
            for j in range(1, L + 1):
                tag = f"leaf{j}"
                if M.get("lean", {}).get(tag, {}).get("build_s"):
                    continue
                need(M["lean"][tag]["lrat_bytes"] / 2 ** 30 + 1, f"{tag} build")
                dt, rss, _ = build(f"{mod}.Leaf{j}", f"build-{tag}.log")
                M["lean"][tag].update(build_s=round(dt), build_maxrss=rss)
                for fn in (f"{tag}.lrat", f"{tag}.cnf"):
                    os.remove(os.path.join(ddir, fn))
                save()
                log(f"{tag}: lake build OK {dt:.0f}s (max RSS {rss / 1e9:.1f} GB); "
                    f"its LRAT and CNF deleted, .olean kept until the main build")
            dt, rss, _ = build(f"{mod}.Cover", "build-cover.log")
            dt2, rss2, out = build(mod, "build-main.log")
            ax = re.search(r"depends on axioms: \[(.*?)\]", out.replace("\n", " "))
            axioms = [x.strip() for x in ax.group(1).split(",")] if ax else []
            assert axioms and not any("sorryAx" in x for x in axioms), f"axioms: {axioms}"
            M["main_build_s"] = round(dt + dt2)
            M["axioms"] = axioms
            with open(os.path.join(ddir, "MANIFEST.txt"), "w") as f:
                f.write(f"# {time.ctime()}  split route, {L} cubes on edges {M.get('split_edges')}"
                        f"  (a4_split_certify.py)\n")
                for j in range(1, L + 1):
                    t = M["lean"][f"leaf{j}"]
                    f.write(f"{sha(os.path.join(ddir, f'w{j}.txt'))}  data/{key}/w{j}.txt\n"
                            f"{t['cnf_sha256']}  data/{key}/leaf{j}.cnf (deleted)\n"
                            f"{t['lrat_sha256']}  data/{key}/leaf{j}.lrat (deleted)\n")
                f.write(f"{M['lean']['cover']['lrat_sha256']}  data/{key}/cover.lrat\n")
            # the leaf .oleans embed their certificates: drop them now that the
            # main module is built (a rebuild regenerates them from the LRATs)
            lib = os.path.join(LEAN, ".lake", "build", "lib", "lean", "Biplanar", "Instances", name)
            for fn in os.listdir(lib):
                if re.match(r"Leaf\d+\.(olean|ilean|trace)", fn):
                    os.remove(os.path.join(lib, fn))
            M["built"] = True
            M["free_gb_end"] = round(free_gb(), 1)
            save()
    nd = sum(1 for x in M["axioms"] if "native_decide" in x)
    log(f"CERTIFIED: {mod.replace('Instances.', '')}.not_biplanar via {L} cubes "
        f"(axioms: standard + {nd} native_decide)")


if __name__ == "__main__":
    main()
