"""Corpus oracle runner: per-declaration verdicts of Lean's checker and of nitrolean.

usage: python3 -I bench/oracle/run.py [--tier N] [--only ID,...] [--out DIR]
           [--nitrolean BIN] [--timeout S] [--mem-mib MIB] [--max-rounds N] [--results FILE]

For each project built by build.sh (OUT/<id>/export.ndjson and build.env):

1. Lean: `leanchecker --from-export` of the project's toolchain (v4.36.0 for toolchains
   before v4.35.0, whose leanchecker has no --from-export).
2. nitrolean on the export, with --threads 1 and with all cores.
3. nitrolean on the project's .olean files (`check --olean DIR --module ROOT`), with
   --threads 1 and with all cores, when they are .olean files of Lean v4.36.0, the only
   version nitrolean's .olean reader supports.

Both checkers stop at the first declaration they reject. To get a verdict per declaration,
a run that rejects declaration D is repeated on the export without D: a rejected theorem is
replaced by an axiom of the same type (so the declarations that use it are still checked),
any other rejected record is dropped together with every record that depends on it (those
are `skipped`). This is repeated until the checker accepts what is left (at most
--max-rounds runs). The verdicts are compared constant by constant: accept, or reject with
an error kind (tools/kinds in this file). The .olean runs cannot be filtered, so they give
one verdict: they must accept exactly when the export runs found nothing to reject, and
otherwise reject one of the declarations those runs rejected.

Writes OUT/<id>/result.json and OUT/<id>/verdicts.tsv (one row per constant: Lean's and
nitrolean's verdicts), and the summary table to --results (default bench/oracle/RESULTS.md).
Prints every mismatch; a constant nitrolean accepts and Lean rejects is reported as a
SOUNDNESS mismatch. Exit status 0 if every project agrees and the variants are identical,
1 if not.
"""
import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "tools"))
import export as ex  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
RUN_LIMITED = os.path.join(ROOT, "bench", "kernel-compute", "tools", "run_limited.py")

# Error kinds, from the message of either checker (first match wins).
KINDS = [
    ("declined", r"^declined|resource limit|not implemented|too large|unsupported"),
    ("malformed", r"malformed|parse error|undefined .*id|duplicate id|unknown record|line \d+:"),
    ("already-declared", r"already declared|declared twice|duplicate (declaration|constant)"),
    # Lean's replay skips partial and unsafe constants, so it reports a use of one as an
    # unknown constant.
    ("unknown-constant", r"unknown (constant|declaration)|must not contain (partial|unsafe)"
                         r"|uses unsafe declaration|environment does not have"),
    # A constructor or recursor record that differs from what the kernel derives (Lean:
    # "Invalid recursor", found after the replay), whatever field differs.
    ("inductive", r"does not match the declaration derived|^invalid (constructor|recursor)"),
    ("declaration-type-mismatch", r"declaration type mismatch"),
    ("application-type-mismatch", r"application type mismatch"),
    ("function-expected", r"function expected"),
    ("type-expected", r"type expected"),
    ("projection", r"projection"),
    ("theorem-not-prop", r"theorem type is not prop|not a proposition"),
    ("universe", r"universe|level param"),
    ("inductive", r"inductive|constructor|recursor|positiv|nested|quotient"),
    ("loose-variables", r"free variable|metavariable|loose bound"),
    ("deep-recursion", r"deep recursion|recursion depth|stack overflow"),
    ("timeout", r"deterministic timeout|heartbeat"),
]


def kind_of(msg):
    m = msg.lower()
    for k, rx in KINDS:
        if re.search(rx, m):
            return k
    return "other"


def parse_lean(log_text):
    """(accepted, decl or None, message) from leanchecker's output."""
    if "Lean default kernel accepts the solution" in log_text and "rejects" not in log_text:
        return True, None, ""
    m = re.search(r"while replaying declaration '(.+?)':\n(.*)", log_text, re.S)
    if m:
        return False, m.group(1), m.group(2).strip()
    m = re.search(r"(Invalid|No such) (constructor|recursor) (\S+)", log_text)
    if m:
        return False, m.group(3), m.group(0)
    m = re.search(r"(Quotient constant mismatch on|quotient constant in final kernel env): (\S+)",
                  log_text)
    if m:
        return False, m.group(2), "quotient " + m.group(0)
    return False, None, log_text.strip()[-500:]


def parse_nitrolean(log_text):
    if re.search(r"^accepted", log_text, re.M):
        return True, None, ""
    m = re.search(r"^nitrolean: (rejected|declined): declaration '(.+?)': (.*)", log_text, re.M | re.S)
    if m:
        msg = m.group(3).strip()
        return False, m.group(2), ("declined: " + msg) if m.group(1) == "declined" else msg
    m = re.search(r"^nitrolean: (.*)", log_text, re.M | re.S)
    return False, None, (m.group(1) if m else log_text).strip()[-500:]


def run_limited(cmd, log, timeout, mem_mib):
    """Runs cmd with an unlimited stack under run_limited.py; returns its status line."""
    wrapped = ["bash", "-c", 'ulimit -s unlimited; exec "$@"', "bash"] + cmd
    p = subprocess.run([sys.executable, "-I", RUN_LIMITED, str(timeout), str(mem_mib), log, "--"]
                       + wrapped, capture_output=True, text=True, check=True)
    status, code, wall, peak = p.stdout.strip().split("\t")
    return {"status": status, "exit": code, "wall_s": float(wall), "peak_mib": int(peak)}


def read_log(path):
    with open(path, errors="replace") as f:
        return f.read()


def per_decl(label, cmd_of, parse, export, index, work, args):
    """The per-declaration loop for one checker on one export."""
    os.makedirs(work, exist_ok=True)
    cur = export
    rejected = {}      # normalized constant name -> (kind, message)
    axioms = set()
    drop = set()
    dropped = set()
    runs = []
    status = "complete"
    for rnd in range(args.max_rounds):
        log = os.path.join(work, f"{label}.{rnd}.log")
        st = run_limited(cmd_of(cur), log, args.timeout, args.mem_mib)
        runs.append(st)
        if st["status"] != "exited":
            status = st["status"]
            break
        ok, decl, msg = parse(read_log(log))
        if ok and st["exit"] == "0":
            break
        if ok:
            status = f"error: exit {st['exit']}"
            break
        d = ex.norm_name(decl) if decl else None
        rec = index.by_name.get(d) if d else None
        if rec is None:
            status = f"rejected without a declaration of the export: {msg[:300]}"
            break
        block = [ex.norm_name(n) for n in rec[2]]
        if d in drop:
            status = f"rejected '{d}' again after dropping it"
            break
        st["decl"], st["kind"] = d, kind_of(msg)
        for n in block:
            rejected.setdefault(n, (kind_of(msg), msg.splitlines()[0][:300] if msg else ""))
        if rec[1] == "thm" and d not in axioms:
            axioms.add(d)
        else:
            axioms.discard(d)
            drop.update(block)
        nxt = os.path.join(work, f"{label}.{rnd + 1}.ndjson")
        dropped = ex.rewrite(export, nxt, drop_names=drop, axiomatize=axioms)
        if cur != export:
            os.remove(cur)
        cur = nxt
    else:
        status = f"stopped after {args.max_rounds} rounds"
    if cur != export and os.path.exists(cur):
        os.remove(cur)
    verdicts = {}
    for n in index.constants():
        n = ex.norm_name(n)
        if n in rejected:
            verdicts[n] = "reject:" + rejected[n][0]
        elif n in dropped:
            verdicts[n] = "skipped"
        elif status != "complete":
            verdicts[n] = "unknown"
        else:
            verdicts[n] = "accept"
    return {"label": label, "status": status, "runs": runs,
            "rejected": {n: list(v) for n, v in rejected.items()}, "verdicts": verdicts}


def single(label, cmd, parse, work, args):
    log = os.path.join(work, f"{label}.log")
    st = run_limited(cmd, log, args.timeout, args.mem_mib)
    out = {"label": label, "runs": [st]}
    if st["status"] != "exited":
        out["status"] = st["status"]
        return out
    ok, decl, msg = parse(read_log(log))
    if ok and st["exit"] == "0":
        out["status"] = "accept"
    elif st["exit"] in ("1", "2"):
        out["status"] = "reject"
        out["decl"] = ex.norm_name(decl) if decl else None
        out["kind"] = kind_of(msg)
        out["message"] = msg.splitlines()[0][:300] if msg else ""
    else:
        out["status"] = f"error: exit {st['exit']}"
        out["message"] = msg[:300]
    return out


def compare(lean, nitro):
    c = {"agree": 0, "kind_differs": [], "nitro_only_reject": [], "nitro_only_accept": [],
         "not_compared": 0}
    for n, lv in lean.items():
        nv = nitro.get(n, "unknown")
        if lv in ("skipped", "unknown") or nv in ("skipped", "unknown"):
            if lv == nv == "skipped":
                c["agree"] += 1
            else:
                c["not_compared"] += 1
        elif lv == nv:
            c["agree"] += 1
        elif lv == "accept":
            c["nitro_only_reject"].append((n, nv))
        elif nv == "accept":
            c["nitro_only_accept"].append((n, lv))
        else:
            c["agree"] += 1
            c["kind_differs"].append((n, lv, nv))
    return c


def env_file(path):
    out = {}
    with open(path) as f:
        for line in f:
            if "=" in line:
                k, v = line.rstrip("\n").split("=", 1)
                out[k] = v
    return out


def toolchain_bin(tc):
    subprocess.run(["elan", "toolchain", "install", tc], capture_output=True)
    prefix = subprocess.run(["elan", "run", tc, "lean", "--print-prefix"], capture_output=True,
                            text=True, check=True).stdout.strip()
    return os.path.join(prefix, "bin")


def check_toolchain(tc):
    m = re.match(r"leanprover/lean4:v4\.(\d+)\.", tc)
    return "leanprover/lean4:v4.36.0" if m and int(m.group(1)) < 35 else tc


def run_project(pid, args):
    out = os.path.join(args.out, pid)
    export = os.path.join(out, "export.ndjson")
    if not os.path.exists(export):
        print(f"{pid}: not built (run build.sh)", file=sys.stderr)
        return None
    b = env_file(os.path.join(out, "build.env"))
    work = os.path.join(out, "work")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    print(f"{pid}: indexing the export", file=sys.stderr)
    index = ex.Index(export)
    lean_tc = check_toolchain(b["toolchain"])
    leanchecker = os.path.join(toolchain_bin(lean_tc), "leanchecker")
    nitro = os.path.abspath(args.nitrolean)
    ncpu = os.cpu_count() or 1
    res = {"id": pid, "toolchain": b["toolchain"], "check_toolchain": lean_tc,
           "commit": b.get("commit"), "constants": len(index.constants()),
           "records": len(index.decls), "export_bytes": os.path.getsize(export),
           "threads_all": ncpu, "date": datetime.date.today().isoformat()}
    print(f"{pid}: leanchecker ({lean_tc})", file=sys.stderr)
    lean = per_decl("lean", lambda f: [leanchecker, "--from-export", f], parse_lean, export,
                    index, work, args)
    res["lean"] = {k: v for k, v in lean.items() if k != "verdicts"}
    variants = {}
    for threads, name in ((1, "export-1"), (0, "export-all")):
        print(f"{pid}: nitrolean, export, threads {threads or ncpu}", file=sys.stderr)
        v = per_decl(f"nitrolean-{name}",
                     lambda f, t=threads: [nitro, "check", "--threads", str(t), f],
                     parse_nitrolean, export, index, work, args)
        variants[name] = v
    main = variants["export-all"]
    res["nitrolean"] = {k: v for k, v in main.items() if k != "verdicts"}
    res["compare"] = compare(lean["verdicts"], main["verdicts"])
    res["variants"] = {}
    res["variants"]["export-1"] = {k: v for k, v in variants["export-1"].items()
                                   if k != "verdicts"}
    res["variants"]["export-1"]["identical"] = (variants["export-1"]["verdicts"]
                                                == main["verdicts"])
    nitro_rejected = {n for n, v in main["verdicts"].items() if v.startswith("reject:")}
    if b["toolchain"] == "leanprover/lean4:v4.36.0":
        env = dict(os.environ)
        env["PATH"] = toolchain_bin(b["toolchain"]) + os.pathsep + env["PATH"]
        mods = sum((["--module", r] for r in b["roots"].split(",")), [])
        for threads, name in ((1, "olean-1"), (0, "olean-all")):
            print(f"{pid}: nitrolean, .olean, threads {threads or ncpu}", file=sys.stderr)
            old = os.environ.get("PATH")
            os.environ["PATH"] = env["PATH"]
            try:
                o = single(f"nitrolean-{name}",
                           [nitro, "check", "--olean", "--threads", str(threads)] + mods
                           + [b["project_dir"]], parse_nitrolean, work, args)
            finally:
                os.environ["PATH"] = old
            if o["status"] == "accept":
                o["identical"] = not nitro_rejected and main["status"] == "complete"
            elif o["status"] == "reject":
                o["identical"] = o.get("decl") in nitro_rejected and (
                    main["verdicts"][o["decl"]] == "reject:" + o["kind"])
            else:
                o["identical"] = False
            res["variants"][name] = o
    else:
        res["variants"]["olean"] = {"status": "n/a", "identical": None,
                                    "message": f".olean files of {b['toolchain']}; the reader "
                                               "supports Lean v4.36.0 only"}
    with open(os.path.join(out, "verdicts.tsv"), "w") as f:
        f.write("constant\tlean\tnitrolean\n")
        for n, lv in lean["verdicts"].items():
            f.write(f"{n}\t{lv}\t{main['verdicts'].get(n, 'unknown')}\n")
    with open(os.path.join(out, "result.json"), "w") as f:
        json.dump(res, f, indent=1)
    if not args.keep_logs:
        shutil.rmtree(work, ignore_errors=True)
    return res


def num(n):
    """1234567 as `1 234 567`, as in bench/kernel-compute/README.md."""
    return format(n, ",").replace(",", " ")


def fmt_run(r):
    """A cell like those of bench/kernel-compute/README.md: `1.2 s, 345` (MiB)."""
    st = r["runs"][0]
    if st["status"] != "exited":
        return f"{st['status']} after {st['wall_s']:.0f} s"
    t = st["wall_s"]
    ts = f"{t:.2f} s" if t < 10 else f"{t:.1f} s" if t < 100 else f"{t:.0f} s"
    return f"{ts}, {num(st['peak_mib'])}"


def variant_cell(v):
    if v.get("status") == "n/a":
        return "n/a"
    s = fmt_run(v) if v.get("runs") else v.get("status", "")
    verdict = {"complete": "", "accept": "accepts"}.get(v.get("status"), v.get("status", ""))
    if v.get("status") == "reject":
        verdict = f"rejects {v.get('decl')}"
    if "rejected" in v and v["rejected"]:
        verdict = f"{len(v['rejected'])} rejected"
    return f"{s}{'; ' + verdict if verdict else ''}"


def write_results(results, path, nitro_version):
    rows = []
    for r in results:
        c = r["compare"]
        notes = []
        if c["kind_differs"]:
            notes.append(f"{len(c['kind_differs'])} with another error kind")
        if c["not_compared"]:
            notes.append(f"{c['not_compared']} not compared (skipped or unknown)")
        for side in ("lean", "nitrolean"):
            if r[side]["status"] != "complete":
                notes.append(f"{side}: {r[side]['status'][:80]}")
        rows.append(f"| {r['id']} | {r['toolchain'].split(':')[-1]} | {num(r['constants'])} | "
                    f"{num(c['agree'])} | {len(c['nitro_only_reject'])} | "
                    f"{len(c['nitro_only_accept'])} | {fmt_run(r['nitrolean'])} | "
                    f"{fmt_run(r['lean'])} | {'; '.join(notes)} |")
    vrows = []
    for r in results:
        v = r["variants"]
        cells = [variant_cell(r["nitrolean"]), variant_cell(v["export-1"])]
        cells += [variant_cell(v[k]) for k in ("olean-all", "olean-1")] if "olean-all" in v \
            else ["n/a (not Lean v4.36.0)", "n/a"]
        ident = all(x.get("identical") is not False for x in v.values())
        vrows.append(f"| {r['id']} | " + " | ".join(cells) + f" | {'yes' if ident else 'NO'} |")
    mism = []
    for r in results:
        c = r["compare"]
        for n, lv in c["nitro_only_accept"]:
            mism.append(f"- **soundness**: `{n}` ({r['id']}): nitrolean accepts, Lean {lv}")
        for n, nv in c["nitro_only_reject"]:
            mism.append(f"- `{n}` ({r['id']}): Lean accepts, nitrolean {nv}")
        for n, lv, nv in c["kind_differs"]:
            mism.append(f"- `{n}` ({r['id']}): both reject, Lean {lv}, nitrolean {nv}")
    text = f"""# Corpus oracle results

Written by `bench/oracle/run.py` ({results[0]['date'] if results else ''};
{nitro_version}, {results[0]['threads_all'] if results else '?'} cores). How the verdicts are
obtained is in `README.md`. Times are wall-clock seconds and memory is peak resident MiB,
of the first run on the whole export (`check --threads 0` for nitrolean,
`leanchecker --from-export` for Lean).

| project | Lean | declarations | agree | nitrolean-only reject | nitrolean-only accept | nitrolean | leanchecker | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- |
""" + "\n".join(rows) + """

## Variants

nitrolean's verdicts on each project from the NDJSON export and from the project's .olean
files, with all cores and with one thread. The .olean runs load the roots and everything
they import, the Lean core library included, so they check more than the export.

| project | NDJSON, all cores | NDJSON, 1 thread | .olean, all cores | .olean, 1 thread | identical |
| --- | --- | --- | --- | --- | --- |
""" + "\n".join(vrows) + "\n\n## Mismatches\n\n" + ("\n".join(mism) if mism else "None.") + "\n"
    with open(path, "w") as f:
        f.write(text)


def projects(tier, only):
    out = []
    with open(os.path.join(HERE, "projects.tsv")) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            cols = line.rstrip("\n").split("\t")
            if (only and cols[0] in only) or (not only and int(cols[1]) <= tier):
                out.append(cols[0])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tier", type=int, default=1)
    ap.add_argument("--only", default="")
    ap.add_argument("--out", default=os.environ.get("ORACLE_OUT", os.path.join(HERE, "out")))
    ap.add_argument("--nitrolean", default=os.path.join(ROOT, "target", "release", "nitrolean"))
    ap.add_argument("--timeout", type=float, default=3600)
    ap.add_argument("--mem-mib", type=int, default=64 * 1024)
    ap.add_argument("--max-rounds", type=int, default=50)
    ap.add_argument("--results", default=os.path.join(HERE, "RESULTS.md"))
    ap.add_argument("--keep-logs", action="store_true")
    args = ap.parse_args()
    only = [x for x in args.only.split(",") if x]
    results = []
    bad = False
    for pid in projects(args.tier, only):
        r = run_project(pid, args)
        if r is None:
            bad = True
            continue
        results.append(r)
        c = r["compare"]
        for n, lv in c["nitro_only_accept"]:
            print(f"SOUNDNESS {pid}: nitrolean accepts {n}, Lean {lv}")
        for n, nv in c["nitro_only_reject"]:
            print(f"MISMATCH {pid}: Lean accepts {n}, nitrolean {nv}")
        for n, lv, nv in c["kind_differs"]:
            print(f"KIND {pid}: {n}: Lean {lv}, nitrolean {nv}")
        for k, v in r["variants"].items():
            if v.get("identical") is False:
                print(f"VARIANT {pid}: {k} differs: {v.get('status')} {v.get('decl', '')}")
                bad = True
        bad |= bool(c["nitro_only_accept"] or c["nitro_only_reject"] or c["kind_differs"])
        print(f"{pid}: {r['constants']} constants, agree {c['agree']}, nitrolean-only reject "
              f"{len(c['nitro_only_reject'])}, nitrolean-only accept {len(c['nitro_only_accept'])}")
    ver = subprocess.run([args.nitrolean, "--version"], capture_output=True, text=True).stdout
    try:
        commit = subprocess.run(["git", "-C", ROOT, "rev-parse", "HEAD"],
                                capture_output=True, text=True).stdout.strip()
    except OSError:
        commit = ""
    if results:
        write_results(results, args.results, f"{ver.strip()} at {commit}" if commit else ver)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
