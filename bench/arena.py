#!/usr/bin/env python3
"""Run the lean-kernel-arena test cases against ocaml4lean and the official kernel.

For every test YAML with a `leanfile` (or a ready `file`), the Lean source is
compiled with the official toolchain, the requested declarations are exported
with tools/Export.lean, and then
  * ocaml4lean checks the export file, and
  * the official kernel replays the same declarations (tools/Replay.lean).
Outcomes are compared with the expected one; wall time and peak RSS are recorded.

usage: arena.py ARENA_DIR WORK_DIR [glob...]
"""
import glob, json, os, re, shutil, signal, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_HOME = os.environ.get("LEAN_HOME", "/opt/lean/lean-4.35.0-linux")
LEAN = os.path.join(LEAN_HOME, "bin", "lean")
CHECKER = os.path.join(ROOT, "_build", "default", "bin", "main.exe")
JOBS = os.environ.get("JOBS", "1")

def yaml_get(text, key):
    m = re.search(r'^%s:\s*(.*)$' % re.escape(key), text, re.M)
    return m.group(1).strip() if m else None

def timed(cmd, env=None, timeout=600):
    t0 = time.time()
    p = subprocess.Popen(["/usr/bin/time", "-f", "MAXRSS %M"] + cmd, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, env=env, start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)   # kill the checker too, not only /usr/bin/time
        p.communicate()
        return None, time.time() - t0, 0, "timeout"
    p.stdout, p.stderr = out, err
    dt = time.time() - t0
    m = re.search(r"MAXRSS (\d+)", p.stderr)
    return p.returncode, dt, int(m.group(1)) if m else 0, p.stdout + p.stderr

def main():
    arena, work = sys.argv[1], sys.argv[2]
    pats = sys.argv[3:] or ["perf/*.yaml", "bugs/*.yaml", "corner-cases/*.yaml", "other/*.yaml"]
    os.makedirs(work, exist_ok=True)
    results = []
    for pat in pats:
        for y in sorted(glob.glob(os.path.join(arena, "tests", pat))):
            text = open(y).read()
            name = os.path.relpath(y, os.path.join(arena, "tests"))[:-5]
            outcome = yaml_get(text, "outcome")
            leanfile = yaml_get(text, "leanfile")
            file_ = yaml_get(text, "file")
            decls = yaml_get(text, "export-decls")
            decls = json.loads(decls) if decls else None
            mod = re.sub(r'[^A-Za-z0-9]', '_', name)
            mod = "T_" + mod
            nd = os.path.join(work, mod + ".ndjson")
            rec = {"test": name, "expected": outcome}
            tmo = min(600, int(yaml_get(text, "timeout") or 600))
            env = dict(os.environ, LEAN_PATH=work + ":" + os.path.join(LEAN_HOME, "lib", "lean"),
                       PATH=os.path.join(LEAN_HOME, "bin") + ":" + os.environ["PATH"])
            if leanfile:
                src = os.path.join(arena, leanfile)
                shutil.copy(src, os.path.join(work, mod + ".lean"))
                if not os.path.exists(os.path.join(work, mod + ".olean")):
                    r = subprocess.run([LEAN, "-o", os.path.join(work, mod + ".olean"), os.path.join(work, mod + ".lean")],
                                       capture_output=True, text=True, env=env, cwd=work, timeout=1800)
                    if r.returncode != 0:
                        rec["error"] = "compile failed: " + (r.stdout + r.stderr)[-300:]
                        results.append(rec); print(json.dumps(rec)); continue
                if decls is None:
                    rec["skipped"] = "whole-module export (not supported here)"
                    results.append(rec); print(json.dumps(rec)); continue
                if not os.path.exists(nd):
                    with open(nd, "w") as f:
                        r = subprocess.run([LEAN, "--run", os.path.join(ROOT, "tools", "Export.lean"), mod, "--"] + decls,
                                           stdout=f, stderr=subprocess.PIPE, text=True, env=env, cwd=work, timeout=1800)
                    if r.returncode != 0:
                        rec["error"] = "export failed: " + r.stderr[-300:]
                        os.remove(nd); results.append(rec); print(json.dumps(rec)); continue
                code, dt, rss, out = timed([LEAN, "--run", os.path.join(ROOT, "tools", "Replay.lean"), mod, "--"] + decls, env=env, timeout=tmo)
                m = re.search(r"in ([0-9.e+-]+)s", out)
                rec["official"] = {"accept": code == 0 if code is not None else None, "timeout": code is None, "wall": dt, "kernel_time": float(m.group(1)) if m else None, "rss_kb": rss}
            elif file_:
                nd = os.path.join(arena, file_)
            else:
                continue
            code, dt, rss, out = timed([CHECKER, "-j", JOBS, "--stats", nd], timeout=tmo)
            m = re.search(r"check ([0-9.]+)s", out)
            rec["ocaml4lean"] = {"accept": code == 0 if code is not None else None, "timeout": code is None, "wall": dt, "check_time": float(m.group(1)) if m else None,
                                 "rss_kb": rss, "msg": out.strip().splitlines()[-1][:160] if out.strip() else "",
                                 "exit": code}
            exp_acc = {"accept": True, "reject": False}.get(outcome)
            if exp_acc is not None:
                rec["ok"] = rec["ocaml4lean"]["accept"] == exp_acc
            results.append(rec)
            print(json.dumps(rec), flush=True)
    with open(os.path.join(work, "results.json"), "w") as f:
        json.dump(results, f, indent=1)

if __name__ == "__main__":
    main()
