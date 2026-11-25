#!/usr/bin/env python3
"""The DAG's verifier (docs/GITHUB_PLATFORM.md, "Workflows"). Untrusted, standard library only.

    python3 dag_verify.py verify --dag BASE --new NEW --out OUT [--env ID] [--records DIR]
    python3 dag_verify.py semantic --dag DAG PATH

`verify` checks the files a pull request adds. `BASE` is a checkout of the DAG's `main`; `NEW`
holds the added files at their repository paths (`dag/...`). It lays both out in a Lake workspace
that requires this checkout's core (in CI, the environment image's), and checks every added node,
definitions first, then theorems, then solutions, each after the nodes it imports:

* the metadata file (`.json`) against its schema, and the names in it against the path;
* the imports (`dag.import_problem`), then the syntactic filter (`#sigaba_neo_platform_lint`);
* the build (`CE` on failure);
* definitions: nothing forbidden, no `sorry`; theorems: the statement ends in `:= by sorry` and
  the file declares the named theorem and nothing else; solutions: the statuses of the server
  (`WA`, `SORRY`, `FAILED`; `ACCEPTED` when every theorem it uses is proved in this environment
  according to `--records`, else `SKETCH_ACCEPTED`);
* semantic IDs of definitions and theorems (`DUPLICATE` if an existing node of this environment,
  or another added node, has the same ID), and the hash of solutions (`DUPLICATE` if the theorem
  already has a solution with the same normalized text);
* for solutions, the std modules they import, transitively, with their hashes (the record's
  `std` field).

It writes `OUT/result.json` (schemas/result.schema.json), or with `--out -` prints it on standard
output, and exits 0 when every item passed, 1 otherwise. Lean code runs while it builds: run it in
the sandbox (no network, no credentials).

In the gate's container the verifier runs as root without capabilities except changing its user,
with `SIGABA_LEAN_UID` set: every Lean and Lake process then runs as that user, which cannot write
the sources (written by root), cannot signal the verifier, and is killed after each step. The
result goes to the verifier's own standard output. The build outputs of definitions and theorems
are hashed after they are built; a later step that changes them fails its item.

`semantic` prints the semantic ID of one built node of a DAG checkout (for maintainers).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

import dag as D

LIBS = ("Definitions", "Theorems", "Solutions")


def errors(log: str, n: int = 40) -> str:
    lines = [l for l in log.splitlines() if l.startswith("error") and "build failed" not in l]
    return "\n".join(lines[:n]) if lines else "\n".join(log.splitlines()[-n:])


class Workspace:
    """A Lake project with the DAG's layout (`dag/` as its source directory) that requires the
    core and links its built packages, so that it never fetches or rebuilds Mathlib."""

    def __init__(self, d: Path, core: Path = D.CORE, timeout: float | None = 1800):
        self.dir, self.core, self.timeout = d, core, timeout
        uid = os.environ.get("SIGABA_LEAN_UID")
        self.uid = int(uid) if uid and os.geteuid() == 0 else None
        d.mkdir(parents=True, exist_ok=True)
        (d / "lakefile.toml").write_text(
            'name = "dag"\nsrcDir = "dag"\nleanOptions = { autoImplicit = false }\n\n'
            f'[[require]]\nname = "SigabaNeo"\npath = {json.dumps(str(core))}\n' +
            "".join(f'\n[[lean_lib]]\nname = "{lib}"\n' for lib in LIBS))
        m = json.loads((core / "lake-manifest.json").read_text())
        m.update(name="dag", packages=[
            {"type": "path", "scope": "", "name": "SigabaNeo", "manifestFile": "lake-manifest.json",
             "inherited": False, "dir": str(core), "configFile": "lakefile.toml"},
            *[dict(p, inherited=True) for p in m["packages"]]])
        (d / "lake-manifest.json").write_text(json.dumps(m, indent=1) + "\n")
        (d / "lean-toolchain").write_text((core / "lean-toolchain").read_text())
        (d / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
        for p in (core / ".lake" / "packages").iterdir():
            if not (dst := d / ".lake" / "packages" / p.name).exists():
                dst.symlink_to(p.resolve())
        for lib in LIBS:
            (d / "dag" / lib).mkdir(parents=True, exist_ok=True)
        (d / ".lake" / "out").mkdir(parents=True, exist_ok=True)
        if self.uid is not None:     # Lean may create its build outputs, not touch the rest
            os.chmod(d / ".lake", 0o1777)
            os.chmod(d / ".lake" / "out", 0o1777)

    def outputs(self) -> dict[str, str]:
        """The hashes of the built modules of definitions and theorems."""
        out = {}
        base = self.dir / ".lake" / "build"
        for sub in ("lib/lean/Definitions", "lib/lean/Theorems", "ir/Definitions", "ir/Theorems"):
            if (base / sub).is_dir():
                for p in (base / sub).rglob("*"):
                    if p.is_file():
                        out[str(p.relative_to(base))] = hashlib.sha256(p.read_bytes()).hexdigest()
        return out

    def run(self, args: list[str], stdin: str | None = None) -> subprocess.CompletedProcess:
        env = {k: v for k, v in os.environ.items()
               if k not in ("LEAN_PATH", "LEAN_SRC_PATH", "SIGABA_LEAN_UID")}
        user = {} if self.uid is None else {"user": self.uid, "group": self.uid, "extra_groups": []}
        # Its own session, so that a timeout kills the whole tree (Lake's `lean` children too).
        p = subprocess.Popen(args, cwd=self.dir, env=env, text=True, stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             start_new_session=True, **user)
        try:
            out, err = p.communicate(stdin, timeout=self.timeout)
            return subprocess.CompletedProcess(args, p.returncode, out, err)
        except subprocess.TimeoutExpired:
            self.kill_all(p)
            try:
                p.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                pass
            return subprocess.CompletedProcess(args, 124, "", f"error: timed out after {self.timeout}s")
        finally:
            if self.uid is not None:     # nothing the step started may outlive it
                self.kill_all(None)

    def kill_all(self, p: subprocess.Popen | None) -> None:
        """Kill what a step started: as the Lean user (the verifier has no right to signal it), every
        process of that user; otherwise the step's process group."""
        if self.uid is not None:
            subprocess.run(["sh", "-c", "kill -9 -1 2>/dev/null; true"], user=self.uid,
                           group=self.uid, extra_groups=[], timeout=30)
        elif p is not None:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass

    def build(self, modules: list[str]) -> subprocess.CompletedProcess:
        return self.run(["lake", "build", *modules])

    def platform(self, cmd: str) -> dict:
        """Run a `#sigaba_neo_platform_*` command whose last argument is the output file."""
        out = self.dir / ".lake" / "out" / "platform-out.json"
        out.unlink(missing_ok=True)
        r = self.run(["lake", "env", "lean", "--stdin"],
                     stdin=f'import SigabaNeo.Platform\n{cmd} ".lake/out/platform-out.json"\n')
        if r.returncode != 0 or not out.exists():   # a result counts only from a normal exit
            return {"status": "ERROR", "message": errors(r.stdout + r.stderr)}
        return json.loads(out.read_text())

    def lint(self, path: str, imports: list[str]) -> dict:
        """The syntactic filter on `path`. The running Lean imports the file's own (allowed, built)
        imports too, so that their environment extensions exist when the file is parsed."""
        out = self.dir / ".lake" / "out" / "platform-lint.json"
        out.unlink(missing_ok=True)
        r = self.run(["lake", "env", "lean", "--stdin"], stdin=(
            "".join(f"import {i}\n" for i in imports) +
            f'import SigabaNeo.Platform\n#sigaba_neo_platform_lint ".lake/out/platform-lint.json" '
            f'{json.dumps(path)}\n'))
        if r.returncode != 0 or not out.exists():
            return {"status": "ERROR", "message": errors(r.stdout + r.stderr)}
        return json.loads(out.read_text())["files"][0]


def lean_str(s: str) -> str:
    return json.dumps(s)


def topo(items: list[dict]) -> list[dict]:
    """Added items in dependency order: definitions, theorems, solutions; within a kind, each
    after the added modules it imports."""
    rank = {"definition": 0, "theorem": 1, "solution": 2, "note": 3}
    by_mod = {D.module_of(i["path"]): i for i in items if i["path"].endswith(".lean")}
    out, seen = [], set()

    def visit(i: dict, stack: tuple = ()) -> None:
        if i["path"] in seen or i["path"] in stack:
            return
        for m in i.get("imports", []):
            if m in by_mod:
                visit(by_mod[m], stack + (i["path"],))
        seen.add(i["path"])
        out.append(i)

    for i in sorted(items, key=lambda i: (rank[i["kind"]], i["path"])):
        visit(i)
    return out


def verify(base: Path, new: Path | None, env_id: str | None, records_dir: Path | None, work: Path,
           core: Path = D.CORE, timeout: float = 1800, reverify: list[str] | None = None,
           revision: str | None = None) -> dict:
    """Check the files of `new` (added to `base`), or with `reverify`, those paths of `base` again
    (in another environment or under another std release)."""
    dag = D.Dag(base)
    env = dag.environment(env_id) or {"id": env_id or "local", "std": None}
    records = D.read_records(records_dir)
    known_ids: dict[str, str] = {}
    recorded: set[str] = set()
    for r in records.get(env["id"], []):
        if D.id_record(r):
            known_ids.setdefault(r["id"], r["path"])
            recorded.add(r["path"])
    proved = {n for n, t in D.status(dag, records, env).theorems.items() if t["status"] == "Proved"}
    manifest = D.std_manifest(core)

    ws = Workspace(work, core, timeout)
    if (base / "dag").is_dir():
        for p in (base / "dag").rglob("*.lean"):
            dst = ws.dir / p.relative_to(base)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)

    # Duplicates are decided against the whole base: its definitions and theorems that the records
    # do not cover yet (records are published after a merge, and may lag) are checked too, as
    # *shadow* items. They go through the very checks a checked node goes through, in one
    # dependency order with the checked nodes, sharing which modules failed; their statuses are
    # not reported. A shadow that passes is a candidate owner of its ID; one that fails is none;
    # one whose check does not finish (ERROR) leaves duplicates undecidable.
    shadows = []
    for n in dag.nodes():
        if n.kind not in ("definition", "theorem") or n.path in recorded or \
                n.path in (reverify or []):
            continue
        shadows.append({"path": n.path, "kind": n.kind, "text": n.text, "meta": n.meta or None,
                        "match": D.classify(n.path)[1], "imports": n.imports, "shadow": True})

    items: list[dict] = []
    results: list[dict] = []
    src = base if reverify is not None else new
    if reverify is not None:
        new_files = sorted({f for p in reverify for f in (p, p.removesuffix(".lean") + ".json")
                            if (base / f).is_file()})
    else:
        new_files = sorted(str(p.relative_to(new)) for p in new.rglob("*") if p.is_file())
    leans = [f for f in new_files if not f.endswith(".json")]
    for f in new_files:
        c = D.classify(f)
        if c is None:
            results.append({"path": f, "kind": "note", "status": "ERROR",
                            "message": "not a path of the DAG's layout"})
        elif f.endswith(".json") and f.removesuffix(".json") + ".lean" not in leans:
            results.append({"path": f, "kind": c[0], "status": "ERROR",
                            "message": "a metadata file without its .lean file"})
    for f in leans:
        c = D.classify(f)
        if c is None:
            continue
        kind, m = c
        text = (src / f).read_text()
        if kind == "note":
            items.append({"path": f, "kind": kind, "name": m.group(1), "text": text})
            continue
        js = src / (f.removesuffix(".lean") + ".json")
        meta = json.loads(js.read_text()) if js.exists() else None
        if reverify is None and (base / f).exists():
            results.append({"path": f, "kind": kind, "status": "ERROR",
                            "message": "the node already exists; nodes are never changed"})
            continue
        items.append({"path": f, "kind": kind, "text": text, "meta": meta, "match": m,
                      "imports": D.imports_of(text)})
        dst = ws.dir / f
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text)

    added_ids: dict[str, str] = {}
    failed_modules: set[str] = set()
    base_errors: list[str] = []
    scanned_ids: dict[str, list[str]] = {}   # shadows' IDs: computed, not established by a record
    for it in topo(items + shadows):
        if it.get("shadow"):
            r = check_item(it, ws, dag, base, proved, known_ids, {}, failed_modules, manifest,
                           core)
            if r["status"] == "OK" and r.get("id"):
                scanned_ids.setdefault(r["id"], []).append(it["path"])
                continue
            failed_modules.add(D.module_of(it["path"]))
            if r["status"] == "ERROR":
                base_errors.append(f"{it['path']}: its check did not finish: "
                                   f"{r.get('message', '')[:500]}")
            continue
        before = ws.outputs()
        res = check_item(it, ws, dag, base, proved, known_ids, added_ids, failed_modules, manifest,
                         core)
        after = ws.outputs()
        changed = sorted(p for p, h in before.items() if after.get(p) != h)
        if changed:
            res.update(status="FAILED", message="building it changed the build outputs of other "
                       "modules: " + ", ".join(changed[:10]))
        if res["status"] not in ("OK", "ACCEPTED", "SKETCH_ACCEPTED") and it["kind"] != "note":
            failed_modules.add(D.module_of(it["path"]))
        results.append(res)
    if reverify is not None:             # checked nodes are the base's too: an undecided one
        for r in results:                  # leaves ownership undecided, as a shadow would
            if r["kind"] in ("definition", "theorem") and r["status"] == "ERROR":
                base_errors.append(f"{r['path']}: its check did not finish: "
                                   f"{r.get('message', '')[:500]}")
    if base_errors:                      # ownership is undecidable for the checked IDs
        for r in results:
            if r["kind"] in ("definition", "theorem") and r["status"] == "OK":
                r.update(status="ERROR", message="whether it duplicates a node of the base cannot "
                         "be decided:\n" + "\n".join(base_errors[:20]))
    assign_owners(results, known_ids, scanned_ids, reverify is not None)
    ok = all(r["status"] in ("OK", "ACCEPTED", "SKETCH_ACCEPTED") for r in results)
    out = {"ok": ok and bool(results), "env": env["id"], "fingerprint": D.text_fingerprint(core),
           "std": env.get("std"), "items": results}
    if revision:
        out["revision"] = revision
    return out


def assign_owners(results: list[dict], known: dict[str, str], scanned: dict[str, list[str]],
                  reverify: bool) -> None:
    """Decide which node owns each semantic ID; the others with it become DUPLICATE. The owner is
    the node whose record established the ID here; else, checking a pull request, a node of the
    base (the first by path); else the first by path among all the nodes that have it (the base's
    and the checked ones when re-verifying, the checked ones otherwise). It depends on neither the
    order the nodes were built in nor how they are split into batches."""
    checked: dict[str, list[str]] = {}
    for r in results:
        if r["kind"] in ("definition", "theorem") and r["status"] == "OK" and r.get("id"):
            checked.setdefault(r["id"], []).append(r["path"])
    for r in results:
        sid = r.get("id")
        if r["kind"] not in ("definition", "theorem") or r["status"] != "OK" or not sid:
            continue
        owner = known.get(sid)
        if owner is None:
            base = scanned.get(sid, [])
            pool = base + checked[sid] if reverify or not base else base
            owner = min(pool)
        if owner != r["path"]:
            r.update(status="DUPLICATE", message="a node with the same meaning exists",
                     duplicate_of=owner)


def check_item(it: dict, ws: Workspace, dag: D.Dag, base: Path, proved: set[str],
               known_ids: dict, added_ids: dict, failed: set[str], manifest: dict[str, str],
               core: Path) -> dict:
    kind, path = it["kind"], it["path"]
    res: dict = {"path": path, "kind": kind}

    def done(status: str, msg: str = "", **kw) -> dict:
        res.update(status=status, **({"message": msg[:20000]} if msg else {}), **kw)
        return res

    if kind == "note":
        res["name"] = it["name"]
        try:
            meta, _ = D.front_matter(it["text"])
        except ValueError as e:
            return done("FAILED", str(e))
        probs = D.validate(meta, D.schema("note"), "front matter")
        return done("FAILED", "\n".join(probs)) if probs else done("OK")

    meta, m = it["meta"], it["match"]
    probs = D.node_meta_problems(kind, path, meta, m)
    if probs:
        return done("FAILED", "\n".join(probs))
    name = meta["name"] if kind in ("definition", "theorem") else meta["theorem"]
    res["name"] = name
    module = D.module_of(path)
    disproof = kind == "solution" and meta["proof_type"] == "disprove"

    # Imports: allowed roots, existing DAG modules, nothing that failed in this run.
    probs = []
    for i in it["imports"]:
        if p := D.import_problem(i, disproof):
            probs.append(p)
        elif i.startswith(("Definitions.", "Theorems.")) and not (ws.dir / D.path_of(i)).exists():
            probs.append(f"import {i}: no such node")
        elif i in failed:
            probs.append(f"import {i}: that node fails its checks here")
        elif kind == "definition" and i.startswith("Theorems."):
            probs.append(f"import {i}: a definition may not import theorems")
    if kind == "solution":
        own = f"Theorems.Thm_{m.group(1)}"
        if not (ws.dir / D.path_of(own)).exists():
            probs.append(f"no theorem with the slug {m.group(1)}")
        if own in it["imports"] and disproof:
            probs.append("a disproof may not import its own target")
    if probs:
        return done("FAILED", "\n".join(probs))
    if kind == "theorem" and not D.ends_in_sorry(it["text"]):
        return done("FAILED", "the formal statement must end with `:= by sorry`")

    # The imports (and a solution's theorem) are built first, on their own: the node's build must
    # not change their outputs, which the checks below read. Then the syntactic filter (files are
    # parsed with their imports' syntax).
    deps = [i for i in it["imports"] if i.startswith(("Definitions.", "Theorems."))]
    if kind == "solution":
        deps.append(f"Theorems.Thm_{m.group(1)}")
    if deps:
        b = ws.build(deps)
        if b.returncode != 0:
            return done("CE" if b.returncode == 1 else "ERROR",   # a timeout or crash: undecided
                        "an imported node does not build:\n" + errors(b.stdout + b.stderr))
    snapshot = ws.outputs()

    def unchanged() -> dict | None:
        now = ws.outputs()
        changed = sorted(p for p, h in snapshot.items() if now.get(p) != h)
        return None if not changed else done(
            "FAILED", "building it changed the build outputs of other modules: " +
            ", ".join(changed[:10]))
    lint = ws.lint(path, it["imports"])
    if lint.get("status") == "ERROR":     # the filter did not finish: undecided, not rejected
        return done("ERROR", lint.get("message", "the filter did not run"))
    if lint["problems"]:
        return done("LINT", "\n".join(lint["problems"]))

    b = ws.build([module])
    if b.returncode != 0:
        return done("CE" if b.returncode == 1 else "ERROR",       # a timeout or crash: undecided
                    "compile error:\n" + errors(b.stdout + b.stderr))
    if bad := unchanged():
        return bad

    if kind in ("definition", "theorem"):
        r = ws.platform(f'#sigaba_neo_platform_module {lean_str(module)} "{kind}" '
                        f'{lean_str(name if kind == "theorem" else "_")}')
        if r["status"] != "OK":
            return done(r["status"] if r["status"] != "OK" else "FAILED", r.get("message", ""))
        s = ws.platform(f'#sigaba_neo_platform_semantic {lean_str(module)} "{kind}" '
                        f'{lean_str(name if kind == "theorem" else "_")}')
        if s.get("status") != "OK":      # undecided when the command itself did not finish
            return done("ERROR" if s.get("status") == "ERROR" else "FAILED",
                        s.get("message", "no semantic ID"))
        sid = D.semantic_id(s)
        res["id"] = sid
        if bad := unchanged():
            return bad
        # Who owns the ID is decided once every item has its ID (`assign_owners`).
        return done("OK")

    # A solution.
    h = D.solution_hash(it["text"])
    res.update(hash=h, theorem=name, proof_type=meta["proof_type"])
    thm = dag.theorem_by_slug(m.group(1))
    for other in (dag.solutions(thm) if thm else []):
        if other.path != path and D.solution_hash(other.text) == h:
            return done("DUPLICATE", "the theorem has a solution with the same text",
                        duplicate_of=other.path)
    same = f"solution:{m.group(1)}:{h}"           # an earlier solution of this pull request
    if added_ids.get(same, path) != path:
        return done("DUPLICATE", "the theorem has a solution with the same text",
                    duplicate_of=added_ids[same])
    r = ws.platform(f'#sigaba_neo_platform_submission {lean_str(name)} "{meta["proof_type"]}" '
                    f'{lean_str(module)}')
    if r["status"] != "OK":
        return done(r["status"], r.get("message", ""))
    uses = r.get("uses", [])
    # The std modules it imports, through the DAG modules it imports.
    seen, todo, mods = set(), list(it["imports"]), []
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        mods.append(i)
        if i.startswith(("Definitions.", "Theorems.")) and (ws.dir / D.path_of(i)).exists():
            todo += D.imports_of((ws.dir / D.path_of(i)).read_text())
    std = {s: manifest[s] for s in D.std_closure(mods, core) if s in manifest}
    if bad := unchanged():
        return bad
    status = "ACCEPTED" if disproof or all(u in proved for u in uses) else "SKETCH_ACCEPTED"
    added_ids[same] = path
    return done(status, uses=uses, std=std)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="action", required=True)
    v = sub.add_parser("verify")
    v.add_argument("--dag", type=Path, required=True, help="a checkout of the DAG's main")
    v.add_argument("--new", type=Path, help="the added files, at their paths")
    v.add_argument("--reverify", type=Path, help="a JSON list of paths of the DAG to check again "
                   "(instead of --new)")
    v.add_argument("--out", required=True, help="a directory for result.json, or - for stdout")
    v.add_argument("--revision", help="the commit being verified, echoed in the result")
    v.add_argument("--env", help="the environment's id (default: the DAG's default)")
    v.add_argument("--records", type=Path, help="a checkout of the records branch")
    v.add_argument("--workdir", type=Path, help="default: a temporary directory")
    v.add_argument("--timeout", type=float, default=1800, help="per Lake call, in seconds")
    s = sub.add_parser("semantic")
    s.add_argument("--dag", type=Path, required=True)
    s.add_argument("path", help="dag/Definitions/… or dag/Theorems/…")
    a = ap.parse_args(argv)
    if a.action == "semantic":
        ws = Workspace(Path(tempfile.mkdtemp(prefix="dag-semantic-")))  # noqa: F841
        for p in (a.dag / "dag").rglob("*.lean"):
            dst = ws.dir / p.relative_to(a.dag)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        node = next(n for n in D.Dag(a.dag).nodes() if n.path == a.path)
        b = ws.build([node.module])
        if b.returncode != 0:
            print(errors(b.stdout + b.stderr))
            return 1
        r = ws.platform(f'#sigaba_neo_platform_semantic {lean_str(node.module)} "{node.kind}" '
                        f'{lean_str(node.name)}')
        if r.get("status") != "OK":
            print(r.get("message"))
            return 1
        print(D.semantic_id(r))
        return 0
    work = a.workdir or Path(tempfile.mkdtemp(prefix="dag-verify-"))
    if (a.new is None) == (a.reverify is None):
        ap.error("give exactly one of --new and --reverify")
    again = json.loads(a.reverify.read_text()) if a.reverify else None
    out = verify(a.dag.resolve(), a.new.resolve() if a.new else None, a.env, a.records,
                 work.resolve(), timeout=a.timeout, reverify=again, revision=a.revision)
    if a.out == "-":
        sys.stdout.write(json.dumps(out) + "\n")
    else:
        Path(a.out).mkdir(parents=True, exist_ok=True)
        (Path(a.out) / "result.json").write_text(json.dumps(out, indent=1) + "\n")
    for r in out["items"]:
        print(f"{r['status']:16} {r['path']}" + (f"\n  {r['message'][:2000]}" if r.get("message")
                                                 else ""), file=sys.stderr)
    return 0 if out["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
