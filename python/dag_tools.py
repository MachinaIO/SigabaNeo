#!/usr/bin/env python3
"""The DAG's tools that run no Lean (docs/GITHUB_PLATFORM.md). Standard library only.

CI's trusted jobs (they never run code of a pull request):

    fetch     --repo O/R --base SHA --head SHA --out DIR
              the files the event's head commit adds, as data, through the API
    precheck  --dag BASE --fetched DIR --author LOGIN --out precheck.json
              who may submit, where, how much, the metadata and the notes
    check-result RESULT.json         the verifier's output against its schema
    decide    --precheck P --result R --dag BASE --author LOGIN --event E --out decision.json
    records   --result R --records DIR [--author --pr --commit --run]
              append the verified nodes to the records branch
    index     --dag DAG --records DIR --out DIR [--core CORE]
              statuses per environment, open leaves, needs port, search entries, std candidates
    reverify-plan --dag DAG --records DIR --env ID --out plan.json

Maintainers:

    std-manifest --tag TAG [--core CORE] --dag DAG     add a std release to env/std.json
    init DIR --core-url URL --core-rev REV --image IMG --owner LOGIN [--core-path PATH]
              a new DAG repository: layout, environment, meta, workflows, instructions
    import-server DATA_DIR --out DIR   the nodes of the retired server's database, as DAG files
    formalpedia --dag DAG --out DIR [--mirror DIR] [--env E] [--match RE] [--limit N]
              Formalpedia's new items, as DAG files (to open as a pull request)
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import sqlite3
import sys
import time
import urllib.request
from pathlib import Path

import dag as D
from research import records as RR

TEMPLATES = D.CORE / "templates" / "dag"


# -- fetch ---------------------------------------------------------------------------------------


def api(path: str, token: str | None, accept: str = "application/vnd.github+json"):
    req = urllib.request.Request("https://api.github.com" + path)
    req.add_header("Accept", accept)
    req.add_header("User-Agent", "sigaba-neo-dag-tools")
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read())


# The compare API lists at most this many files; above it, `fetch` diffs the trees itself.
COMPARE_FILES = 300
# Above this many added files, contents come from one archive of `head` instead of one API call
# per blob (the token's rate limit would not allow thousands of calls).
BLOB_CALLS = 50


def tree_diff(repo: str, token: str | None, old: str, new: str) -> list[dict]:
    """The files that differ between commits `old` and `new`, as the compare API reports them
    (`filename`, `status` in added / removed / modified), from the commits' recursive trees."""
    def flat(sha: str) -> dict[str, dict]:
        root = api(f"/repos/{repo}/git/commits/{sha}", token)["tree"]["sha"]
        t = api(f"/repos/{repo}/git/trees/{root}?recursive=1", token)
        if t.get("truncated"):
            raise SystemExit("the commit's tree is too large to list")
        return {e["path"]: e for e in t.get("tree", []) if e.get("type") != "tree"}
    a, b = flat(old), flat(new)
    rows = []
    for path in sorted(set(a) | set(b)):
        if path not in a:
            rows.append({"filename": path, "status": "added"})
        elif path not in b:
            rows.append({"filename": path, "status": "removed"})
        elif (a[path]["sha"], a[path].get("mode")) != (b[path]["sha"], b[path].get("mode")):
            rows.append({"filename": path, "status": "modified"})
    return rows


def head_archive(repo: str, token: str | None, head: str) -> dict[str, bytes]:
    """The regular files of commit `head`, by path, read from its tarball (one request). Only
    regular members are read: links and other members are skipped, never followed. Contents are
    data."""
    import io
    import tarfile
    req = urllib.request.Request(f"https://api.github.com/repos/{repo}/tarball/{head}")
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("User-Agent", "sigaba-neo-dag-tools")
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(req, timeout=600) as r:
        raw = r.read()
    files: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as tar:
        for m in tar:
            if not m.isreg() or "/" not in m.name:
                continue
            path = m.name.split("/", 1)[1]      # drop the archive's top directory
            if not D.classify(path):
                continue
            fh = tar.extractfile(m)
            if fh is not None:
                files[path] = fh.read()
    return files


def fetch(repo: str, out: Path, token: str | None, base: str, head: str) -> list[dict]:
    """The files that commit `head` changes against `base` (the event's commits, which do not
    move), with the content of the added ones under `out/files/<path>`, and the list in
    `out/files.json` with `head` as its revision. A file's mode and blob come from the tree entry
    of `head` itself: a symbolic link or a submodule is reported as such and not downloaded.
    Contents are data: nothing here interprets them."""
    for sha in (base, head):
        if not re.fullmatch(r"[0-9a-f]{40}", sha or ""):
            raise SystemExit(f"not a commit: {sha!r}")
    cmp = api(f"/repos/{repo}/compare/{base}...{head}", token)
    files = cmp.get("files", [])
    if len(files) >= COMPARE_FILES:
        # The compare API lists at most 300 files. A large pull request is listed from the full
        # trees of the merge base and of `head` instead (the same three-dot comparison).
        merge_base = (cmp.get("merge_base_commit") or {}).get("sha", "")
        if not re.fullmatch(r"[0-9a-f]{40}", merge_base):
            raise SystemExit("too many changed files, and no merge base to list them from")
        files = tree_diff(repo, token, merge_base, head)
    trees: dict[str, dict] = {}

    def tree(sha: str) -> dict:
        if sha not in trees:
            t = api(f"/repos/{repo}/git/trees/{sha}", token)
            trees[sha] = {e["path"]: e for e in t.get("tree", [])}
        return trees[sha]

    root = api(f"/repos/{repo}/git/commits/{head}", token)["tree"]["sha"]

    def entry(path: str) -> dict | None:
        node = {"type": "tree", "sha": root}
        for part in path.split("/"):
            if node.get("type") != "tree":
                return None
            node = tree(node["sha"]).get(part)
            if node is None:
                return None
        return node

    out.mkdir(parents=True, exist_ok=True)
    wanted = [f["filename"] for f in files if f["status"] == "added" and D.classify(f["filename"])]
    archive = head_archive(repo, token, head) if len(wanted) > BLOB_CALLS else None
    rows = []
    for f in files:
        row = {"filename": f["filename"], "status": f["status"]}
        if f["status"] == "added" and D.classify(f["filename"]):
            e = entry(f["filename"])
            row.update(type=(e or {}).get("type"), mode=(e or {}).get("mode"))
            if e is None or e["type"] != "blob" or e["mode"] not in ("100644", "100755"):
                rows.append(row)
                continue
            if archive is not None:
                data = archive.get(f["filename"])
                if data is None:
                    rows.append(row)
                    continue
            else:
                blob = api(f"/repos/{repo}/git/blobs/{e['sha']}", token)
                data = base64.b64decode(blob["content"]) if blob.get("encoding") == "base64" \
                    else blob["content"].encode()
            row["size"] = len(data)
            if len(data) <= D.LIMITS["file_bytes"]:
                dst = out / "files" / f["filename"]
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(data)
        rows.append(row)
    (out / "files.json").write_text(json.dumps({"revision": head, "files": rows}, indent=1) + "\n")
    return rows


# -- precheck ------------------------------------------------------------------------------------


WRITERS = ("admin", "maintain", "write")


def precheck(base: D.Dag, rows: list[dict], content: Path, author: str,
             revision: str | None = None, permission: str | None = None) -> dict:
    """Everything that can be decided without Lean: the author, the paths (only additions under
    `dag/`), sizes, metadata, notes and imports. `permission` is the author's permission on the
    repository as GitHub reports it (`admin`, `write`, `read`, `none`), which the `collaborators`
    mode needs."""
    trusted = base.trusted()
    problems: list[str] = []
    mode = trusted.get("mode")
    # `collaborators`: whoever has write access to the repository, and those listed.
    writer = mode == "collaborators" and permission in WRITERS
    accepted = mode == "open" or writer or author in trusted.get("accept", [])
    if not accepted:
        why = (f"@{author} has no write access to this repository (permission "
               f"{permission or 'unknown'})" if mode == "collaborators"
               else f"@{author} may not submit to this DAG yet")
        problems.append(f"{why} (meta/trusted.json); nothing of the pull request was run")
        return {"ok": False, "accepted": False, "automerge": False, "problems": problems,
                "added": [], "revision": revision}
    if not rows:
        problems.append("the pull request changes nothing")
    if len(rows) > D.LIMITS["files"]:
        problems.append(f"more than {D.LIMITS['files']} files")
    total = 0
    added: dict[str, str] = {}
    for r in rows:
        f = r["filename"]
        if r["status"] != "added":
            problems.append(f"{f}: {r['status']}; a pull request may only add files (nodes are "
                            "never changed, renamed or deleted)")
            continue
        if r.get("type") != "blob" or r.get("mode") not in ("100644", "100755"):
            problems.append(f"{f}: not a regular file in the commit (type {r.get('type')}, "
                            f"mode {r.get('mode')})")
            continue
        if D.classify(f) is None:
            problems.append(f"{f}: not a path of the DAG's layout (dag/Definitions/Def_<name>, "
                            "dag/Theorems/Thm_<slug>, dag/Solutions/<slug>/Sub_<id>, "
                            "dag/Notes/<slug>.md)")
            continue
        size = r.get("size", 0)
        total += size
        if size > D.LIMITS["file_bytes"]:
            problems.append(f"{f}: larger than {D.LIMITS['file_bytes']} bytes")
            continue
        p = content / f
        if not p.is_file():
            problems.append(f"{f}: its content could not be fetched")
            continue
        try:
            added[f] = p.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            problems.append(f"{f}: not UTF-8")
    if total > D.LIMITS["total_bytes"]:
        problems.append(f"more than {D.LIMITS['total_bytes']} bytes in all")

    new_theorems = {}
    for f, text in added.items():
        kind, m = D.classify(f)
        if kind == "note" or f.endswith(".json"):
            continue
        js = f.removesuffix(".lean") + ".json"
        meta = None
        if js in added:
            try:
                meta = json.loads(added[js])
            except json.JSONDecodeError as e:
                problems.append(f"{js}: not JSON: {e}")
                continue
        problems += [f"{f}: {p}" for p in D.node_meta_problems(kind, f, meta, m)]
        if kind == "theorem" and meta:
            new_theorems[m.group(1)] = meta.get("name")
        disproof = kind == "solution" and (meta or {}).get("proof_type") == "disprove"
        for i in D.imports_of(text):
            if p := D.import_problem(i, disproof):
                problems.append(f"{f}: {p}")
            elif i.startswith(("Definitions.", "Theorems.")):
                if D.path_of(i) not in added and not (base.root / D.path_of(i)).exists():
                    problems.append(f"{f}: import {i}: no such node")
        if kind == "theorem" and not D.ends_in_sorry(text):
            problems.append(f"{f}: the formal statement must end with `:= by sorry`")
    for f in added:
        if f.endswith(".json") and f.removesuffix(".json") + ".lean" not in added:
            problems.append(f"{f}: a metadata file without its .lean file")
    for f in added:
        kind, m = D.classify(f)
        if kind == "solution" and f.endswith(".lean"):
            s = m.group(1)
            if s not in new_theorems and not (base.root / f"dag/Theorems/Thm_{s}.lean").exists():
                problems.append(f"{f}: no theorem with the slug {s}")
    # Notes: front matter, references to nodes that exist (here or in this pull request).
    in_pr = {}
    for f, text in added.items():
        if f.endswith(".md") or f.endswith(".json"):
            continue
        kind, m = D.classify(f)
        js = added.get(f.removesuffix(".lean") + ".json")
        try:
            meta = json.loads(js) if js else {}
        except json.JSONDecodeError:
            meta = {}
        in_pr[f] = (kind, meta)
    for f, text in added.items():
        if not f.endswith(".md"):
            continue
        try:
            meta, _ = D.front_matter(text)
        except ValueError as e:
            problems.append(f"{f}: {e}")
            continue
        problems += [f"{f}: {p}" for p in D.validate(meta, D.schema("note"), "front matter")]
        for ref in meta.get("refs", []) if isinstance(meta.get("refs"), list) else []:
            if not ref_exists(base, ref, added, in_pr):
                problems.append(f"{f}: refs: {ref} does not exist")
        sup = meta.get("supersedes")
        if isinstance(sup, str) and not ref_exists(base, f"note:{sup}", added, in_pr):
            problems.append(f"{f}: supersedes: no note {sup}")
        # Research protocol records (docs/RESEARCH_PROTOCOL.md): untrusted bookkeeping, checked
        # so that the index can rely on their shape.
        tags = meta.get("tags", []) if isinstance(meta.get("tags"), list) else []
        if "research-goal" in tags:
            problems += [f"{f}: {p}" for p in RR.goal_note_problems(f, text)]
        elif RR.GOAL_NOTE.fullmatch(D.classify(f)[1].group(1)):
            problems.append(f"{f}: a note named goal-<fingerprint> must be tagged research-goal")
        if "research-summary" in tags:
            problems += [f"{f}: {p}" for p in RR.summary_note_problems(text)]
    automerge = writer or author in trusted.get("automerge", [])
    return {"ok": not problems, "accepted": True, "automerge": automerge,
            "problems": problems, "added": sorted(added), "revision": revision}


def ref_exists(base: D.Dag, ref: str, added: dict, in_pr: dict) -> bool:
    if base.resolve_ref(ref) is not None:
        return True
    m = D.REF.fullmatch(ref)
    if not m:
        return False
    if m.group(1) == "definition":
        return f"dag/Definitions/Def_{m.group(2)}.lean" in added
    if m.group(1) == "theorem":
        return f"dag/Theorems/Thm_{D.slug(m.group(2))}.lean" in added
    if m.group(3):
        return f"dag/Solutions/{m.group(3)}/Sub_{m.group(4)}.lean" in added
    return f"dag/Notes/{m.group(5)}.md" in added


# -- results and decisions -----------------------------------------------------------------------


def check_result(path: Path) -> dict:
    """The verifier's output, if it has the schema's shape. It came out of the sandbox, so it is
    data from untrusted code: nothing reads more than the schema allows."""
    try:
        r = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise SystemExit(f"no result: {e}")
    if probs := D.validate(r, D.schema("result")):
        raise SystemExit("the result does not have the expected shape:\n" + "\n".join(probs[:20]))
    return r


PASSING = ("OK", "ACCEPTED", "SKETCH_ACCEPTED")


def result_problems(pre: dict, result: dict, env: str | None, revision: str | None,
                    exit_code: int | None) -> list[str]:
    """Why a verifier's result cannot be the gate's verdict: it must come from a verifier that
    exited normally, be about the expected environment and commit, and have exactly one item per
    added node (every added file but metadata)."""
    probs = []
    if revision is None and pre.get("revision") is None:
        probs.append("there is no commit to bind the result to")
    if exit_code not in (0, 1):
        probs.append(f"the verifier exited with {exit_code}")
    if env is not None and result.get("env") != env:
        probs.append(f"the result is about the environment {result.get('env')!r}, not {env!r}")
    if revision is not None and result.get("revision") != revision:
        probs.append(f"the result is about {result.get('revision')!r}, not {revision!r}")
    if pre.get("revision") is not None and result.get("revision") != pre["revision"]:
        probs.append(f"the result is about {result.get('revision')!r}, but the precheck read "
                     f"{pre['revision']!r}")
    expected = sorted(f for f in pre.get("added", []) if not f.endswith(".json"))
    got = [it["path"] for it in result.get("items", [])]
    if sorted(got) != expected:
        missing = sorted(set(expected) - set(got))
        extra = sorted(set(got) - set(expected))
        dups = sorted({p for p in got if got.count(p) > 1})
        probs.append("the result does not cover exactly the added nodes"
                     + (f"; missing {missing}" if missing else "")
                     + (f"; unexpected {extra}" if extra else "")
                     + (f"; repeated {dups}" if dups else ""))
    passed = bool(got) and all(it["status"] in PASSING for it in result.get("items", []))
    if bool(result.get("ok")) != passed:
        probs.append("the result's `ok` contradicts its items")
    if (exit_code == 0) != passed and exit_code in (0, 1):
        probs.append("the verifier's exit status contradicts its items")
    return probs


def decide(pre: dict, result: dict | None, author: str, event: str, env: str | None = None,
           revision: str | None = None, exit_code: int | None = 0) -> dict:
    """The gate's verdict: the check's conclusion, a comment, labels, and whether to merge. The
    conclusion comes from the items' statuses, once the result is shown to be about this pull
    request (`result_problems`)."""
    lines = []
    if not pre.get("accepted"):
        return {"conclusion": "failure", "automerge": False, "labels": ["not-accepted"],
                "comment": "### Not accepted\n\n" + "\n".join(f"- {p}" for p in pre["problems"])}
    if not pre.get("ok"):
        lines.append("### Precheck failed\n")
        lines += [f"- {p}" for p in pre["problems"][:100]]
        return {"conclusion": "failure", "automerge": False,
                "labels": ["rejected"], "comment": "\n".join(lines)}
    if result is None:
        return {"conclusion": "failure", "automerge": False, "labels": [],
                "comment": "### The verifier produced no result\n\nSee the workflow's log."}
    bad = result_problems(pre, result, env, revision, exit_code)
    if bad:
        return {"conclusion": "failure", "automerge": False, "labels": [],
                "comment": "### The verifier's result is not usable\n\n" +
                           "\n".join(f"- {p}" for p in bad)}
    lines.append(f"### Verification in `{result['env']}`" +
                 (f" (std `{result['std']}`)" if result.get("std") else "") + "\n")
    lines.append("| Status | Node | |\n| --- | --- | --- |")
    for it in result["items"]:
        extra = it.get("duplicate_of") or (", ".join(it.get("uses", [])) and
                                           "uses " + ", ".join(it.get("uses", [])))
        if it.get("id"):
            extra = (extra + " " if extra else "") + f"id `{it['id'][:16]}`"
        lines.append(f"| `{it['status']}` | `{it['path']}` | {extra or ''} |")
    for it in result["items"]:
        if it.get("message"):
            msg = it["message"][:3000].replace("```", "'''")
            lines.append(f"\n<details><summary><code>{it['path']}</code></summary>\n\n```\n{msg}\n"
                         "```\n</details>")
    ok = all(it["status"] in PASSING for it in result["items"])
    automerge = ok and pre.get("automerge", False)
    if ok and not automerge:
        lines.append(f"\nPassed. @{author} is not on the automerge list, so a maintainer merges it.")
    return {"conclusion": "success" if ok else "failure", "automerge": automerge,
            "labels": [] if ok and automerge else ["needs-maintainer"] if ok else ["rejected"],
            "comment": "\n".join(lines)}


MANAGED_LABELS = ("not-accepted", "rejected", "needs-maintainer")


def label_changes(current: list[str], wanted: list[str]) -> list[tuple[str, str]]:
    """The edits that make a pull request's gate labels those of the latest decision: add the
    wanted ones it lacks, remove the other gate labels it has; other labels are left alone."""
    ops = [("add", l) for l in wanted if l not in current]
    ops += [("remove", l) for l in current if l in MANAGED_LABELS and l not in wanted]
    return ops


def append_records(result: dict, records: Path, meta: dict, env: str) -> list[dict]:
    """Append a record for every checked node of `result` to `<records>/<env>.jsonl`, with its
    status. The environment is the caller's (the workflow's), and the result must be about it."""
    if not re.fullmatch(D.ENV_ID, env):
        raise SystemExit(f"not an environment id: {env!r}")
    if result.get("env") != env:
        raise SystemExit(f"the result is about {result.get('env')!r}, not {env!r}")
    dest = (records / f"{env}.jsonl").resolve()
    if dest.parent != records.resolve():
        raise SystemExit(f"{dest} is not in {records}")
    # Every checked node is recorded with its status, failures too: they are attempts (the
    # re-verification plan tries the unattempted first); only passing records count anywhere.
    out = []
    for it in result["items"]:
        if it["kind"] == "note":
            continue
        rec = {"kind": it["kind"], "path": it["path"], "name": it.get("name", ""),
               "env": result["env"], "status": it["status"]}
        for k in ("id", "hash", "theorem", "proof_type", "uses", "std"):
            if k in it:
                rec[k] = it[k]
        rec.update({k: v for k, v in meta.items() if v is not None})
        rec["time"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        if probs := D.validate(rec, D.schema("record")):
            raise SystemExit("bad record: " + "; ".join(probs))
        out.append(rec)
    # Idempotent: a retried publication (after a concurrent push) does not repeat a record of the
    # same verification run and node.
    def key(r: dict) -> tuple:
        return (r.get("kind"), r.get("path"), r.get("run") or r.get("commit"), r.get("status"))

    seen = set()
    if dest.exists():
        seen = {key(json.loads(l)) for l in dest.read_text().splitlines() if l.strip()}
    out = [r for r in out if key(r) not in seen]
    if out:
        records.mkdir(parents=True, exist_ok=True)
        with dest.open("a") as f:
            for rec in out:
                f.write(json.dumps(rec, sort_keys=True) + "\n")
    return out


# -- index ---------------------------------------------------------------------------------------

CLAIM = re.compile(r"SigabaNeo\.Claim_[0-9a-f]{16}\.(prove|refute)")


def index(dag: D.Dag, records: dict, core: Path | None = None) -> dict:
    deg = D.in_degrees(dag)
    promotions = dag.read_json("meta/promotions.json", {"promotions": []})["promotions"]
    promoted = {p["node"]: p["std"] for p in promotions}
    nodes = []
    for n in dag.nodes():
        e = {"kind": n.kind, "name": n.name, "path": n.path}
        if n.kind == "note":
            e.update(title=n.meta.get("title"), refs=n.meta.get("refs", []),
                     supersedes=n.meta.get("supersedes"), tags=n.meta.get("tags", []))
        else:
            e.update(title=n.meta.get("title"), tags=n.meta.get("tags", []),
                     in_degree=deg.get(n.module, 0))
            ref = {"definition": f"definition:{n.name}", "theorem": f"theorem:{n.name}"}.get(n.kind)
            if ref in promoted:
                e["promoted_to"] = promoted[ref]
        nodes.append(e)
    superseded = {n["supersedes"]: n["name"] for n in nodes if n.get("supersedes")}
    for n in nodes:
        if n["kind"] == "note" and n["name"] in superseded:
            n["superseded_by"] = superseded[n["name"]]
    envs = {}
    for env in dag.environments():
        if env.get("state") == "frozen":
            continue
        st = D.status(dag, records, env)
        claims = {}
        meta = dag.read_json("meta/assumptions.json", {"claims": {}})["claims"]
        for name, t in st.theorems.items():
            if CLAIM.fullmatch(name):
                claims[name] = {"status": t["status"], **meta.get(name, {}),
                                "sketches": sum(1 for r in st.solutions.values()
                                                if r["theorem"] == name and
                                                r["status"] == "SKETCH_ACCEPTED")}
        envs[env["id"]] = {
            "state": env.get("state"), "std": env.get("std"),
            "counts": {s: sum(1 for t in st.theorems.values() if t["status"] == s)
                       for s in ("Proved", "Disproved", "Open", "Drifted", "Unchecked")},
            "theorems": {n: {**t, "open_leaves": D.open_leaves(st, n)
                             if t["status"] == "Open" and t["solutions"] else []}
                         for n, t in st.theorems.items()},
            "claims": claims, "needs_port": st.needs_port, "stale": st.stale}
    goals = research_goals(dag, nodes, envs)
    candidates = sorted((n for n in nodes if n["kind"] in ("definition", "theorem") and
                         "promoted_to" not in n and n.get("in_degree", 0) > 0),
                        key=lambda n: (-n["in_degree"], n["name"]))[:50]
    out = {"generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
           "environments": envs, "nodes": nodes, "promotions": promotions,
           "std_candidates": [{"name": n["name"], "kind": n["kind"], "in_degree": n["in_degree"]}
                              for n in candidates],
           "goals": goals}
    if core is not None:
        out["std"] = std_summary(core)
    return out


def research_goals(dag: D.Dag, nodes: list[dict], envs: dict) -> list[dict]:
    """The research goals (notes tagged `research-goal` with a valid contract), the statuses of
    their targets per environment, and the summary notes that refer to them."""
    out = []
    for n in dag.by_kind("note"):
        if "research-goal" not in n.meta.get("tags", []) or RR.goal_note_problems(n.path, n.text):
            continue
        goal = RR.one_block(D.front_matter(n.text)[1], "goal")
        fp = RR.goal_fingerprint(goal)
        targets = {}
        for ref in goal["targets"]:
            if ref.startswith("theorem:"):
                name = ref.removeprefix("theorem:")
                targets[ref] = {eid: {"status": e["theorems"].get(name, {}).get("status"),
                                      "open_leaves": e["theorems"].get(name, {})
                                      .get("open_leaves", [])}
                                for eid, e in envs.items()}
        summaries = [m["name"] for m in nodes if m["kind"] == "note" and
                     f"note:{n.name}" in m.get("refs", []) and
                     "research-summary" in m.get("tags", [])]
        out.append({"fingerprint": fp, "note": n.name, "title": goal["title"], "kind": goal["kind"],
                    "objective": goal["objective"], "policy": goal.get("policy", {}),
                    "parent": goal.get("parent"), "definitions": goal["definitions"],
                    "targets": targets, "summaries": sorted(summaries)})
    return sorted(out, key=lambda g: g["note"])


def std_summary(core: Path) -> list[dict]:
    """Each std module and the first line of its module docstring."""
    out = []
    for p in sorted((core / D.STD).rglob("*.lean")):
        text = p.read_text()
        m = re.search(r"/-!?\s*(.*?)(?:\n\s*\n|-/)", text, re.S)
        first = " ".join(m.group(1).split())[:200] if m else ""
        out.append({"module": ".".join(p.relative_to(core).with_suffix("").parts), "doc": first})
    return out


def index_markdown(ix: dict) -> str:
    lines = [f"# DAG index\n\nGenerated {ix['generated']}. Machine-readable: `index.json`.\n"]
    for eid, e in ix["environments"].items():
        c = e["counts"]
        lines.append(f"## Environment `{eid}` ({e['state']}, std `{e['std']}`)\n")
        lines.append(f"{c['Proved']} proved, {c['Disproved']} disproved, {c['Open']} open, "
                     f"{c['Drifted']} drifted, {c['Unchecked']} not yet checked here; "
                     f"{len(e['needs_port'])} solutions need a port, "
                     f"{len(e['stale'])} need re-verification under the current std.\n")
        if e["claims"]:
            lines.append("### Claims\n\n| Card | Status | Tags | Refute sketches |\n|---|---|---|---|")
            for n, cl in sorted(e["claims"].items()):
                lines.append(f"| `{n}` | {cl['status']} | {', '.join(cl.get('tags', []))} | "
                             f"{cl['sketches']} |")
            lines.append("")
        lines.append("### Theorems\n\n| Theorem | Status | Open leaves |\n|---|---|---|")
        for n, t in sorted(e["theorems"].items()):
            lines.append(f"| `{n}` | {t['status']} | {', '.join(f'`{x}`' for x in t['open_leaves'])} |")
        if e["needs_port"]:
            lines.append("\n### Needs port\n")
            lines += [f"- `{p}`" for p in e["needs_port"]]
        lines.append("")
    if ix.get("goals"):
        lines.append("## Research goals\n")
        for g in ix["goals"]:
            lines.append(f"### {g['title']}\n\n`{g['note']}` ({g['kind']}, objective "
                         f"`{g['objective']['kind']}`). Policy (not Lean-verified): "
                         f"{', '.join(g['policy'].get('forbidden_routes', [])) or 'none'}.\n")
            for ref, per_env in g["targets"].items():
                for eid, t in per_env.items():
                    leaves = ", ".join(f"`{x}`" for x in t["open_leaves"])
                    lines.append(f"- `{ref}` in `{eid}`: {t['status']}"
                                 + (f"; open leaves {leaves}" if leaves else ""))
            if g["summaries"]:
                lines.append("- task summaries: " + ", ".join(f"`{x}`" for x in g["summaries"]))
            lines.append("")
    notes = [n for n in ix["nodes"] if n["kind"] == "note" and "superseded_by" not in n]
    if notes:
        lines.append("## Notes\n")
        lines += [f"- `{n['name']}`: {n.get('title') or ''}" for n in notes]
        lines.append("")
    if ix["std_candidates"]:
        lines.append("## Candidates for std (most imported)\n")
        lines += [f"- `{c['name']}` ({c['kind']}, imported {c['in_degree']}×)"
                  for c in ix["std_candidates"]]
    return "\n".join(lines) + "\n"


def reverify_plan(dag: D.Dag, records: dict, env_id: str) -> list[str]:
    """The nodes to check in `env_id`: theorems and definitions without an ID there and solutions
    without a counting record there. Those never tried there come first (definitions and theorems,
    then the solutions of the most imported theorems); those whose last try failed come after,
    least recently tried first, so that failing nodes never keep the others from their turn."""
    env = dag.environment(env_id)
    if env is None:
        raise SystemExit(f"no environment {env_id}")
    st = D.status(dag, records, env)
    recs = records.get(env_id, [])
    have = {r["path"] for r in recs if D.id_record(r)}
    tried: dict[str, str] = {}
    for r in recs:
        tried[r["path"]] = max(tried.get(r["path"], ""), r.get("time") or "")
    deg = D.in_degrees(dag)
    nodes = [n for n in dag.nodes() if n.kind in ("definition", "theorem") and n.path not in have]
    sols = [n for n in dag.by_kind("solution") if n.path not in st.solutions]
    thm_deg = lambda n: -deg.get(f"Theorems.Thm_{n.path.split('/')[2]}", 0)  # noqa: E731
    todo = [n.path for n in nodes] + \
        [n.path for n in sorted(sols, key=lambda n: (thm_deg(n), n.path))]
    fresh = [p for p in todo if p not in tried]
    retries = sorted((p for p in todo if p in tried), key=lambda p: (tried[p], todo.index(p)))
    return fresh + retries


# -- maintainers ---------------------------------------------------------------------------------


def std_release(dag_dir: Path, tag: str, core: Path) -> dict:
    p = dag_dir / "env" / "std.json"
    data = json.loads(p.read_text()) if p.exists() else {"releases": {}}
    data["releases"][tag] = D.std_manifest(core)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    return data


def render(text: str, values: dict) -> str:
    for k, v in values.items():
        text = text.replace("{{" + k + "}}", v)
    return text


def init(d: Path, core_url: str, core_rev: str, image: str, owner: str, env_id: str,
         core_path: Path | None = None, core: Path = D.CORE) -> None:
    """A new DAG repository at `d`."""
    if (d / "dag").exists():
        raise SystemExit(f"{d} already has a DAG")
    # Lake writes names that are not identifiers in guillemets (`«cslib-frontier»`).
    pins = {p["name"].strip("«»"): p["rev"] for p in
            json.loads((core / "lake-manifest.json").read_text())["packages"]
            if p.get("type") == "git"}
    if missing := [n for n in ("mathlib", "cslib-frontier") if not pins.get(n)]:
        raise SystemExit(f"the core's lake-manifest.json does not pin {', '.join(missing)}")
    toolchain = (core / "lean-toolchain").read_text().strip()
    repo = re.sub(r"^https://github\.com/|\.git$", "", core_url)
    values = {"CORE_URL": core_url, "CORE_REPO": repo, "CORE_REV": core_rev, "OWNER": owner,
              "IMAGE": image, "ENV_ID": env_id}
    for src in sorted(TEMPLATES.rglob("*")):
        if src.is_file():
            dst = d / src.relative_to(TEMPLATES)
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(render(src.read_text(), values))
    require = (f'path = {json.dumps(str(core_path))}' if core_path else
               f'git = {json.dumps(core_url)}\nrev = {json.dumps(core_rev)}')
    (d / "lakefile.toml").write_text(
        'name = "dag"\nsrcDir = "dag"\nleanOptions = { autoImplicit = false }\n\n'
        f'[[require]]\nname = "SigabaNeo"\n{require}\n\n'
        '[[lean_lib]]\nname = "Definitions"\n\n[[lean_lib]]\nname = "Theorems"\n\n'
        '[[lean_lib]]\nname = "Solutions"\n')
    (d / "lean-toolchain").write_text(toolchain + "\n")
    for sub in ("Definitions", "Theorems", "Solutions", "Notes"):
        (d / "dag" / sub).mkdir(parents=True, exist_ok=True)
        (d / "dag" / sub / ".gitkeep").write_text("")
    env = {"id": env_id, "lean": toolchain, "mathlib": pins.get("mathlib", ""),
           "cslib_frontier": pins.get("cslib-frontier", ""), "core": core_rev,
           "core_url": core_url, "image": image, "fingerprint": D.text_fingerprint(core),
           "std": core_rev, "state": "default"}
    (d / "env").mkdir(exist_ok=True)
    (d / "env" / "environments.json").write_text(json.dumps({"environments": [env]}, indent=1)
                                                 + "\n")
    std_release(d, core_rev, core)
    (d / "meta").mkdir(exist_ok=True)
    (d / "meta" / "trusted.json").write_text(json.dumps(
        {"mode": "allowlist", "accept": [owner], "automerge": [owner]}, indent=1) + "\n")
    (d / "meta" / "assumptions.json").write_text('{"claims": {}}\n')
    (d / "meta" / "promotions.json").write_text('{"promotions": []}\n')


def write_node(out: Path, path: str, text: str, meta: dict | None) -> None:
    p = out / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    if meta is not None:
        p.with_suffix(".json").write_text(json.dumps(meta, indent=1, ensure_ascii=False) + "\n")


def import_server(data_dir: Path, out: Path) -> dict:
    """The definitions, theorems and accepted solutions of the retired server's database, written
    as DAG files (and the operator's claim metadata as `meta/assumptions.json`)."""
    db = sqlite3.connect(data_dir / "platform.sqlite")
    db.row_factory = sqlite3.Row
    counts = {"definition": 0, "theorem": 0, "solution": 0}
    for d in db.execute("SELECT * FROM definitions WHERE deprecated_at IS NULL"):
        meta = {"name": d["name"], "title": d["title"] or d["name"]}
        if d["nl"]:
            meta["description"] = d["nl"]
        if d["source"]:
            meta["source"] = d["source"]
        if json.loads(d["tags"] or "[]"):
            meta["tags"] = [t for t in json.loads(d["tags"]) if re.fullmatch(r"[a-z0-9][a-z0-9-]*", t)]
        write_node(out, f"dag/Definitions/Def_{d['name']}.lean", d["code"], meta)
        counts["definition"] += 1
    thms = {}
    for t in db.execute("SELECT * FROM theorems WHERE deprecated_at IS NULL"):
        thms[t["id"]] = t
        meta = {"name": t["name"], "title": t["title"] or t["name"]}
        if t["nl"]:
            meta["statement"] = t["nl"]
        if t["source"]:
            meta["source"] = t["source"]
        tags = [x for x in json.loads(t["tags"] or "[]") if re.fullmatch(r"[a-z0-9][a-z0-9-]*", x)]
        if tags:
            meta["tags"] = tags
        text = (t["preamble"] or "").rstrip() + "\n\n" + t["statement"].strip() + "\n"
        write_node(out, f"dag/Theorems/Thm_{t['slug']}.lean", text, meta)
        counts["theorem"] += 1
    for s in db.execute("SELECT * FROM submissions WHERE status IN ('ACCEPTED','SKETCH_ACCEPTED') "
                        "AND deprecated_at IS NULL ORDER BY created_at"):
        t = thms.get(s["theorem_id"])
        if t is None:
            continue
        sid = s["id"].replace("-", "")[:16]
        meta = {"theorem": t["name"], "proof_type": s["proof_type"]}
        if s["explanation"]:
            meta["explanation"] = s["explanation"]
        write_node(out, f"dag/Solutions/{t['slug']}/Sub_{sid}.lean", s["content"], meta)
        counts["solution"] += 1
    claims = {}
    try:
        for m in db.execute("SELECT * FROM assumption_meta"):
            t = thms.get(m["theorem_id"])
            if t is not None:
                c = {"tags": json.loads(m["tags"] or "[]")}
                if m["proposed_year"]:
                    c["proposed_year"] = m["proposed_year"]
                if m["source"]:
                    c["source"] = m["source"]
                claims[t["name"]] = c
    except sqlite3.OperationalError:
        pass
    if claims:
        (out / "meta").mkdir(parents=True, exist_ok=True)
        (out / "meta" / "assumptions.json").write_text(json.dumps({"claims": claims}, indent=1)
                                                       + "\n")
    return counts


def flatten_namespace(preamble: str, statement: str, name: str) -> tuple[str, str] | None:
    """A theorem file whose statement sits in `namespace X … end X`, as the DAG wants it: the
    statement last, ending in `:= by sorry`, with the theorem's full name (declaring `X.t` resolves
    names in `X` as the namespace did). None if it cannot be put in that form."""
    stmt = statement.rstrip()
    ends = []
    while (m := re.search(r"\n\s*end\s+([A-Za-z_][\w.']*)\s*$", stmt)):
        ends.append(m.group(1))
        stmt = stmt[: m.start()].rstrip()
    if not stmt.endswith(":= by sorry"):
        return None
    pre = preamble
    for ns in ends:
        m = re.search(rf"^namespace\s+{re.escape(ns)}\s*$", pre, re.M)
        if m is None:
            return None
        pre = pre[: m.start()] + pre[m.end():]
    ns = ".".join(reversed(ends))
    if ns:
        short = name[len(ns) + 1:] if name.startswith(ns + ".") else None
        m = re.match(r"(theorem|lemma)\s+(\S+)", stmt)
        if short is None or m is None or m.group(2) != short:
            return None
        stmt = f"theorem {name}" + stmt[m.end():]
    return re.sub(r"\n{3,}", "\n\n", pre).rstrip() + "\n", stmt + "\n"


def formalpedia_items(dag: D.Dag, out: Path, mirror_dir: Path, env: str | None,
                      match: str | None, limit: int | None, url: str | None = None) -> dict:
    """Formalpedia's definitions and theorems not yet in the DAG (by name), with their accepted
    solutions, written under `out` as DAG files that record their source. Each one goes through
    the gate like any pull request: nothing is taken on trust."""
    import formalpedia
    mirror = formalpedia.Mirror(url or formalpedia.URL, mirror_dir)
    rev = mirror.update()
    env = env or mirror.default_env(rev)
    files = mirror.files(rev, env)
    pattern = re.compile(match) if match else None
    have_sources = {n.meta.get("source") for n in dag.nodes() if n.meta.get("source")}
    counts = {"definition": 0, "theorem": 0, "solution": 0, "skipped": 0}
    written: set[str] = set()

    def src(path: str) -> str:
        return f"formalpedia:{env}:{path}@{files[path]}"

    def module_path(module: str) -> str | None:
        top, _, rest = module.partition(".")
        if top not in ("Definitions", "Theorems") or "." in rest:
            return None
        return f"envs/{env}/{top}/{rest}.lean"

    def add(path: str, budget: list[int]) -> bool:
        if path in written:
            return True
        if path not in files or src(path) in have_sources:
            return True
        item = formalpedia.parse(path, mirror.read(files[path]))
        for m in item.imports:
            dep = module_path(m)
            target = D.path_of(m) if m.startswith(("Definitions.", "Theorems.")) else None
            if dep and target and not (dag.root / target).exists() and not (out / target).exists():
                if not add(dep, budget):
                    counts["skipped"] += 1
                    return False
        if item.kind == "definition":
            if not re.fullmatch(D.DEF_NAME, item.name) or dag.definition(item.name):
                counts["skipped"] += 1
                return False
            write_node(out, f"dag/Definitions/Def_{item.name}.lean", item.body,
                       {"name": item.name, "title": (item.header.get("title") or item.name)[:200],
                        "source": src(path)})
        else:
            split = item.split_statement()
            if split is not None:
                split = flatten_namespace(*split, item.name)
            if split is None or not re.fullmatch(D.THM_NAME, item.name) or dag.theorem(item.name):
                counts["skipped"] += 1
                return False
            meta = {"name": item.name, "title": (item.header.get("title") or item.name)[:200],
                    "source": src(path)}
            if item.header.get("statement"):
                meta["statement"] = item.header["statement"][:20000]
            write_node(out, f"dag/Theorems/Thm_{D.slug(item.name)}.lean",
                       split[0].rstrip() + "\n\n" + split[1], meta)
        written.add(path)
        counts[item.kind] += 1
        budget[0] -= 1
        return True

    budget = [limit if limit is not None else 10 ** 9]
    for path in sorted(files):
        if budget[0] <= 0:
            break
        if "/Solutions/" in path or (pattern and not pattern.search(path)):
            continue
        add(path, budget)
    synced = {D.slug(formalpedia.parse(p, mirror.read(files[p])).name)
              for p in written if "/Theorems/" in p}
    for path in sorted(files):
        if "/Solutions/" not in path:
            continue
        stem = path.rsplit("/", 1)[1][len("Sol_"):-len(".lean")]
        s = stem if stem in synced else re.sub(r"_\d+$", "", stem)
        if s not in synced:
            continue
        item = formalpedia.parse(path, mirror.read(files[path]))
        if item.header.get("status") not in ("ACCEPTED", "SKETCH_ACCEPTED"):
            continue
        sid = files[path][:16]
        write_node(out, f"dag/Solutions/{s}/Sub_{sid}.lean", item.body,
                   {"theorem": item.name, "proof_type": item.header.get("proof_type", "prove"),
                    "source": src(path)})
        counts["solution"] += 1
    return {"commit": rev, "env": env, **counts}


# -- command line --------------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="action", required=True)
    f = sub.add_parser("fetch")
    f.add_argument("--repo", required=True)
    f.add_argument("--base", required=True, help="the event's base commit")
    f.add_argument("--head", required=True, help="the event's head commit")
    f.add_argument("--out", type=Path, required=True)
    p = sub.add_parser("precheck")
    p.add_argument("--dag", type=Path, required=True)
    p.add_argument("--fetched", type=Path, required=True, help="the output of `fetch`")
    p.add_argument("--author", required=True)
    p.add_argument("--permission", help="the author's permission on the repository (GitHub's "
                   "`admin`, `write`, `read` or `none`), for the `collaborators` mode")
    p.add_argument("--out", type=Path, required=True)
    c = sub.add_parser("check-result")
    c.add_argument("result", type=Path)
    d = sub.add_parser("decide")
    d.add_argument("--precheck", type=Path, required=True)
    d.add_argument("--result", type=Path)
    d.add_argument("--author", required=True)
    d.add_argument("--event", default="pull_request_target")
    d.add_argument("--env", help="the environment the gate verified in")
    d.add_argument("--revision", help="the commit the gate verified")
    d.add_argument("--exit-code", type=Path, help="a file with the verifier's exit status")
    d.add_argument("--out", type=Path, required=True)
    lb = sub.add_parser("labels", help="the label edits for a decision (`add L` / `remove L`)")
    lb.add_argument("--decision", type=Path, required=True)
    lb.add_argument("--current", required=True, help="the pull request's labels, a JSON list")
    r = sub.add_parser("records")
    r.add_argument("--result", type=Path, required=True)
    r.add_argument("--records", type=Path, required=True)
    r.add_argument("--env", required=True, help="the environment, from the workflow")
    r.add_argument("--author")
    r.add_argument("--pr", type=int)
    r.add_argument("--commit")
    r.add_argument("--run")
    i = sub.add_parser("index")
    i.add_argument("--dag", type=Path, required=True)
    i.add_argument("--records", type=Path)
    i.add_argument("--out", type=Path, required=True)
    i.add_argument("--core", type=Path)
    rp = sub.add_parser("reverify-plan")
    rp.add_argument("--dag", type=Path, required=True)
    rp.add_argument("--records", type=Path)
    rp.add_argument("--env", required=True)
    rp.add_argument("--limit", type=int, default=200)
    rp.add_argument("--out", type=Path, required=True)
    s = sub.add_parser("std-manifest")
    s.add_argument("--dag", type=Path, required=True)
    s.add_argument("--tag", required=True)
    s.add_argument("--core", type=Path, default=D.CORE)
    n = sub.add_parser("init")
    n.add_argument("dir", type=Path)
    n.add_argument("--core-url", required=True)
    n.add_argument("--core-rev", required=True)
    n.add_argument("--image", required=True, help="the environment image, pinned by digest")
    n.add_argument("--owner", required=True, help="the maintainers' GitHub login or team")
    n.add_argument("--env-id", default="env-1")
    n.add_argument("--core-path", type=Path, help="require the core by path (local testing)")
    m = sub.add_parser("import-server")
    m.add_argument("data_dir", type=Path)
    m.add_argument("--out", type=Path, required=True)
    fp = sub.add_parser("formalpedia")
    fp.add_argument("--dag", type=Path, required=True)
    fp.add_argument("--out", type=Path, required=True)
    fp.add_argument("--mirror", type=Path, default=Path("formalpedia-mirror"))
    fp.add_argument("--url")
    fp.add_argument("--env")
    fp.add_argument("--match")
    fp.add_argument("--limit", type=int)
    a = ap.parse_args(argv)

    if a.action == "fetch":
        rows = fetch(a.repo, a.out, os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN"),
                     a.base, a.head)
        print(f"{len(rows)} changed files")
    elif a.action == "precheck":
        fetched = json.loads((a.fetched / "files.json").read_text())
        out = precheck(D.Dag(a.dag), fetched["files"], a.fetched / "files", a.author,
                       fetched.get("revision"), a.permission)
        a.out.write_text(json.dumps(out, indent=1) + "\n")
        for line in out["problems"]:
            print(line)
        print("precheck:", "ok" if out["ok"] else "failed")
        if gh := os.environ.get("GITHUB_OUTPUT"):
            with open(gh, "a") as g:
                g.write(f"ok={'true' if out['ok'] else 'false'}\nrevision={out['revision'] or ''}\n")
    elif a.action == "check-result":
        check_result(a.result)
        print("the result has the expected shape")
    elif a.action == "decide":
        pre = json.loads(a.precheck.read_text())
        res = check_result(a.result) if a.result and a.result.exists() else None
        code = None
        if a.exit_code is not None:
            try:
                code = int(a.exit_code.read_text().strip())
            except (OSError, ValueError):
                code = None
        out = decide(pre, res, a.author, a.event, a.env or None, a.revision or None,
                     code if a.exit_code is not None else 0)
        a.out.write_text(json.dumps(out, indent=1) + "\n")
        print(out["comment"])
        return 0 if out["conclusion"] == "success" else 1
    elif a.action == "labels":
        wanted = json.loads(a.decision.read_text())["labels"]
        current = json.loads(a.current or "[]")
        for op, label in label_changes([str(c) for c in current], wanted):
            print(op, label)
    elif a.action == "records":
        res = check_result(a.result)
        recs = append_records(res, a.records, {"author": a.author, "pr": a.pr,
                                               "commit": a.commit, "run": a.run}, a.env)
        print(f"{len(recs)} records appended to {res['env']}.jsonl")
    elif a.action == "index":
        ix = index(D.Dag(a.dag), D.read_records(a.records), a.core)
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / "index.json").write_text(json.dumps(ix, indent=1) + "\n")
        (a.out / "INDEX.md").write_text(index_markdown(ix))
        print(f"{len(ix['nodes'])} nodes indexed")
    elif a.action == "reverify-plan":
        plan = reverify_plan(D.Dag(a.dag), D.read_records(a.records), a.env)[: a.limit]
        a.out.write_text(json.dumps(plan, indent=1) + "\n")
        print(f"{len(plan)} nodes to check again in {a.env}")
    elif a.action == "std-manifest":
        data = std_release(a.dag, a.tag, a.core.resolve())
        print(f"{len(data['releases'][a.tag])} std modules in release {a.tag}")
    elif a.action == "init":
        init(a.dir, a.core_url, a.core_rev, a.image, a.owner, a.env_id,
             a.core_path.resolve() if a.core_path else None)
        print(f"{a.dir}: a new DAG repository (apply the GitHub settings of the core's "
              "docs/GITHUB_PLATFORM.md, section 10)")
    elif a.action == "import-server":
        print(json.dumps(import_server(a.data_dir, a.out)))
    elif a.action == "formalpedia":
        print(json.dumps(formalpedia_items(D.Dag(a.dag), a.out, a.mirror, a.env, a.match,
                                           a.limit, a.url)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
