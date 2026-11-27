"""Git and GitHub for the controller (docs/RESEARCH_PROTOCOL.md, sections 5 and 8). Every call
goes through `Runner`, with argument lists (never a shell), so the tests replace GitHub with a fake
(`FakeGitHub`) and keep real Git on local repositories."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path


class RemoteError(Exception):
    """A failed Git or GitHub call. `kind`: `network`, `permission` or `protocol`."""

    def __init__(self, msg: str, kind: str = "network"):
        super().__init__(msg)
        self.kind = kind


def run(argv: list[str], cwd: Path | None = None, input: str | None = None,
        env: dict | None = None, check: bool = True) -> str:
    p = subprocess.run(argv, cwd=cwd, input=input, capture_output=True, text=True, env=env)
    if check and p.returncode != 0:
        err = (p.stderr or p.stdout).strip()
        kind = "permission" if any(w in err for w in ("403", "Permission", "permission denied",
                                                     "not authorized")) else "network"
        raise RemoteError(f"{' '.join(argv[:3])}: {err[-2000:]}", kind)
    return p.stdout


class Git:
    """Git on a local clone or worktree."""

    def __init__(self, root: Path):
        self.root = Path(root)

    def __call__(self, *args: str, input: str | None = None, env: dict | None = None,
                 check: bool = True) -> str:
        return run(["git", "-C", str(self.root), *args], input=input, env=env, check=check)

    def head(self) -> str:
        return self("rev-parse", "HEAD").strip()


class GitHub:
    """GitHub through `gh`. `repo` is `owner/name`."""

    def __init__(self, repo: str):
        self.repo = repo

    def gh(self, *args: str, input: str | None = None) -> str:
        return run(["gh", *args], input=input)

    def api(self, path: str, method: str = "GET", body: dict | None = None,
            paginate: bool = False):
        args = ["api", path, "-X", method]
        if paginate:      # one compact JSON item per line, across pages
            args += ["--paginate", "--jq", ".[]"]
        if body is not None:
            args += ["--input", "-"]
        out = self.gh(*args, input=json.dumps(body) if body is not None else None)
        if paginate:
            return [json.loads(line) for line in out.splitlines() if line.strip()]
        return json.loads(out) if out.strip() else None

    # -- identity --------------------------------------------------------------------------------
    def login(self) -> str:
        return self.api("user")["login"]

    def can_push(self) -> bool:
        return bool(self.api(f"repos/{self.repo}").get("permissions", {}).get("push"))

    def ensure_fork(self) -> str:
        """The user's fork (created if missing), as `owner/name`."""
        self.gh("repo", "fork", self.repo, "--clone=false")
        return f"{self.login()}/{self.repo.split('/')[1]}"

    # -- pull requests ---------------------------------------------------------------------------
    PR_FIELDS = "number,url,state,isDraft,headRefName,headRefOid,author,title,body,mergedAt"

    def list_prs(self, state: str = "all", limit: int = 1000) -> list[dict]:
        return json.loads(self.gh("pr", "list", "-R", self.repo, "--state", state, "--limit",
                                  str(limit), "--json", self.PR_FIELDS))

    def find_pr(self, branch: str) -> dict | None:
        prs = json.loads(self.gh("pr", "list", "-R", self.repo, "--state", "all", "--head",
                                 branch, "--json", self.PR_FIELDS))
        return prs[0] if prs else None

    def view_pr(self, number: int) -> dict:
        return json.loads(self.gh("pr", "view", str(number), "-R", self.repo, "--json",
                                  self.PR_FIELDS))

    def create_pr(self, head: str, title: str, body: str, draft: bool) -> dict:
        args = ["pr", "create", "-R", self.repo, "--base", "main", "--head", head,
                "--title", title, "--body-file", "-"]
        if draft:
            args.append("--draft")
        url = self.gh(*args, input=body).strip().splitlines()[-1]
        return self.view_pr(int(url.rstrip("/").rsplit("/", 1)[1]))

    def ready(self, number: int) -> None:
        self.gh("pr", "ready", str(number), "-R", self.repo)

    def to_draft(self, number: int) -> None:
        self.gh("pr", "ready", str(number), "-R", self.repo, "--undo")

    def close(self, number: int, comment: str) -> None:
        self.gh("pr", "close", str(number), "-R", self.repo, "--comment", comment)

    def comments(self, number: int) -> list[dict]:
        return self.api(f"repos/{self.repo}/issues/{number}/comments?per_page=100",
                        paginate=True) or []

    def comment(self, number: int, body: str) -> dict:
        return self.api(f"repos/{self.repo}/issues/{number}/comments", "POST", {"body": body})

    def edit_comment(self, comment_id: int, body: str) -> dict:
        return self.api(f"repos/{self.repo}/issues/comments/{comment_id}", "PATCH",
                        {"body": body})

    def pr_files(self, number: int) -> list[dict]:
        return self.api(f"repos/{self.repo}/pulls/{number}/files?per_page=100",
                        paginate=True) or []

    def blob(self, sha: str) -> bytes:
        import base64
        d = self.api(f"repos/{self.repo}/git/blobs/{sha}")
        return base64.b64decode(d["content"])


class FakeGitHub:
    """GitHub in memory, for the tests: pull requests, comments, files and blobs. `fail` makes the
    next N write calls raise a network error."""

    def __init__(self, repo: str, login: str = "alice", push: bool = True):
        self.repo, self._login, self.push = repo, login, push
        self.prs: dict[int, dict] = {}
        self._comments: dict[int, list[dict]] = {}
        self.files: dict[int, list[dict]] = {}
        self.blobs: dict[str, bytes] = {}
        self.next_id = 1000
        self.fail = 0
        self.calls: list[str] = []

    def _write(self, what: str):
        self.calls.append(what)
        if self.fail:
            self.fail -= 1
            raise RemoteError(f"{what}: simulated network failure")

    def login(self):
        return self._login

    def can_push(self):
        return self.push

    def ensure_fork(self):
        return f"{self._login}/{self.repo.split('/')[1]}"

    def list_prs(self, state="all", limit=1000):
        return [dict(p) for p in self.prs.values()]

    def find_pr(self, branch):
        return next((dict(p) for p in self.prs.values() if p["headRefName"] == branch), None)

    def view_pr(self, number):
        return dict(self.prs[number])

    def create_pr(self, head, title, body, draft):
        self._write("create_pr")
        n = len(self.prs) + 1
        self.prs[n] = {"number": n, "url": f"https://github.com/{self.repo}/pull/{n}",
                       "state": "OPEN", "isDraft": draft, "headRefName": head.split(":")[-1],
                       "headRefOid": None, "author": {"login": self._login}, "title": title,
                       "body": body, "mergedAt": None}
        self._comments[n] = []
        return dict(self.prs[n])

    def ready(self, number):
        self._write("ready")
        self.prs[number]["isDraft"] = False

    def to_draft(self, number):
        self._write("to_draft")
        self.prs[number]["isDraft"] = True

    def close(self, number, comment):
        self._write("close")
        self.comment(number, comment)
        self.prs[number]["state"] = "CLOSED"

    def comments(self, number):
        return [dict(c) for c in self._comments.get(number, [])]

    def comment(self, number, body):
        self._write("comment")
        self.next_id += 1
        c = {"id": self.next_id, "body": body, "user": {"login": self._login},
             "created_at": "2026-01-01T00:00:00Z"}
        self._comments.setdefault(number, []).append(c)
        return dict(c)

    def edit_comment(self, comment_id, body):
        self._write("edit_comment")
        for cs in self._comments.values():
            for c in cs:
                if c["id"] == comment_id:
                    c["body"] = body
                    return dict(c)
        raise RemoteError("no such comment", "protocol")

    def pr_files(self, number):
        return list(self.files.get(number, []))

    def blob(self, sha):
        return self.blobs[sha]
