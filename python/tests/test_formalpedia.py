"""Syncing Formalpedia into the compatible server, from a small local export in its layout.

    python3 -m unittest discover -s python/tests -p 'test_formalpedia.py' -v
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

import common  # noqa: F401  (puts python/ on the path)
import formalpedia
from p2m_server import CORE, Core, Platform, PlatformConfig

HEADER = "-- Prove2me | {module}\n-- name    : {name}\n-- status  : {status}\n" \
         "-- url     : https://prove2.me/theorems/x\n-- title:\n--   {title}\n-- statement:\n" \
         "--   A test item.\n--\n--   Second paragraph.\n\n"

DEF = HEADER.format(module="Definitions.Def_FpDef", name="FpDef", status="Definition",
                    title="two") + "namespace FpTest\n\ndef two : Nat := 2\n\nend FpTest\n"
THM = HEADER.format(module="Theorems.Thm_FpTest_two_eq", name="FpTest.two_eq", status="Proved",
                    title="two is two") + \
    "import Definitions.Def_FpDef\n\nnamespace FpTest\n\ntheorem two_eq : two = 2 := by sorry\n\nend FpTest\n"
SOL = "-- Prove2me | solution 1 for FpTest.two_eq\n-- status  : ACCEPTED   (prove)\n" \
      "-- author  : @someone\n\nimport Definitions.Def_FpDef\n\ntheorem solution : FpTest.two = 2 := rfl\n"
THM2 = HEADER.format(module="Theorems.Thm_FpTest_two_pos", name="FpTest.two_pos", status="Open",
                     title="two is positive") + \
    "import Definitions.Def_FpDef\n\ntheorem FpTest.two_pos : 0 < FpTest.two := by sorry\n"


def git(d: Path, *args: str) -> None:
    subprocess.run(["git", "-C", str(d), *args], check=True, capture_output=True)


def write(repo: Path, files: dict[str, str]) -> None:
    for rel, text in files.items():
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text)
    git(repo, "add", "-A")
    git(repo, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "snapshot")


class ParseTest(unittest.TestCase):
    def test_parse(self):
        t = formalpedia.parse("envs/e/Theorems/Thm_FpTest_two_eq.lean", THM)
        self.assertEqual((t.kind, t.name, t.header["title"]), ("theorem", "FpTest.two_eq", "two is two"))
        self.assertEqual(t.header["statement"], "A test item.\n\nSecond paragraph.")
        self.assertEqual(t.imports, ["Definitions.Def_FpDef"])
        pre, stmt = t.split_statement()
        self.assertTrue(pre.startswith("import Definitions.Def_FpDef\n\nnamespace FpTest"))
        self.assertTrue(stmt.startswith("theorem two_eq : two = 2 := by sorry"))
        s = formalpedia.parse("envs/e/Solutions/Sol_FpTest_two_eq.lean", SOL)
        self.assertEqual((s.kind, s.name, s.header["status"], s.header["proof_type"]),
                         ("solution", "FpTest.two_eq", "ACCEPTED", "prove"))
        self.assertTrue(s.body.startswith("import Definitions.Def_FpDef"))


class SyncTest(unittest.TestCase):
    def test_sync(self):
        tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-formalpedia-"))
        pf = Platform(PlatformConfig(tmp / "data", Core(CORE), {}))
        pf.start()
        try:
            repo = tmp / "export"
            repo.mkdir()
            git(repo, "init", "-q")
            git(repo, "config", "uploadpack.allowFilter", "true")
            write(repo, {"MANIFEST.json": json.dumps({"environments": [{"dir": "e", "is_default": True}]}),
                         "envs/e/Definitions/Def_FpDef.lean": DEF,
                         "envs/e/Theorems/Thm_FpTest_two_eq.lean": THM,
                         "envs/e/Solutions/Sol_FpTest_two_eq.lean": SOL})
            url = repo.as_uri()

            def sync() -> dict:
                r = pf.sync_formalpedia(url)
                while pf.busy():
                    time.sleep(1)
                return r

            r = sync()
            self.assertEqual((r["env"], r["changed"]), ("e", 3))
            self.assertEqual(r["queued"], {"definition": 1, "theorem": 1, "solution": 1, "skipped": 0})
            t = pf.row("SELECT * FROM theorems WHERE name = 'FpTest.two_eq'")
            self.assertIsNotNone(t, pf.formalpedia_status())
            self.assertEqual(t["status"], "Proved", pf.formalpedia_status())
            self.assertEqual(json.loads(t["tags"]), ["formalpedia"])
            self.assertEqual(set(pf.formalpedia_status().values()), {"PUBLISHED", "ACCEPTED"})

            # Nothing changed: nothing to do. A new theorem: only it.
            self.assertEqual(sync()["changed"], 0)
            write(repo, {"envs/e/Theorems/Thm_FpTest_two_pos.lean": THM2})
            r = sync()
            self.assertEqual((r["changed"], r["queued"]["theorem"], r["queued"]["definition"]), (1, 1, 0))
            self.assertEqual(pf.row("SELECT status FROM theorems WHERE name = 'FpTest.two_pos'")["status"],
                             "Open")
        finally:
            pf.stop.set()
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
