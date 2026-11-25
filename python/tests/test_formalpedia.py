"""Formalpedia's items as DAG nodes (`dag_tools.py formalpedia`), from a small local export in its
layout, checked by the verifier like any pull request.

    python3 -m unittest discover -s python/tests -p 'test_formalpedia.py' -v
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import common  # noqa: F401  (puts python/ on the path)
import dag as D
import dag_tools as T
import dag_verify as V
import formalpedia

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


class ConvertTest(unittest.TestCase):
    def test_convert_and_verify(self):
        tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-formalpedia-"))
        try:
            repo = tmp / "export"
            repo.mkdir()
            git(repo, "init", "-q")
            git(repo, "config", "uploadpack.allowFilter", "true")
            write(repo, {"MANIFEST.json": json.dumps({"environments": [{"dir": "e", "is_default": True}]}),
                         "envs/e/Definitions/Def_FpDef.lean": DEF,
                         "envs/e/Theorems/Thm_FpTest_two_eq.lean": THM,
                         "envs/e/Solutions/Sol_FpTest_two_eq.lean": SOL})
            base = tmp / "base"
            base.mkdir()
            out = tmp / "new"
            r = T.formalpedia_items(D.Dag(base), out, tmp / "mirror", None, None, None,
                                    url=repo.as_uri())
            self.assertEqual((r["env"], r["definition"], r["theorem"], r["solution"]), ("e", 1, 1, 1))
            nodes = {n.path: n for n in D.Dag(out).nodes()}
            self.assertEqual(len(nodes), 3)
            self.assertIn("dag/Definitions/Def_FpDef.lean", nodes)
            self.assertIn("dag/Theorems/Thm_FpTest_two_eq.lean", nodes)
            self.assertEqual(len([p for p in nodes if p.startswith("dag/Solutions/FpTest_two_eq/Sub_")]), 1)
            stmt = nodes["dag/Theorems/Thm_FpTest_two_eq.lean"].text
            self.assertTrue(stmt.rstrip().endswith("theorem FpTest.two_eq : two = 2 := by sorry"), stmt)
            for n in nodes.values():
                self.assertTrue(n.meta["source"].startswith("formalpedia:e:envs/e/"))

            # The gate's checks, as for any pull request.
            res = V.verify(base, out, None, None, tmp / "work")
            self.assertEqual({i["path"]: i["status"] for i in res["items"]},
                             {p: "ACCEPTED" if "/Solutions/" in p else "OK" for p in nodes},
                             json.dumps(res, indent=1))

            # Once merged, nothing is converted again; a new theorem alone is.
            shutil.copytree(out / "dag", base / "dag")
            write(repo, {"envs/e/Theorems/Thm_FpTest_two_pos.lean": THM2})
            out2 = tmp / "new2"
            r = T.formalpedia_items(D.Dag(base), out2, tmp / "mirror", None, None, None,
                                    url=repo.as_uri())
            self.assertEqual((r["definition"], r["theorem"]), (0, 1))
            self.assertEqual([n.name for n in D.Dag(out2).nodes()], ["FpTest.two_pos"])
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
