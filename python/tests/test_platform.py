"""The std build: every std module has build outputs. The platform's check of forbidden
declarations (`SigabaNeo.Platform.forbidden`) on a compiled module: the compiler code Lean
generates for recursion and inductive types is allowed, the same names declared by hand are not.
(The syntactic filter rejects `unsafe` and `implemented_by` in a DAG file before this check; the
module here is compiled without it.)

    python3 -m unittest discover -s python/tests -p 'test_platform.py' -v
"""

from __future__ import annotations

import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from common import REPO

MODULE = """\
def foo (n : Nat) : Nat := n + 1
unsafe def foo._unsafe_rec (n : Nat) : Nat := n
inductive P : Prop | a | b
unsafe def P.ctorIdx._impl : P → Nat := fun _ => 0
@[implemented_by P.ctorIdx._impl] def P.ctorIdx : P → Nat := fun _ => 0
inductive T | a | b | c (t : T)
def bar : Nat → Nat
  | 0 => 0
  | n+1 => bar (n / 2) + 1
decreasing_by omega
class inductive C | a | b
"""

CHECK = """\
import SigabaNeo.Platform
import Forge
open Lean Elab Command
run_cmd do
  for w in SigabaNeo.Platform.forbidden (← getEnv) `Forge do
    logInfo m!"forbidden: {w}"
"""


class ForbiddenTest(unittest.TestCase):
    def test_compiler_code(self):
        tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-platform-"))
        try:
            def lake_env(*args: str) -> str:
                return subprocess.run(["lake", "env", *args], cwd=REPO, text=True,
                                      capture_output=True, check=True).stdout.strip()
            lean = lake_env("which", "lean")
            env = {"LEAN_PATH": lake_env("printenv", "LEAN_PATH") + ":" + str(tmp),
                   "PATH": "/usr/bin:/bin"}
            (tmp / "Forge.lean").write_text(MODULE)
            (tmp / "Check.lean").write_text(CHECK)
            subprocess.run([lean, "-o", "Forge.olean", "Forge.lean"], cwd=tmp, env=env, check=True)
            out = subprocess.run([lean, "Check.lean"], cwd=tmp, env=env, text=True,
                                 capture_output=True)
            got = sorted(line.split("forbidden: ", 1)[1] for line in out.stdout.splitlines()
                         if "forbidden: " in line)
            self.assertEqual(got, ["P.ctorIdx is implemented_by", "P.ctorIdx._impl is unsafe",
                                   "foo._unsafe_rec is unsafe"], out.stdout + out.stderr)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


class StdBuildTest(unittest.TestCase):
    def test_every_std_module_is_built(self):
        """`lake build` (as the environment image runs it) builds every std module of the
        manifest, also those the umbrella `SigabaNeoStd` does not import: a DAG node may import
        any of them, and the image's core is read only."""
        import dag
        lib = REPO / ".lake" / "build" / "lib" / "lean"
        missing = [m for m in dag.std_manifest()
                   if not (lib / Path(*m.split("."))).with_suffix(".olean").exists()]
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
