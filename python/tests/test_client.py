"""`sigaba_neo.py check` against a fake server that reports whatever each scenario wants.

The claim is the echo case (`¬ TestCase.Echo.target` holds).

    python3 -m unittest discover -s python/tests -p 'test_client.py' -v
"""

from __future__ import annotations

import json
import shutil
import tempfile
import threading
import unittest
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from common import load
from sigaba_neo import Server, check

TARGET = "TestCase.Echo.target"
OPENS = "open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM"

DEF_ECHO = f"""import CslibFrontier.Crypto.Computational.PseudorandomFunction

namespace TestCase.EchoP2M
{OPENS}

/-- Query once, output the first bit of the reply. -/
noncomputable def echo : OracleDistinguisher := fun _ _ =>
  (fun reply : List Bool => reply.headD false) <$>
    (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), []))

end TestCase.EchoP2M
"""

CHILD_PREAMBLE = f"import Definitions.Def_EchoP2M\n{OPENS}"
CHILD_STATEMENT = "theorem TestCase.EchoP2M.echo_ppt : IsOraclePPT encBool TestCase.EchoP2M.echo := by sorry"
CHILD_SOLUTION = f"""import Definitions.Def_EchoP2M
import CslibFrontier.Tactic.PPT
{OPENS}

theorem solution : IsOraclePPT encBool TestCase.EchoP2M.echo := by
  ppt [TestCase.EchoP2M.echo]
"""

ROOT_SOLUTION = f"""import Definitions.Def_Echo
import Definitions.Def_EchoP2M
import Theorems.Thm_TestCase_EchoP2M_echo_ppt
import CslibFrontier.Crypto.Negligible.Basic

namespace TestCase.EchoSol
{OPENS}

theorem game_echo (b : Bool) (n : ℕ) :
    ProbComp.eval (TestCase.Echo.game b TestCase.EchoP2M.echo n) = PMF.pure b := by
  simp [TestCase.Echo.game, TestCase.EchoP2M.echo]

end TestCase.EchoSol

{OPENS}

theorem solution : ¬ TestCase.Echo.target := by
  intro h
  have hneg := h TestCase.EchoP2M.echo TestCase.EchoP2M.echo_ppt
  simp only [TestCase.EchoSol.game_echo] at hneg
  have hadv : Game.advantage (PMF.pure false) (PMF.pure true) = 1 := by
    simp [Game.advantage, Game.succProbability, NNReal.nndist_eq]
  rw [hadv] at hneg
  exact not_negligible_const one_ne_zero hneg
"""

AXIOM_SOLUTION = """import Definitions.Def_Echo

axiom cheat : ¬ TestCase.Echo.target

theorem solution : ¬ TestCase.Echo.target := cheat
"""

WRONG_SOLUTION = """import Definitions.Def_Echo

theorem solution : True := trivial
"""


class FakeProve2Me:
    """Theorems, definitions, submissions; the API routes the client uses."""

    def __init__(self):
        self.theorems: dict[str, dict] = {}
        self.definitions: list[dict] = []
        self.subs: dict[str, dict] = {}       # id -> {theorem_id, status, content, children}

    def add_theorem(self, tid, name, preamble, statement, status, env):
        self.theorems[tid] = {"theorem_id": tid, "theorem_name": name, "status": status,
                              "preamble": preamble, "formal_statement": statement,
                              "mathlib_rev": env, "deprecated_at": None}

    def add_sub(self, sid, tid, content, children=(), status="ACCEPTED"):
        self.subs[sid] = {"id": sid, "theorem_id": tid, "status": status, "content": content,
                          "children": list(children), "accepted_at": "2026-11-01T00:00:00Z",
                          "deprecated_at": None}

    def route(self, path: str, q: dict) -> tuple[int, dict]:
        parts = path.strip("/").split("/")[2:]  # after api/v1
        if parts == ["theorems"]:
            return 200, {"theorems": list(self.theorems.values())}
        if parts == ["definitions"]:
            return 200, {"definitions": self.definitions}
        if len(parts) == 2 and parts[0] == "theorems":
            t = self.theorems.get(parts[1])
            return (200, t) if t else (404, {"error": "no"})
        if len(parts) == 3 and parts[0] == "theorems" and parts[2] == "submissions":
            want = set(q.get("status", [""])[0].split(","))
            return 200, {"submissions": [s for s in self.subs.values()
                                         if s["theorem_id"] == parts[1] and s["status"] in want]}
        if len(parts) == 3 and parts[0] == "theorems" and parts[2] == "decompositions":
            out = []
            for s in self.subs.values():
                if s["theorem_id"] == parts[1] and s["children"]:
                    out.append({"submission_id": s["id"], "children": [
                        {"theorem_id": c, "theorem_name": self.theorems[c]["theorem_name"],
                         "status": self.theorems[c]["status"]} for c in s["children"]]})
            return 200, {"decompositions": out}
        if len(parts) == 3 and parts[0] == "submissions" and parts[2] == "solution":
            s = self.subs.get(parts[1])
            return (200, {"content": s["content"]}) if s else (404, {"error": "no"})
        return 404, {"error": "no route"}

    def serve(self) -> tuple[ThreadingHTTPServer, str]:
        fake = self

        class H(BaseHTTPRequestHandler):
            def do_GET(self):
                u = urllib.parse.urlparse(self.path)
                if self.headers.get("Authorization") != "Bearer test-token":
                    code, body = 401, {"error": "auth"}
                else:
                    code, body = fake.route(u.path, urllib.parse.parse_qs(u.query))
                data = json.dumps(body).encode()
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)

            def log_message(self, *a):
                pass

        httpd = ThreadingHTTPServer(("127.0.0.1", 0), H)
        threading.Thread(target=httpd.serve_forever, daemon=True).start()
        return httpd, f"http://127.0.0.1:{httpd.server_address[1]}/api/v1"


state: dict = {}


def setUpModule():
    state["tmp"] = Path(tempfile.mkdtemp(prefix="sigaba-neo-p2m-"))
    state["claim"] = load("echo").claim


def tearDownModule():
    shutil.rmtree(state["tmp"], ignore_errors=True)


class Prove2MeTest(unittest.TestCase):
    def run_check(self, name: str, populate) -> dict:
        claim = state["claim"]
        fake = FakeProve2Me()
        for n, t in claim.definitions.items():
            fake.definitions.append({"definition_name": n, "definition": t})
        cards = {p: {"theorem_name": claim.name(p), "preamble": claim.preamble,
                     "formal_statement": claim.card_statement(claim.name(p), p == "refute") +
                     " := by sorry"} for p in ("prove", "refute")}
        populate(fake, cards, "env")
        httpd, base = fake.serve()
        try:
            return check(Server(base, "test-token"), claim, state["tmp"] / name)
        finally:
            httpd.shutdown()
            httpd.server_close()

    @staticmethod
    def card(fake, cards, pol, tid, status, env):
        c = cards[pol]
        fake.add_theorem(tid, c["theorem_name"], c["preamble"], c["formal_statement"], status, env)

    def test_reduction_proof(self):
        """The refute card is proved by a sketch whose child lemma is proved."""
        def populate(fake, cards, env):
            self.card(fake, cards, "prove", "t-prove", "Open", env)
            self.card(fake, cards, "refute", "t-refute", "Proved", env)
            fake.definitions.append({"definition_name": "EchoP2M", "definition": DEF_ECHO,
                                     "deprecated_at": None})
            fake.add_theorem("t-ppt", "TestCase.EchoP2M.echo_ppt", CHILD_PREAMBLE, CHILD_STATEMENT,
                             "Proved", env)
            fake.add_sub("s-root", "t-refute", ROOT_SOLUTION, ["t-ppt"], status="SKETCH_ACCEPTED")
            fake.add_sub("s-ppt", "t-ppt", CHILD_SOLUTION)

        r = self.run_check("reduction", populate)
        self.assertEqual(r["outcome"], "refuted", json.dumps(r, indent=1))
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertTrue(refute["verified"])
        self.assertIn(f"established: ¬ {TARGET}", refute["report"])
        self.assertEqual(refute["nodes"], [refute["theorem_name"], "TestCase.EchoP2M.echo_ppt"])
        prove = next(c for c in r["cards"] if c["polarity"] == "prove")
        self.assertFalse(prove["verified"])
        self.assertEqual(prove["status"], "Open")

    def test_open_child(self):
        """A sketch whose child lemma is still open is no proof."""
        def populate(fake, cards, env):
            self.card(fake, cards, "refute", "t-refute", "Proved", env)
            fake.definitions.append({"definition_name": "EchoP2M", "definition": DEF_ECHO,
                                     "deprecated_at": None})
            fake.add_theorem("t-ppt", "TestCase.EchoP2M.echo_ppt", CHILD_PREAMBLE, CHILD_STATEMENT,
                             "Open", env)
            fake.add_sub("s-root", "t-refute", ROOT_SOLUTION, ["t-ppt"], status="SKETCH_ACCEPTED")

        r = self.run_check("open-child", populate)
        self.assertEqual(r["outcome"], "open", json.dumps(r, indent=1))
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertEqual(refute["problems"], ["no complete proof could be downloaded"])

    def test_axiom_and_wrong_type(self):
        """Prove2Me's verdict is not trusted: an axiom, and a solution of another type."""
        def populate(fake, cards, env):
            self.card(fake, cards, "prove", "t-prove", "Proved", env)
            self.card(fake, cards, "refute", "t-refute", "Proved", env)
            fake.add_sub("s-wrong", "t-prove", WRONG_SOLUTION)
            fake.add_sub("s-axiom", "t-refute", AXIOM_SOLUTION)

        r = self.run_check("axiom", populate)
        self.assertEqual(r["outcome"], "open", json.dumps(r, indent=1))
        prove = next(c for c in r["cards"] if c["polarity"] == "prove")
        refute = next(c for c in r["cards"] if c["polarity"] == "refute")
        self.assertFalse(prove["verified"])
        self.assertFalse(refute["verified"])
        self.assertIn("depends on the axiom", refute["report"])


if __name__ == "__main__":
    unittest.main()
