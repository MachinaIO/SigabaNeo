"""The whole cycle on the compatible server (`p2m_server.py`), on the echo claim.

1. `submit` (twice, the second a no-op); `check` reports `open`.
2. An agent publishes a definition and a child lemma.
3. A sketch of the refute claim: `SKETCH_ACCEPTED`.
4. The child's proof: `ACCEPTED`, and both theorems become `Proved`.
5. Bad submissions: `FAILED`, `WA`, `SORRY`, `CE`, importing the target itself.
6. `check` reports `refuted`.

    python3 -m unittest discover -s python/tests -p 'test_server.py' -v
"""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path

import json

from common import load, make_claim
from sigaba_neo import Claim, Server, check, selected, submit, slug
from p2m_server import CORE, Core, Platform, PlatformConfig, serve
from test_client import (AXIOM_SOLUTION, CHILD_PREAMBLE, CHILD_SOLUTION, CHILD_STATEMENT,
                         DEF_ECHO, ROOT_SOLUTION, WRONG_SOLUTION)

KEY = "agent-key"
OTHER = "other-key"
state: dict = {}


def setUpModule():
    tmp = Path(tempfile.mkdtemp(prefix="sigaba-neo-server-"))
    pf = Platform(PlatformConfig(tmp / "data", Core(CORE), {KEY: "agent", OTHER: "other"}))
    httpd = serve(pf, "127.0.0.1", 0)
    base = f"http://127.0.0.1:{httpd.server_address[1]}/api/v1"
    state.update(tmp=tmp, pf=pf, httpd=httpd, base=base, server=Server(base, KEY))


def tearDownModule():
    state["httpd"].shutdown()
    state["httpd"].server_close()
    state["pf"].stop.set()
    shutil.rmtree(state["tmp"], ignore_errors=True)


def prove(theorem_id: str, content: str, kind: str = "prove") -> str:
    """An agent's submission through `/verify`; its final status."""
    s = state["server"]
    r = s.post_form("/verify", {"theorem_id": theorem_id, "proof_type": kind, "file": content})
    return s.wait(f"/verify?submission_id={r['submission_id']}", lambda x: x != "PENDING")["status"]


class ServerTest(unittest.TestCase):
    def test_cycle(self):
        s = state["server"]
        self.assertEqual(Server(state["base"], None).get("/health")["status"], "ok")
        tok = s.post("/agent/refresh", {"api_key": KEY})["access_token"]
        env = Server(state["base"], tok).get("/environments")["environments"][0]
        self.assertIn("cslib-frontier", env["packages"])

        # The submitter (twice: the second time changes nothing).
        claim = load("echo").claim
        ids = submit(s, claim)
        self.assertEqual(submit(s, claim), ids)
        self.assertEqual(s.theorem(claim.name("refute"))["status"], "Open")
        self.assertEqual(check(s, claim, state["tmp"] / "check0")["outcome"], "open")

        # An agent.
        d1 = s.publish("/submit-definition", {"definition_name": "EchoP2M",
                                              "definition_title": "echo",
                                              "definition": DEF_ECHO})["definition_id"]
        self.assertRegex(d1, r"^[0-9a-f]{64}$")
        # Content IDs: the same content (up to whitespace and comments) is the same definition;
        # other content under the same name is refused.
        d2 = s.publish("/submit-definition", {"definition_name": "EchoP2M",
                                              "definition_title": "echo again",
                                              "definition": "-- a comment\n" + DEF_ECHO.replace(
                                                  "noncomputable def echo", "noncomputable  def  echo")
                                              })["definition_id"]
        self.assertEqual(d1, d2)
        other = s.post("/submit-definition", {"definition_name": "EchoP2M", "definition_title": "x",
                                              "definition": DEF_ECHO.replace("headD false",
                                                                             "headD true")})
        job = s.wait(f"/publish-jobs/{other['job_id']}", lambda x: x not in ("PENDING", "COMPILING"))
        self.assertEqual(job["status"], "FAILED")
        self.assertIn("taken by different content", job["error_message"])
        child = s.publish("/submit-problem", {
            "theorem_name": "TestCase.EchoP2M.echo_ppt", "theorem_title": "echo is PPT",
            "preamble": CHILD_PREAMBLE, "formal_statement": CHILD_STATEMENT,
            "natural_language_statement": "The echo adversary is PPT."})["theorem_id"]
        bad = s.post("/submit-problem", {
            "theorem_name": "Bad.stmt", "theorem_title": "bad", "preamble": "def helper : Nat := 0",
            "formal_statement": "theorem Bad.stmt : helper = 0 := by sorry",
            "natural_language_statement": "x"})
        job = s.wait(f"/publish-jobs/{bad['jobs'][0]['job_id']}", lambda x: x not in
                     ("PENDING", "COMPILING"))
        self.assertEqual(job["status"], "FAILED")
        self.assertIn("declares more than", job["error_message"])

        self.assertEqual(prove(ids["refute"], ROOT_SOLUTION), "SKETCH_ACCEPTED")
        self.assertEqual(s.theorem(claim.name("refute"))["status"], "Open")
        leaves = s.get(f"/theorems/{ids['refute']}/open-leaves")["open_leaves"]
        self.assertEqual([x["theorem_name"] for x in leaves], ["TestCase.EchoP2M.echo_ppt"])
        self.assertEqual(prove(child, CHILD_SOLUTION), "ACCEPTED")
        # The same proof again (other whitespace) is the same submission, with its verdict.
        r1 = s.post_form("/verify", {"theorem_id": child, "proof_type": "prove",
                                     "file": CHILD_SOLUTION.replace("  ppt", "  -- again\n  ppt")})
        p1 = s.wait(f"/verify?submission_id={r1['submission_id']}", lambda x: x != "PENDING")
        subs = s.get(f"/theorems/{child}/submissions", status="ACCEPTED")["submissions"]
        self.assertEqual([x["id"] for x in subs], [p1["id"]])
        self.assertEqual(p1["status"], "ACCEPTED")
        self.assertEqual(s.theorem("TestCase.EchoP2M.echo_ppt")["status"], "Proved")
        self.assertEqual(s.theorem(claim.name("refute"))["status"], "Proved")

        # Bad submissions to the prove claim.
        self.assertEqual(prove(ids["prove"], AXIOM_SOLUTION.replace(
            "¬ TestCase.Echo.target", "TestCase.Echo.target")), "FAILED")
        self.assertEqual(prove(ids["prove"], WRONG_SOLUTION), "WA")
        self.assertEqual(prove(ids["prove"], "import Definitions.Def_Echo\n\ntheorem solution : "
                               "TestCase.Echo.target := by sorry\n"), "SORRY")
        self.assertEqual(prove(ids["prove"], "theorem solution : oops := by\n"), "CE")
        own = f"import Theorems.Thm_{claim.name('prove').replace('.', '_')}\n"
        self.assertEqual(prove(ids["prove"], own + "theorem solution : True := trivial\n"), "FAILED")
        self.assertEqual(s.theorem(claim.name("prove"))["status"], "Open")

        # The submitter checks.
        r = check(s, claim, state["tmp"] / "check")
        self.assertEqual(r["outcome"], "refuted", r)
        refute = next(x for x in r["cards"] if x["polarity"] == "refute")
        self.assertEqual(refute["nodes"], [claim.name("refute"), "TestCase.EchoP2M.echo_ppt"])

    def test_hypotheses(self):
        """Cards are per proposition and reductions compose: S is reduced to A, A to B (by other
        agents, on A's own card), and a claim of S that allows only B is refuted under B. The
        hypotheses are chosen on the server and fixed at submission."""
        s, pf, tmp = state["server"], state["pf"], state["tmp"]
        vac = load("vacuous").claim
        defs = {**vac.definitions, "Chain": "namespace TestCase.Chain\n\n"
                "def a : Prop := False\ndef b : Prop := False\n\nend TestCase.Chain\n"}
        # Two assumptions, each a claim of its own; the operator annotates B.
        a = make_claim(tmp / "assumption-a", "TestCase.Chain.a", [], defs)
        b = make_claim(tmp / "assumption-b", "TestCase.Chain.b", [], defs)
        submit(s, a)
        submit(s, b)
        card_a, card_b = a.name("prove"), b.name("prove")
        pf.annotate(card_b, ["well-established"], 2000, "test")
        rows = s.get("/sigaba-neo/assumptions")["assumptions"]
        row = next(r for r in rows if r["theorem_name"] == card_b)
        self.assertEqual((row["tags"], row["proposed_year"], row["refute"]["sketches"]),
                         (["well-established"], 2000, 0))

        # The claim of S selects B.
        d = tmp / "claim"
        make_claim(d, "TestCase.Vacuous.strong", [], defs)
        c = json.loads((d / "claim.json").read_text())
        c["select"] = [{"tag": "well-established", "minYears": 5}]
        (d / "claim.json").write_text(json.dumps(c))
        claim = Claim.load(d)
        self.assertEqual([r["theorem_name"] for r in selected(s, claim)], [card_b])
        self.assertEqual(selected(s, Claim(d, claim.target, [], claim.definitions,
                                           select=[{"minRefuteSketches": 1}])), [])
        ids = submit(s, claim)
        claim = Claim.load(d)
        self.assertEqual((claim.hypotheses, claim.cards), (["TestCase.Chain.b"],
                                                           {"TestCase.Chain.b": card_b}))
        self.assertIsNotNone(claim.resolved_at)
        self.assertEqual(submit(s, claim), ids)       # fixed: not resolved again
        # The cards are the proposition's: the same with other hypotheses.
        self.assertEqual(claim.name("prove"), Claim(d, claim.target, [], claim.definitions).name("prove"))

        # Agents: S from A (a sketch on S's refute card), A from B (on A's own card).
        imp = lambda card: f"import Theorems.Thm_{slug(card)}\nimport Definitions.Def_Chain\n"  # noqa: E731
        self.assertEqual(prove(ids["refute"], imp(card_a) + "import Definitions.Def_Vacuous\n\n"
                               "theorem solution : ¬ TestCase.Vacuous.strong := "
                               f"fun _ => (show False from {card_a})\n"), "SKETCH_ACCEPTED")
        self.assertEqual(s.theorem(card_a)["status"], "Open")
        r = check(s, claim, tmp / "check-before")
        self.assertEqual(r["outcome"], "open", json.dumps(r, indent=1))
        self.assertEqual(prove(s.theorem(card_a)["theorem_id"], imp(card_b) + "\n"
                               f"theorem solution : TestCase.Chain.a := (show False from {card_b})\n"),
                         "SKETCH_ACCEPTED")

        # The submitter checks: refuted under B, through A.
        r = check(s, claim, tmp / "check-hyp")
        self.assertEqual(r["outcome"], "refuted", json.dumps(r, indent=1))
        refute = next(x for x in r["cards"] if x["polarity"] == "refute")
        self.assertEqual(refute["nodes"], [claim.name("refute"), card_a])
        self.assertEqual(refute["hypotheses"], [card_b])
        self.assertIn("established: TestCase.Chain.b → ¬ TestCase.Vacuous.strong", refute["report"])
        self.assertIn(f"hypothesis axioms: {card_b}", refute["report"])

    def test_discussion(self):
        """Claims are missions (Prove2Me's entry point for agents) with a discussion thread."""
        s = state["server"]
        claim = load("echo").claim
        ids = submit(s, claim)
        missions = s.get("/missions", q=claim.digest[:16])["missions"]
        self.assertEqual([m["id"] for m in missions], [ids["prove"]])
        mid = ids["prove"]
        self.assertEqual(missions[0]["main_theorem"]["theorem_name"], claim.name("prove"))
        self.assertEqual(missions[0]["refute_theorem"]["theorem_name"], claim.name("refute"))
        self.assertEqual(s.get(f"/missions/{mid}")["id"], mid)
        ms = s.get(f"/missions/{mid}/milestones")["milestones"]
        self.assertEqual([m["theorem"]["theorem_name"] for m in ms],
                         [claim.name("prove"), claim.name("refute")])
        self.assertIsNone(s.get(f"/missions/{ids['refute']}"))     # only prove cards are missions
        self.assertEqual(s.get("/fields")["fields"], [])

        # A failed attempt, logged with references; a reply.
        r = s.post_form("/verify", {"theorem_id": ids["prove"], "proof_type": "prove",
                                    "file": WRONG_SOLUTION})
        sub = s.wait(f"/verify?submission_id={r['submission_id']}", lambda x: x != "PENDING")
        c = s.post(f"/missions/{mid}/comments", {
            "body_md": f"Tried `True` — wrong type, see [it](p2m:solution/{r['submission_id']}) "
                       f"and [the refute card](p2m:theorem/{ids['refute']}).",
            "tags": ["attempt"]})
        self.assertEqual(c["tags"], ["attempt"])
        self.assertTrue(c["is_agent"])
        refs = {x["type"]: x for x in c["references"]}
        self.assertEqual(refs["theorem"]["name"], claim.name("refute"))
        self.assertEqual((refs["solution"]["id"], refs["solution"]["status"]), (sub["id"], "WA"))
        reply = s.post(f"/missions/{mid}/comments", {"body_md": "Refute instead.",
                                                     "tags": ["strategy"],
                                                     "parent_comment_id": c["id"]})
        self.assertEqual(reply["parent_comment_id"], c["id"])
        thread = s.get(f"/missions/{mid}/comments")
        self.assertEqual([x["id"] for x in thread["comments"]], [reply["id"], c["id"]])
        self.assertEqual([x["id"] for x in s.get(f"/missions/{mid}/comments", tag="attempt")
                          ["comments"]], [c["id"]])
        with self.assertRaisesRegex(SystemExit, "HTTP 400"):
            s.get(f"/missions/{mid}/comments", tag="nonsense")
        self.assertEqual([m["comment_id"] for m in
                          s.get(f"/theorems/{ids['refute']}/mentions")["mentions"]], [c["id"]])
        self.assertEqual([m["comment_id"] for m in
                          s.get(f"/submissions/{r['submission_id']}/mentions")["mentions"]], [c["id"]])

        # Only the author edits or deletes; deletes are soft.
        other = Server(state["base"], OTHER)
        with self.assertRaisesRegex(SystemExit, "HTTP 403"):
            other.call("DELETE", f"/missions/{mid}/comments/{c['id']}")
        e = s.call("PATCH", f"/missions/{mid}/comments/{c['id']}",
                   json.dumps({"body_md": "Edited.", "tags": ["attempt", "strategy"]}).encode(),
                   "application/json")
        self.assertEqual((e["body_md"], e["references"], e["tags"]), ("Edited.", [],
                                                                      ["attempt", "strategy"]))
        s.call("DELETE", f"/missions/{mid}/comments/{c['id']}")
        self.assertEqual([x["id"] for x in s.get(f"/missions/{mid}/comments")["comments"]],
                         [reply["id"]])
        gone = s.get(f"/missions/{mid}/comments", include_deleted="true")["comments"]
        self.assertTrue(next(x for x in gone if x["id"] == c["id"])["deleted"])


if __name__ == "__main__":
    unittest.main()
