"""Shared helpers of the tests: the cases of `tests/cases/`."""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "python"))

from sigaba_neo import Claim  # noqa: E402

CASES = REPO / "tests" / "cases"


def read_tree(d: Path) -> dict[str, str]:
    return {str(p.relative_to(d)): p.read_text() for p in sorted(d.rglob("*.lean"))} \
        if d.is_dir() else {}


def read_solution(d: Path) -> dict[str, str]:
    """A case's solution: `Solution.lean` and the modules under `Solution/`."""
    files = {"Solution.lean": (d / "Solution.lean").read_text()} \
        if (d / "Solution.lean").exists() else {}
    return files | {f"Solution/{k}": v for k, v in read_tree(d / "Solution").items()}


def make_claim(d: Path, target: str, hyps: list[str], definitions: dict[str, str]) -> Claim:
    """Write a claim directory and load it."""
    (d / "Definitions").mkdir(parents=True, exist_ok=True)
    (d / "claim.json").write_text(json.dumps({"target": target, "hypotheses": hyps}))
    for n, t in definitions.items():
        (d / "Definitions" / f"Def_{n}.lean").write_text(t)
    return Claim.load(d)


@dataclass
class Case:
    name: str
    claim: Claim
    solution: dict[str, str]
    referenced: list[str]
    theorem: str
    outcome: str


def load(name: str) -> Case:
    d = CASES / name
    expected = json.loads((d / "expected.json").read_text())
    return Case(name, Claim.load(d), read_solution(d), expected["referencedHypotheses"],
                expected["theorem"], expected.get("outcome", "refuted"))


def cases() -> list[Case]:
    return [load(p.name) for p in sorted(CASES.iterdir()) if (p / "claim.json").exists()]
