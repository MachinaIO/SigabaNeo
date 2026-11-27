# Instructions for AI agents

This repository is the Sigaba-Neo **core**: the trusted check and vocabulary (`SigabaNeo/`), the
standard library (`SigabaNeoStd/`) and the tooling. See [README.md](README.md) and
[docs/GITHUB_PLATFORM.md](docs/GITHUB_PLATFORM.md).

## Submitting work

Everything an agent produces (definitions, theorems, proofs, notes) goes first to the **DAG
repository** in [`DAG_REPO_URL`](DAG_REPO_URL), by pull request: directly with write access,
otherwise from a fork. Everything submitted is in English. How:
[`sigaba-dag`](.claude/skills/sigaba-dag/SKILL.md).

## Roles

Take the role your human gives you and follow its skill or reference (each builds on `sigaba-dag`). For
research on a goal, start from [`sigaba-research`](.claude/skills/sigaba-research/SKILL.md), which
routes to the others and runs workers through the controller `python/sigaba_research.py`
([docs/RESEARCH_PROTOCOL.md](docs/RESEARCH_PROTOCOL.md)).

| Role | Does | Skill |
| --- | --- | --- |
| Research orchestrator | Agrees on a goal with the user, splits it into tasks (one draft PR each), dispatches bounded worker episodes, finalizes tasks | [`sigaba-research`](.claude/skills/sigaba-research/SKILL.md) |
| Problem author | Turns the user's request into a primitive and its Submission proposition `Spec P R`; submits it to the DAG **after the user approves**, and adds it to any working repository that uses Sigaba-Neo | [`sigaba-problem-author`](.claude/skills/sigaba-problem-author/SKILL.md) |
| Design AI | Builds a concrete construction for a submitted primitive and registers the proof of the Submission proposition and its lemmas in the DAG; registers new hardness assumptions if needed | [`sigaba-research` › design](.claude/skills/sigaba-research/references/design.md) |
| Cryptanalysis AI | Proves attacks on registered assumptions that cost less than the claimed strength, so the strength is lowered | [`sigaba-research` › cryptanalysis](.claude/skills/sigaba-research/references/cryptanalysis.md) |

## Lean projects other than SigabaNeo and SigabaNeoStd

`SigabaNeo/` and `SigabaNeoStd/` may be edited directly. In any other Lean project, do not write
new theorems or proofs directly: submit them to the DAG, and once the submitted proposition has a
complete proof there (gate status `ACCEPTED`, not only `SKETCH_ACCEPTED`), bring in the parts that
proof needs, refactored as appropriate (proper names instead of `solution` and `Thm_*`/`Def_*`,
merged files, no duplicates). The problem author's definitions of a primitive are the one
exception: they are added to such a project when they are submitted.

## Conventions

- Skills live in `.claude/skills/` (Claude Code). `python3 python/sigaba_research.py skills sync`
  copies them to `.agents/skills/` (Codex) and, rewritten for an installed core, to
  `plugin/skills/` (the `sigaba-neo` plugin for both). Edit the source, then sync.

- Everything committed is in English, whatever language you use with your human: documents,
  code comments and docstrings, commit messages, branch names, PR titles, bodies and comments.

- Generic machine code (machine-in-machine composition, inlining, programs) goes in
  `SigabaNeoStd/Machines`, not in a topic directory such as `SigabaNeoStd/Lattices`.
