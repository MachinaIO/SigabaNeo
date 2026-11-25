# Instructions for AI agents

This repository is the Sigaba-Neo **core**: the trusted check and vocabulary (`SigabaNeo/`), the
standard library (`SigabaNeoStd/`), and the tooling (`python/`, `schemas/`, `templates/`). Start
with [README.md](README.md); the DAG platform is described in
[docs/GITHUB_PLATFORM.md](docs/GITHUB_PLATFORM.md).

## Submitting work: use the `sigaba-dag` skill

Theorems, lemmas, definitions, proofs, proof sketches and research notes that an AI agent produces
are first submitted as pull requests to the separate **DAG repository** whose URL is in
[`DAG_REPO_URL`](DAG_REPO_URL). Follow the skill
[`.claude/skills/sigaba-dag/SKILL.md`](.claude/skills/sigaba-dag/SKILL.md) for every such
submission. In short:

- Open the pull request directly on the DAG repository if you have write access to it; otherwise
  fork it and open the pull request from the fork.
- Everything submitted (Markdown, metadata, Lean comments and docstrings, commit messages, PR
  titles and bodies) is in English.
- Verify locally with `python/dag_verify.py` before opening the pull request.

## Editing Lean projects other than SigabaNeo and SigabaNeoStd

You may edit `SigabaNeo/` and `SigabaNeoStd/` directly. For **any other Lean project**, do not
write new theorems or proofs into it directly. Instead:

1. State what the project needs as theorem nodes (with the definitions they use) and submit them
   to the DAG repository with the `sigaba-dag` skill.
2. Work on them there (direct proofs, or sketches reducing them to new child theorems) until the
   submitted proposition has a **complete** proof in the DAG: gate status `ACCEPTED` (not just
   `SKETCH_ACCEPTED`), with every theorem it uses proved.
3. Only then bring into the project the parts needed for that proof (definitions, lemmas,
   solutions). Refactor them as appropriate for the project: rename `theorem solution` and the
   DAG's `Thm_*` / `Def_*` modules to proper names, merge files, inline sketch steps, remove
   duplicates of what the project or its dependencies already have.

## Repository conventions

- Generic machine code (machine-in-machine composition, inlining, programs) goes in
  `SigabaNeoStd/Machines`, not in a topic directory such as `SigabaNeoStd/Lattices`.
