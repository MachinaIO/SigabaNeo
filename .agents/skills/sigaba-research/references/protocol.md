# Protocol records (summary)

The authoritative text is docs/RESEARCH_PROTOCOL.md in the core; the schemas are
`schemas/research-*.schema.json`. The controller validates everything; this page lists the fields
you supply.

| Record | You supply | Where it lives |
| --- | --- | --- |
| Goal (`goal prepare --file`) | `kind` (primitive, assumption, claim, theme), `title`, `targets` and `definitions` (DAG references `theorem:…` / `definition:…`), `objective` (`kind`: minimize_cost, lower_strength, prove, refute, decide, explore; `threshold`), `policy` (`forbidden_routes`, `intent`), optional `parent` | note `dag/Notes/goal-<fingerprint>.md` on `main` |
| Task (`work propose`, `task create`) | `goal`, `domain`, `operation`, `title`, `scope`, `deliverables`, `success`, `targets`, `related`, `depends_on` | the PR body |
| Plan (`plan add`) | `target` (`{"kind": "goal"|"task", "id"}`), `required` (task UUIDs, the AND group), `rationale`, `supersedes_plan` | a PR comment |
| Candidate (`candidate add`) | `kind` (construction, attack, proof_route, generalization), `parents`, `refs`, `open_obligations`, `description`, `obstructions` | a PR comment |
| Progress (`progress record`) | `summary`, `established`, `attempted`, `blockers`, `next_steps`, `falsification`, `artifacts` | local; summarized in checkpoints |
| Summary (`task finalize --file`) | the prose | note `dag/Notes/task-<id8>-<slug>.md`, merged |

States of a task (operational, never mathematical): `planned`, `active`, `paused`, `blocked`,
`ready`, `merged`, `closed`, `stale`. Outcomes: `verified_solution`, `verified_refutation`,
`verified_partial`, `candidate`, `handoff`, `inconclusive`, `duplicate`, `cancelled`,
`infra_failure`. Mathematical status (`Proved`, `Disproved`, `Open`, …) comes only from the
records.

Checkpoints: every period (default 600 s) and on every state change, the controller posts a new
comment with a `sigaba-checkpoint-v1` record and rewrites the PR's first comment to show only the
latest state. Without a fresh progress record it posts a heartbeat that says so.
