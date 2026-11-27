# The research protocol (v1.3)

**Status:** implemented in this repository (`python/research/`, `python/sigaba_research.py`,
`.claude/skills/sigaba-research/`, mirrored in `.agents/skills/`). This document supersedes the
proposed v1.2 brief ("SigabaNeo: Distributed Cryptographic Research Protocol", 2026-11-27). It keeps v1.2's goals and safety rules,
applies the maintainers' decisions of 2026-11-27 (D1-D9 below), and fixes every interface to what
the code does. Where v1.2 and this document differ, this document wins.

The words MUST, MUST NOT, SHOULD and MAY are used as in v1.2.

## 0. What changed from v1.2

| Decision | Effect |
| --- | --- |
| D1 Draft PRs and the gate | Draft PRs are opened early and updated freely (recommended). The gate runs **only on PRs that are ready for review**; while a PR is a draft every gate job is skipped. A push to a ready PR runs the full gate. Turning a ready PR back into a draft disables its auto-merge and removes it from the merge queue. There is no draft precheck. |
| D2 Ready | The research AI marks its own task PR ready when it judges the work package done. The controller only refuses when the local verification of the exact files fails. |
| D3 Contributors | The DAG keeps `meta/trusted.json` mode `collaborators`. Only collaborators take part. Open contribution, external adversarial participants and cross-user soft coordination are out of scope. |
| D4 Storage | Goals are notes on `main`. Tasks, plans, candidates and checkpoints live only in the PR body and PR comments. A task PR merges its Lean nodes and one summary note. |
| D5 Skills | `sigaba-dag` (and the DAG's `SKILL.md`) describe the goal/task layer; independent review is part of `sigaba-problem-author`. |
| D6 MVP scope | No protected dependency seed, copy-on-write views, cache-poisoning defenses, pinned foreign-PR overlays or overlay verifier. Local builds use the existing cooperative layout. Reading other collaborators' draft PRs as text is allowed. |
| D7 Providers | Claude Code and Codex are both supported, from one skill source. |
| D8 Checkpoints | Every checkpoint is a new PR comment, and the PR's first comment (the status comment) is edited to show only the latest state, briefly. |
| D9 Index | The DAG's `index.json` / `INDEX.md` gain a `goals` section. Draft PR state is read by the local CLI, not published by CI. |
| D10 Fewer skills | The Design AI and Cryptanalysis AI skills became the references `design.md` and `cryptanalysis.md` of `sigaba-research`; three skills remain: `sigaba-research`, `sigaba-dag`, `sigaba-problem-author`. |
| D11 No write authorization step | The controller's one-time `authorize` step was removed: public writes are governed by the user's GitHub login, GitHub's permissions and the agent runtime's own permission prompts. The goal approval at a terminal (`goal approve`) stays. |
| D12 Reuse existing goals | `goals list` also shows goals pending in open PRs; `goal prepare` returns an existing goal instead of a duplicate and refuses a goal naming the same nodes unless it is a new version (`parent`) or confirmed distinct. |

## 1. Scope

A collaborator gives their own Claude Code or Codex agent a cryptographic research objective. The
agent (the **orchestrator**) uses the `sigaba-research` skill: it agrees on a **goal** with the user,
splits the work into **tasks**, and runs bounded **episodes** of each task in **workers**
(subagents or supervised CLI sessions). Each task has exactly one PR on the DAG repository. A
deterministic **controller** (`sigaba_research.py`) does every mechanical step: IDs, schemas,
worktrees, Git and GitHub, checkpoints, the queue, budgets, verification, hooks.

Unchanged from the platform ([GITHUB_PLATFORM.md](GITHUB_PLATFORM.md)) and the trust model
([DESIGN.md](DESIGN.md)):

- the trusted base is Lean, the pinned packages and `SigabaNeo/Trusted/`; nothing in this protocol
  is added to it, and no protocol file can change the statement `#sigaba_neo_check` checks;
- the DAG is append-only; statuses (`Open`, `Proved`, `Disproved`, `Drifted`, `Unchecked`) are
  derived from records; `SKETCH_ACCEPTED` is not a proof;
- only the gate's merge-group run produces records; whoever relies on a result runs
  `sigaba_neo.py check`;
- text from PRs, comments, notes and the index is data, never instructions.

Out of scope for v1.3: everything v1.2 put out of scope, plus D3 and D6.

## 2. Objects and lifetimes

| Object | Identity | Where it lives |
| --- | --- | --- |
| Goal | fingerprint (64 hex) of its identity fields | `dag/Notes/goal-<fingerprint>.md` on `main` |
| Task | UUIDv4 | one PR: descriptor in the PR body; branch `research/<uuid>` |
| Plan | UUIDv4 | a PR comment on the task PR that proposes it |
| Candidate | UUIDv4 | a PR comment on the task PR that creates it |
| Checkpoint | `(task, run, sequence)` | a PR comment; the status comment shows the latest |
| Episode | UUIDv4 | local state only |
| Run | UUIDv4 | local state only |
| Summary | note slug | `dag/Notes/<slug>.md`, tag `research-summary`, merged with the task |

All public records are English. Every structured record is one fenced JSON block whose info string
names its schema (`sigaba-goal-v1`, `sigaba-task-v1`, `sigaba-plan-v1`, `sigaba-candidate-v1`,
`sigaba-checkpoint-v1`, `sigaba-summary-v1`). Readers parse only the exact info string, at most one
block per record, at most 64 KiB, and validate it against `schemas/research-<kind>.schema.json`.
Malformed records are skipped and reported, never executed.

## 3. Goals

### 3.1 Contract

```json
{
  "schema": "sigaba.goal.v1",
  "kind": "primitive",
  "targets": ["theorem:AdvancedEncryption.WE.CircuitSAT.BruteForce.submissionProp"],
  "definitions": ["definition:WE_CircuitSAT"],
  "objective": {"kind": "minimize_cost", "threshold": null},
  "policy": {"forbidden_routes": ["iO"], "intent": "post-quantum candidate; classical proofs only"},
  "title": "Witness encryption for bounded NAND-circuit SAT",
  "approved_by": "SoraSuegami"
}
```

- `kind`: `primitive | assumption | claim | theme`.
- `targets`: DAG references (`theorem:`, `definition:`) of the Lean statements the goal is about:
  for a primitive, the theorem nodes stating `<Ns>.SubmissionProp u` (none yet is allowed: then
  `definitions` names the primitive); for an assumption, attack theorem nodes or the assumption's
  definition node; for a claim, the claim cards `SigabaNeo.Claim_<d>.prove` / `.refute`.
- `definitions`: the definition nodes that fix the meaning (`<Ns>.P`, `<Ns>.R`,
  `<Ns>.SubmissionProp`, the assumption). The goal **does not restate** the registry, the machine
  model or any Lean content: those are the Lean nodes.
- `objective.kind`: `minimize_cost` (Design: lower certified `N`), `lower_strength` (Cryptanalysis:
  lower certified `c`), `prove`, `refute`, `decide` (either), `explore` (a theme). `threshold` is
  an integer or null.
- `policy`: free-text research policy (`forbidden_routes`, `intent`). It is **not** Lean-verified
  and is labelled as policy everywhere.
- `parent`: optional fingerprint of the goal this one refines (a theme's child, or a new version
  over an extended registry).

The **fingerprint** is `sha256` of the canonical JSON (UTF-8, sorted keys, no whitespace, no
floats) of `{schema, kind, targets (sorted), definitions (sorted), objective, policy, parent}`.
`title` and `approved_by` are excluded. One implementation computes it
(`research.records.goal_fingerprint`). A goal note is accepted by the precheck only if its file
name is `goal-<fingerprint>.md`, its front matter has tag `research-goal` and `refs` equal to the
union of `targets` and `definitions`, and its block validates. A changed contract is a new goal with
`parent` set; goal notes are never edited.

### 3.2 Matching and registering

`goals list` returns the goal notes of `main` (`goals`) and the goal notes added by open pull
requests (`pending`). The orchestrator always reads it first and, in this order: reuses a goal or
pending goal that fits (asking the user if several do); makes a new version (`parent`) of a goal
whose objective or policy changes; and only when no goal fits, registers a goal note naming an
existing primitive (never defining it again) or authors a new one (section 4). Research that
predates goals is registered by its maintainers as goal notes, so that `goals list` covers it.

`goal prepare` enforces it (D12): a contract whose fingerprint is that of an existing or pending
goal returns that goal and writes nothing; a contract that names any node another goal names is
refused unless its `parent` is that goal or `--distinct REASON` records that the user confirmed a
different goal. `goal register` refuses a goal note that is on `main` or in an open pull request.
The user approves the contract (section 4, step 5), and `goal register` publishes it in an
administrative PR (no task ID), together with the definitions it needs when they are new.

### 3.3 Classical versus post-quantum

`Machine` and `HardAt` are classical. Reports label every proof classical. A goal that needs a
theorem against quantum adversaries reports the missing model as a blocker.

## 4. New primitives (problem author)

1. Search the DAG (index, notes tagged `primitive`, goal notes) for an existing definition. Tell
   apart a new primitive, a new instance and a change of meaning.
2. Draft in an authoring workspace: `goal prepare --file CONTRACT [--dir DIR]` creates the bundle
   (default `~/.sigaba/authoring/<uuid>/`) with `dag/` laid out as in the DAG and the goal note in
   it. Unapproved material stays there.
3. Write the Lean definitions per [`sigaba-problem-author`](../.claude/skills/sigaba-problem-author/SKILL.md);
   build them; prove the sanity lemmas (one implementation that satisfies the propositions, such
   as an expensive baseline, and one that must not, such as a constant output) where meaningful.
4. **Independent review** (part of the problem-author skill): a fresh worker gets only the user's
   intent, the Lean files and the sources, and looks for mismatches, quantifier errors, vacuity,
   degenerate parameters, wrong cost accounting and classical/PQ overclaims. Its findings are
   advisory. `goal review --dir DIR` runs the mechanical checks (schema, local `dag_verify`, the
   digest) and writes `review.md`, the packet for the user.
5. **Approval.** The controller computes the bundle digest (`sha256` over the sorted
   `(path, sha256(content))` of every file under `DIR/dag`). The user approves with
   `goal approve --dir DIR --digest HEX`, which **requires an interactive terminal** (the user runs
   it, for instance with `!` in Claude Code); an agent's shell has no terminal and cannot approve.
   Any change of a file changes the digest and voids the approval.
6. `goal register --dir DIR` publishes exactly the approved bytes in one administrative PR (ready
   for review). Research may start immediately on the published PR (section 7.4).

New assumptions (Design AI) follow `sigaba-research`'s `references/design.md`: a definition node tagged `assumption` and its
note; a premise on it needs a new goal over an extended registry, approved as above.

## 5. Tasks and PRs

### 5.1 Descriptor

```json
{
  "schema": "sigaba.task.v1",
  "task_id": "<uuid>",
  "goal": "<goal fingerprint>",
  "domain": "design",
  "operation": "deepen",
  "title": "Resolve the internal-node step",
  "scope": "Find a simulation or the exact missing property.",
  "deliverables": ["a proof or sketch", "a note with the exact obstruction"],
  "success": "a reduction, or an exact remaining obligation",
  "targets": ["theorem:..."],
  "related": [{"task": "<uuid>", "relation": "successor_of"}],
  "depends_on": [{"pr": 117, "head": "<sha>", "paths": ["dag/Definitions/Def_X.lean"]}]
}
```

`domain`: `design | cryptanalysis`. `operation`: `expand | deepen | organize` (v1.2 section 7).
`relation`: `successor_of | related | supports | tests_assumption | duplicate_of`. The descriptor
is immutable: a change of scope is a new task with `successor_of`. Owner, head, state and timing are
derived from GitHub and local state, never written in the descriptor.

### 5.2 PR lifecycle

- `task create` allocates the UUID, creates the worktree from the DAG's latest `main`
  (`~/.sigaba/worktrees/<repo-key>/<uuid>`, branch `research/<uuid>`), makes one empty commit
  (`Start research task <uuid>`; the only empty commit the protocol makes), pushes (to the DAG with
  write access, else to the user's fork) and opens a **draft** PR whose body carries the descriptor
  and the marker `<!-- sigaba-task-v1 <uuid> -->`. It then posts the **status comment** (the PR's
  first comment, marker `<!-- sigaba-status -->`). Retrying finds the PR by branch name; it never
  opens a second one.
- The task's commits are made by the controller from explicit path lists (`artifact propose`),
  only under `dag/`, only adding files, never `git add -A`, never a force push.
- `task ready` (D2) re-verifies the exact files against the current `main` and the records, refuses
  on a failed item or a missing import, and marks the PR ready. The gate then runs.
- After the gate: on `rejected`, the task goes back to draft (`task draft`), is fixed in the same PR
  and made ready again. Passing PRs of `automerge` authors merge through the merge queue.
- `task finalize --outcome O` writes the summary note (section 5.3), adds it as an artifact,
  posts the final checkpoint, and marks the PR ready, or closes it when nothing can be merged
  (`--close`). A closed or merged task is never reopened for new scope: a successor task gets a new
  PR.
- One task owns one PR. Administrative PRs (goal registration, environments, maintenance) have no
  task.

States (derived, operational only): `planned` (local, no PR), `active` (draft PR, being worked),
`paused`, `blocked` (reason recorded), `ready` (PR ready), `merged`, `closed`, `stale` (checkpoint
overdue). Outcomes: `verified_solution`, `verified_refutation`, `verified_partial`, `candidate`,
`handoff`, `inconclusive`, `duplicate`, `cancelled`, `infra_failure`. Mathematical status always
comes from records, never from a state or an outcome.

### 5.3 The summary note

`dag/Notes/task-<first 8 hex of uuid>-<slug>.md`, tag `research-summary`, `refs` = the goal note
(`note:goal-<fingerprint>`) and the nodes the task adds, plus one `sigaba-summary-v1` block
(`task_id`, `goal`, `outcome`, `pr`), followed by prose: what was established (with node names),
what was attempted, exact blockers, next steps. It is the only task record on `main`.

### 5.4 Gate (D1)

`templates/dag/.github/workflows/gate.yml`:

- `pull_request_target` types: `opened, synchronize, reopened, ready_for_review,
  converted_to_draft`;
- every job runs only for a `merge_group`, or for a PR that is not a draft;
- on `converted_to_draft`, the job `unqueue` (with the gate's App token) disables auto-merge and
  dequeues the PR; nothing else runs;
- the `merge` job re-reads the PR and enables auto-merge only if it is still not a draft and its
  head is the verified commit.

A skipped required check on a draft cannot merge it (GitHub never merges drafts), and the merge
queue runs the full gate again on the merged candidate.

## 6. Plans and candidates

**Plan** (`sigaba-plan-v1`): `plan_id`, `goal`, `target` (`{"kind": "goal"|"task", "id"}`),
`required` (a non-empty list of distinct task UUIDs: the AND group), `rationale`,
`supersedes_plan`. Plans with the same target are OR alternatives. A plan is posted as a comment on
the proposer's own task PR (`plan add`) and never edited; a revision is a new plan. The research
graph is rebuilt by `sync` from all plan comments: required members that no task PR declares are
unresolved; plans that would close a cycle (target reachable from a member) are dropped in order
of `plan_id` and reported. A plan is structure, not mathematics: no goal is solved because all
members are merged.

**Candidate** (`sigaba-candidate-v1`): `candidate_id`, `goal`, `kind`
(`construction | attack | proof_route | generalization`), `task`, `parents` (candidate IDs),
`refs` (DAG references or `pr:<n>@<sha>:<path>`), `open_obligations`, `description`,
`obstructions`. Posted as a comment (`candidate add`), never edited; a new version is a new
candidate with `parents`.

## 7. The controller and the orchestrator

### 7.1 Local layout

`SIGABA_HOME` (default `~/.sigaba`; `--home` overrides):

```
repositories/<repo-key>/        controller's clone of the DAG (origin = DAG, fork remote if any)
worktrees/<repo-key>/<uuid>/    one git worktree per task
bases/<repo-key>/               a clean worktree at the DAG's main (the --dag of dag_verify)
records/<repo-key>/             a worktree of the records branch
authoring/<uuid>/               private authoring bundles
scratch/<uuid>/                 a task's private experiments and TMPDIR
state/research.sqlite           runs, tasks, queue, episodes, progress, events, outbox, cache
state/tasks/<uuid>/             progress records, artifact lists, verification results
state/runs/<uuid>/              run config, controller log, worker logs
```

`<repo-key>` is `github.com__<owner>__<repo>`. Paths are resolved and must stay under the home;
symbolic links in the layout are refused. Local builds use `dag_verify.py`'s cooperative layout
(D6): this checkout's core and its `.lake/packages`. Final trust is the gate and
`sigaba_neo.py check`.

### 7.2 Queues and episodes (`round_robin_v1`)

- One FIFO per `(domain, operation)` pair, the pairs in lexicographic order, one persisted cursor.
  Items are ordered by enqueue sequence, then task UUID. The dispatcher skips empty queues and
  queues whose head is blocked, dispatches one item, and moves the cursor past that queue.
- An item is a task (existing, or a proposal that becomes a task, with its draft PR, just before
  its first dispatch). A task has at most one live episode.
- An episode gets `min(episode_seconds, remaining run budget, max_worker_seconds)`. At its end the
  controller records the outcome, stores the worker's result, checkpoints, and puts the task back at
  the tail of its queue unless it finished, paused or blocked. Quota, network and provider failures
  pause with backoff and do not count as failed mathematics.
- **Derived work.** `sync` reads the index's `open_leaves` of the goal's targets (only accepted
  sketches have leaves) and enqueues one `deepen` proposal per leaf, deduplicated by
  `(goal, domain, operation, leaf)`; a leaf already covered by an active task PR is skipped.
- **Semantic proposals.** The orchestrator proposes work only when the queues have nothing
  eligible, at run start, or after a frontier change (`work propose --file`), at most
  `max_proposals` items per call; malformed, duplicate or out-of-scope proposals are rejected.

Public writes (pushes, PRs, comments) use the user's GitHub login; they are governed by the agent
runtime's own permission prompts and by GitHub's permissions, with no separate authorization step
(D11). Defaults (`run start` flags): `max_parallel_workers 3`, `checkpoint_seconds 600`,
`episode_seconds 1800`, `falsification_seconds 180`, `max_run_seconds 14400`,
`retry_backoff_seconds 60`, `max_proposals 6`, `grace_seconds 600`.

### 7.3 Workers

A worker gets: the task descriptor, the goal, its worktree and scratch directory, a budget, a
handoff packet (latest checkpoint, open obligations, candidates) and the worker prompt
(`.claude/skills/sigaba-research/references/worker.md`). It:

1. works only in its worktree and scratch directory, following its domain's reference
   (`design.md` or `cryptanalysis.md`);
2. writes Lean files under `dag/` in its worktree and verifies them with `task verify`;
3. records semantic progress with `progress record --task ID --file F`
   (`{"established": [...], "attempted": [...], "blockers": [...], "next_steps": [...],
   "artifacts": [...]}`) whenever the mathematical state changes, and before it yields;
4. lists the files to publish with `artifact propose --task ID PATH...`;
5. never runs `git push`, `gh pr ...` or edits another task; it may read other PRs as text.

It distinguishes verified facts, conjectures, heuristics and failed attempts. A failed proof search
is not a counterexample. **Falsification first**: before a long proof of a new central claim, it
spends at most `falsification_seconds` looking for a counterexample (small cases, boundary
parameters, `decide` on finite instances), and records the result (`attempted`, `cached`,
`unavailable`, `skipped`) in its progress.

Execution modes:

- **interactive**: the orchestrator delegates to native subagents (Claude Code `Agent`, Codex
  subagents). The watchdog still checkpoints on time; it cannot interrupt a subagent.
- **supervised**: `run start --backend claude|codex` starts each episode as a CLI session
  (`claude -p --output-format stream-json`, `codex exec --json`), with its working directory set to
  the worktree, and terminates it at the deadline.

### 7.4 Using unmerged work

Any PR a collaborator can read may be read, cited and used for exploration before review or merge.
A task that relies on another PR's files records them in `depends_on` with the exact head SHA. It
copies nothing of that PR into its own commits. To build locally against them it may fetch them
(`pr fetch --pr N`, into `state/tasks/<uuid>/deps/<n>/<sha>/`, source files under `dag/` only)
and pass them to `task verify --with-deps`. A dependent task stays a draft until its imports exist
on `main`; `task ready` refuses otherwise. If the other PR changes or closes, the task keeps the
pinned SHA and the next checkpoint reports it.

### 7.5 Goal-result cache

`cache lookup --theorem NAME` answers from the records (the theorem's status and accepted
solutions per environment, by semantic ID) and from local attempt history (`cache record`).
Failed or timed-out attempts are advisory and never make a statement false. Nothing is reused
without the gate and the check.

## 8. Checkpoints and liveness (D8)

The watchdog (`run start` spawns it; `watchdog` runs it in the foreground) keeps a monotonic timer
per active task. Every `checkpoint_seconds`, and immediately on pause, resume, block and finalize,
`task checkpoint` does, without any model call:

1. assembles the checkpoint from the latest progress record (with its own timestamp; marked
   `stale_report` when no fresh one arrived since the previous checkpoint) and machine facts
   (head SHA, changed files, last verification statuses, usage, episode, state);
2. if an artifact list was proposed and its files pass `task verify` byte for byte, commits exactly
   those files and pushes (no empty commits);
3. posts a **new** comment with the `sigaba-checkpoint-v1` block, marker
   `<!-- sigaba-checkpoint <task> <run> <sequence> -->` (idempotent: a marker already present is
   not posted again);
4. **edits the status comment** so it contains only the latest state: state, last checkpoint
   time, one-line summary, established results, blockers, next steps, open dependencies.

Failed remote writes go to the outbox and are retried with backoff. A heartbeat never invents
progress. In supervised mode a worker without a report or file activity for one grace period after
the deadline is marked stale and interrupted; its edits are kept.

## 9. Index (D9)

`dag_tools.py index` adds `goals`: for each goal note, its fingerprint, contract, the status of
each target in each environment (with `open_leaves`), and the summary notes that refer to it.
`INDEX.md` lists them. `sync` adds what CI cannot see (draft PRs, descriptors, plans, latest
checkpoints) into the local database; `task list`, `goals show`, `graph` read it.

## 10. Hooks and automation

`hooks install --provider claude|codex` writes command hooks into the **project's** settings of the
worktree (`.claude/settings.local.json`, `.codex/hooks.json`); it never touches global settings and
keeps unrelated hooks. Events (`SessionStart`, `PostToolUse`, `Stop`, `SubagentStop`) run
`sigaba_research.py hook --event E`, which reads the hook's JSON on standard input, binds it to a
registered task by its working directory, appends an event, and on `Stop` queues an immediate
checkpoint. Hooks are hints; the watchdog is the clock. Without hooks the watchdog and the
supervised runner do the same.

## 11. Commands

`python3 python/sigaba_research.py [--home DIR] [--repo OWNER/NAME] COMMAND`; JSON on standard
output; exit 0 on success, 2 on usage/protocol errors, 3 on permission, 4 on network/provider, 5
on verification failure.

| Command | Does |
| --- | --- |
| `doctor` | checks git, gh auth, repository permission and fork, the core build, providers |
| `sync` | fetches `main` and `records`, reads PRs, descriptors, plans, checkpoints |
| `goals list` / `goals show FP` | goals on `main` and pending goals / one goal with targets' statuses and tasks |
| `goal prepare --file CONTRACT [--dir DIR] [--distinct REASON]` | authoring bundle with the goal note; returns an existing goal, refuses overlaps |
| `goal review --dir DIR` | mechanical checks and the review packet |
| `goal approve --dir DIR --digest HEX` | records approval (terminal only) |
| `goal register --dir DIR` | publishes the approved bundle as an administrative PR |
| `task create --file DESCRIPTOR` | worktree, branch, draft PR, status comment |
| `task list` / `task show ID` | local and remote state |
| `task verify ID [--with-deps]` | `dag_verify.py` on the task's added files |
| `artifact propose ID PATH...` | the files to publish |
| `progress record --task ID --file F` | a semantic progress record |
| `task checkpoint ID` / `checkpoint-due` | one checkpoint / all due checkpoints |
| `task ready ID` / `task draft ID` | mark ready (after verification) / back to draft |
| `task finalize ID --outcome O [--close]` | summary note, final checkpoint, ready or close |
| `task pause ID` / `task resume ID` | pause or resume, with a checkpoint |
| `plan add --task ID --file F`, `candidate add --task ID --file F` | post a plan / candidate |
| `pr fetch --task ID --pr N` | pinned source files of another PR |
| `work propose --file F`, `work derive --goal FP`, `work list` | the queues |
| `run start ...`, `run status`, `run stop`, `run tick` | runs, dispatch, watchdog |
| `episode start ID` / `episode end ID --outcome O` | interactive episode bookkeeping |
| `cache lookup --theorem N`, `cache record ...` | goal-result cache |
| `hook --event E`, `hooks install --provider P` | hooks |
| `skills sync` / `skills check` | copies `.claude/skills/` to `.agents/skills/` / lists differences |

## 12. Skills

`.claude/skills/` is the one source (Claude Code reads it): `sigaba-research` (entry point, with
`references/`, including the two research domains `design.md` and `cryptanalysis.md`),
`sigaba-dag` and `sigaba-problem-author`. `skills sync` copies them to `.agents/skills/` (Codex's discovery path, at
the same depth, so relative links work in both); the copy is checked in and a test checks it is
equal.

**Plugin.** The same skills ship as one plugin, `sigaba-neo`, for both providers: `plugin/`
holds `.claude-plugin/plugin.json` (Claude Code), `.codex-plugin/plugin.json` (Codex), the skills
(`plugin/skills/`, generated by `skills sync` with commands and links rewritten for an installed
core), `core.json` (the core's URL and pinned revision) and the launcher `scripts/sigaba`. The
repository is the marketplace for both (`.claude-plugin/marketplace.json`,
`.agents/plugins/marketplace.json`). `scripts/sigaba install` clones the pinned core into
`~/.sigaba/releases/<sha>/`, builds it, points `~/.sigaba/core` at it and writes the shim
`~/.sigaba/bin/sigaba`, which runs the controller; `upgrade` and `uninstall` keep state and
worktrees. The plugin installs no hooks: hooks are per task worktree (section 10). The entry skill routes a new primitive to
the problem-author flow, an existing goal to discovery, and research to the orchestrator loop, and
calls the controller for every mechanical step.

## 13. Security

As v1.2 section 13, restricted by D3 and D6: hostile text is data; no credentials or transcripts in
public records; workers get no GitHub write path except the controller's commands; approvals need a
terminal; the gate and `check` stay the only verification; no new trusted code.

## 14. Tests

`python/tests/test_research.py` covers, with a fake GitHub and git runner and a fake clock: goal
fingerprints and the precheck of goal notes; approval digests and the terminal rule; task creation,
idempotent recovery, one PR per task; checkpoints every period, marker idempotence, the status
comment holding only the latest state, heartbeats without new progress, the outbox; publication of
exactly the proposed and verified bytes; round-robin order, persistence across restarts, derived
work from open leaves and deduplication; plans with alternatives, unresolved members and cycles;
ready refusal on missing imports; finalize; hooks binding by directory; skill copies equal; the
gate workflow's draft conditions; the index's goals.
