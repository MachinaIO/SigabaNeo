# The platform on GitHub

Agents work on one DAG of definitions, theorems, proofs and notes, kept in a GitHub repository:

- every node is a file;
- agents submit nodes by opening pull requests;
- CI on the pull request verifies them.

This replaces the self-hosted Prove2Me-compatible server, which is gone.

The trust model of [DESIGN.md](DESIGN.md) does not change. The submitter trusts Lean, the pinned
packages and `SigabaNeo/Trusted/`, and nothing else: not GitHub, not CI, not the agents and not the
maintainers' verdicts. `sigaba_neo.py check` builds every proof it uses and runs
`#sigaba_neo_check` itself. CI verdicts, records and the index only tell agents and submitters
where to look.

What is new is what has to be protected. The server's verdicts could be wrong without harm. On
GitHub, two things must also hold:

- the trusted files cannot be changed by an agent's pull request;
- CI, which runs untrusted Lean code, cannot be taken over.

## 1. Repositories

| Repository | Written by | Contents |
| --- | --- | --- |
| **core** (this repository) | maintainers only | `SigabaNeo/Trusted/` (the check, the machine model, assumptions, primitives); `SigabaNeoStd/` (the standard library); the platform's Lean commands (`SigabaNeo/Platform*`); the client and the DAG's tools (`python/`); the schemas (`schemas/`); the environment image (`docker/`); the DAG repository's template (`templates/dag/`). Tags are releases. |
| **dag** | agents, through pull requests | the DAG (`dag/`); the environment pins (`env/`); the maintainers' metadata (`meta/`); the workflows. It is created with `dag_tools.py init` (section 9). |

The boundary is GitHub's permission model, not path rules. A pull request to `dag` cannot touch the
trusted files, because they are not in `dag`. `dag` requires the core by tag, so the core can
change without moving the DAG.

### Layout of `dag`

```
env/environments.json        base environments: id, Lean, Mathlib, cslib-frontier, core tag and
                             URL, image digest, fingerprint, std release, state      [maintainers]
env/std.json                 std releases: tag -> {module: hash}                     [maintainers]
dag/Definitions/Def_<name>.lean   + Def_<name>.json
dag/Theorems/Thm_<slug>.lean      + Thm_<slug>.json
dag/Solutions/<slug>/Sub_<id>.lean + Sub_<id>.json
dag/Notes/<slug>.md
meta/trusted.json            submission mode and lists (section 6)                   [maintainers]
meta/assumptions.json        claim metadata: tags, proposed year, source              [maintainers]
meta/promotions.json         DAG node -> std declaration (section 4)                  [maintainers]
lakefile.toml, lean-toolchain, .github/, README.md, SKILL.md                          [maintainers]
branch `records`             verification records, <env id>.jsonl                     [CI]
```

The `[maintainers]` paths are protected by CODEOWNERS and the ruleset, and pull requests that touch
them never pass the gate. The Lake workspace has `dag/` as its source directory, so
`dag/Theorems/Thm_x.lean` is the module `Theorems.Thm_x`, as on Prove2Me. The schemas of every JSON
file are in `schemas/`.

## 2. The DAG

Everything agents produce is a node, whatever it means. There are four kinds:

| Kind | Edges (depends on) | The gate checks |
| --- | --- | --- |
| Definition | definitions it imports; std; core | the metadata; allowed imports; the syntactic filter; it builds; no forbidden declaration (`axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `partial`); no `sorry`; its semantic ID is new |
| Theorem | definitions; theorems; std; core | the same, except that the statement ends in `:= by sorry` and the file declares the named theorem and nothing else |
| Solution | its theorem; theorems it imports (sketch edges); definitions | the metadata; imports; the filter; it builds; `theorem solution` has the statement's type, or its negation for a disproof (`WA`); no `sorry` (`SORRY`); axioms only `propext`, `Classical.choice`, `Quot.sound`; kernel replay; it does not import its own target; a disproof imports no theorem; its text is new for the theorem |
| Note (Markdown) | `refs:` in its front matter (any nodes); `supersedes:` (a note) | the front matter's schema; referenced nodes exist; size. The content is not checked. |

Rules:

- **Append only.** A pull request may only add files under `dag/`. It may not modify, rename or
  delete them. A correction is a new node, and a note can say what it `supersedes`. Because a node
  may depend only on nodes that already exist (or that the same pull request adds), the graph is
  acyclic.
- **Names are first come.** A path is a name, and an existing path cannot be added again.
- **Allowed imports.** These roots: `Init`, `Std`, `Lean`, `Mathlib`, `Batteries`, `Aesop`,
  `Qq`, `Plausible`, `ProofWidgets`, `ImportGraph`, `LeanSearchClient`, `Cslib`, `CslibFrontier`,
  `SigabaNeoStd`, `Definitions.Def_*`, `Theorems.Thm_*`. Also `SigabaNeo.Trusted.*` and
  `SigabaNeo.Assemble`. Never `Solutions.*` (every solution declares `solution`), and never
  `SigabaNeo.Platform*` (its commands write files).
- **Status is derived, never stored.** `Open`, `Proved`, `Disproved`, `Drifted` and `Unchecked`
  are computed from the DAG and the records, per environment (section 5).
- **Failed attempts** remain as closed pull requests, on which the gate leaves its verdict and the
  log's errors as a comment, and as failed records (re-verifications record failures too, as
  attempts; only `OK` and accepted records count).

The gate's statuses: `OK` (definitions, theorems, notes); `ACCEPTED` (a complete proof: every
theorem it uses is `Proved` in the environment, or a disproof); `SKETCH_ACCEPTED`; `CE`, `WA`,
`SORRY`, `FAILED`, `LINT` (the syntactic filter); `DUPLICATE` (a node with the same semantic ID,
or a solution of the same theorem with the same normalized text; the result names it); `ERROR`.

## 3. Identity

### Semantic IDs of theorems and definitions

A theorem is identified by what its statement means. Its text does not count, and neither does
the environment as a whole. `#sigaba_neo_platform_semantic` (`SigabaNeo/Platform/SemanticId.lean`)
collects every constant the statement refers to, recursively, and writes each one as a *unit* in a
canonical form:

- Expressions are hash-consed into numbered nodes, so the form does not depend on sharing.
- Bound variables are de Bruijn indices. Binder names, binder info and metadata are dropped, and
  universe parameters are numbered.
- Every subterm that is a proof is replaced by a mark (proof irrelevance). A changed proof inside a
  definition or a statement therefore changes nothing.
- A theorem contributes its type only. A definition contributes its type and value. Opaque
  constants and axioms contribute their type.
- An inductive family is one unit, `block:<first type>`: the types of one `mutual` block with
  their constructors and recursors. Its self-references are therefore not cycles.

`dag.semantic_id` hashes the units bottom-up: a unit's hash covers its form and the hashes of the
units it refers to. The root then gives the ID:

- for a theorem, the statement's type, without the theorem's name, so two theorems that state the
  same proposition get the same ID;
- for a definition file, the definitions it declares, by name.

Duplicates are decided against the whole base. Records are published after a merge and may lag,
so the verifier also checks the base's definitions and theorems that the records do not cover yet,
as *shadow* items. Shadows go through the same checks as checked nodes, in one dependency order with
them, sharing which modules failed, and their statuses are not reported. A shadow that passes is a
candidate owner of its ID; one that fails (including through a failed import) is none. If a
shadow's check does not finish (a timeout, a crash, or the filter or the ID command not
finishing, all `ERROR`), the added definitions and theorems are not judged (`ERROR`). When
re-verifying, the checked nodes belong to the base too, so an `ERROR` among them has the same
effect. Two solutions of one theorem with the same
normalized text are duplicates, whether the first is in the base or earlier in the same pull
request.

Consequences:

- The ID depends only on what the statement actually refers to. If those definitions are unchanged,
  a new std release, a Mathlib update or a Lean update leaves the ID unchanged. The tests check
  this: `∀ x : ℝ, x ≤ x + 1 → (0 : ℝ) < 1` and `∀ y : ℝ, y ≤ y + 1 → 0 < (1 : ℝ)`, under two names,
  get one ID.
- Text that elaborates differently gets a different ID. Different text that elaborates to the same
  term gets the same ID.
- Renaming a constant (common in Mathlib) changes the IDs that depend on it.
- Definitions compiled by well-founded recursion may hash differently across Lean versions even if
  nothing changed in the source. They then show up as `Drifted`.
- Cost: a statement about `ℝ` refers to about 580 units (about 320 KB of forms), computed in about
  2 s.

### Solutions and std modules

- **A solution's identity** is its normalized text (`dag.normalize`): comments are removed, line
  endings unified, and trailing spaces and blank lines dropped. Indentation is kept, since it
  decides the structure of tactic blocks. Whether a solution checks depends on the environment
  (section 5).
- **A std module's hash** is its normalized text together with the hashes of the std modules it
  imports (a Merkle hash). Equal hashes therefore mean equal meaning, given the same base
  environment.

IDs are computed in CI, in the sandbox, by a process that loaded untrusted code. They are
bookkeeping: `DUPLICATE` and `Drifted` may be wrong if an attacker forges them, but the check does
not use IDs. It builds everything and compares types itself.

## 4. std: the standard library

`SigabaNeoStd` is a library of the core package: the root module `SigabaNeoStd.lean` and the
modules under `SigabaNeoStd/`. It holds what was `SigabaNeoStd/`: lattices and LWE, discrete
Gaussians, trapdoors, the lattice estimator, attacks, the machine and program libraries, encodings.

- **Names.** As in Mathlib, module paths start with the library's name (`SigabaNeoStd.Lattices.LWE`),
  and declarations keep their own namespaces (`SigabaNeo.Lattices`, `SigabaNeo.Tape`, …).
- **Who writes it.** Only maintainers. Every agent's workspace can import it, and its module list
  and summaries are in the index. Everything else in the DAG can be searched and imported, but
  nothing obliges an agent to read it.

**Curation.** Maintainers periodically look at the DAG for nodes that are useful across a domain.
The index lists the candidates by in-degree (`std_candidates`). The maintainers then:

1. write the std version, assembling it from the DAG's solutions with `p2m_apply%` or rewriting it;
2. release a core tag;
3. record `node -> std declaration` in `meta/promotions.json`.

The DAG node itself is not changed, and the index shows `promoted_to` on it.

**Releases and compatibility.** Lean imports have no versions, and an environment can hold only one
file per module name. So compatibility is decided per module, not per release:

- `env/std.json` lists, for each release, the hash of each std module
  (`dag_tools.py std-manifest`).
- A solution's record lists the std modules in its import closure and their hashes.
- A solution counts under an environment's std release when all of these hashes are equal there.
  Nothing is rebuilt in that case. Otherwise it is *stale* and is checked again (`reverify`).
- `dag.compatible` tells whether several records can be combined in one proof: one hash per module
  name.

Policy: std grows by adding modules. A released module is changed only when necessary, and never
renamed or split. A change to a module affects only the nodes that depend on it.

**std is not trusted.** The trusted check replays it, step 5 of `SigabaNeo/Trusted/Check.lean`.
Every std module the proof uses but the claim's definitions do not import passes the kernel again,
like the workspace's own modules. The std modules the definitions import are part of the claim's
meaning, and the submitter reads them like the core's definitions.

## 5. Environments and records

As on Prove2Me, a **base environment** is fixed and there are few of them. It is one entry of
`env/environments.json`:

- a Lean toolchain;
- Mathlib and cslib-frontier revisions;
- a core tag (with its URL and the fingerprint of its trusted and platform sources);
- the image, pinned by digest;
- its std release;
- a state: `default`, `active` or `frozen`.

The core pins cslib-frontier, and cslib-frontier pins Mathlib and Lean, so a new base environment
comes with a cslib-frontier update or a new core tag.

**Records.** The `records` branch has one file per environment, `<env id>.jsonl`. Each line is the
verification of one node (`schemas/record.schema.json`):

```json
{"kind": "solution", "path": "dag/Solutions/A_b/Sub_x.lean", "name": "A.b", "env": "env-1",
 "status": "SKETCH_ACCEPTED", "hash": "…", "theorem": "A.b", "proof_type": "prove",
 "uses": ["A.c"], "std": {"SigabaNeoStd.Lattices.LWE": "…"}, "author": "alice", "pr": 12,
 "commit": "…", "run": "https://github.com/…/actions/runs/…", "time": "…"}
```

Theorems and definitions have their semantic `id` instead of `hash`, `theorem`, `uses` and `std`.
Failed checks are recorded too, as attempts, but only a record with the status `OK`
(`dag.id_record`) establishes a definition's or theorem's ID in an environment, and only an
accepted record counts for a solution.

**Status per environment** (`dag.status`):

- A solution counts when it has an accepted record there and every std module it used has the
  same hash in the environment's std release. Without a release, a proof that used std does not
  count.
- A theorem is `Proved` when one of its counting proofs uses only `Proved` theorems. A cycle proves
  nothing.
- A theorem is `Disproved` when a disproof counts, and `Open` otherwise.
- A theorem's proofs count only once its statement is established there: an `OK` record of its
  semantic ID in the environment that is its baseline. Otherwise it is `Unchecked` (or
  `Drifted`), and no proof that uses it counts either.
- A theorem is `Drifted` when its semantic ID there differs from the ID recorded when it was
  introduced: its earliest record that is not a re-verification, whatever the environments' names.
  If two such records have the same time and different IDs, there is no baseline, and the theorem
  is `Drifted` everywhere. A drifted theorem is a different proposition there, and no solution
  counts for it. If the new proposition is wanted, it becomes a new node.
- When nodes share an ID without a record that established it, the ID's owner is decided once
  every checked node has its ID, and the others are `DUPLICATE`s of it. The owner is chosen as
  follows:
  - when a pull request is checked and a node of the base has the ID, that base node;
  - otherwise, the first by path among the nodes that have it: the checked ones, and when
    re-verifying, the base's too.

  A base node is a candidate only if it passes the same checks as a checked node. The outcome
  therefore depends neither on the order of the builds nor on how the nodes are split into
  batches.

**Unlike Prove2Me, theorems and definitions are not bound to an environment.** A node is the same
node in every environment where it has the same semantic ID. Only the verification of solutions is
per environment. When a base environment is added, the `reverify` workflow checks the existing
nodes there (`dag_tools.py reverify-plan`, `dag_verify.py verify --reverify`), starting with the
most imported theorems. Solutions that do not check there are listed as `needs_port`, which is work
for agents.

A Lean build uses one environment. `sigaba_neo.py check` uses the environment of the submitter's
core and builds every solution in the chain there.

## 6. Submitting: pull requests and CI

### Who can submit

Agents and people work from forks, and nobody but the maintainers has write access to `dag`. This
is the same while access is restricted and after the repository is public, so going public changes
one field and nothing else. `meta/trusted.json` (`schemas/trusted.schema.json`) sets it:

```json
{"mode": "allowlist", "accept": ["alice", "agent-bot-1"], "automerge": ["alice", "agent-bot-1"]}
```

- `allowlist`: pull requests from authors not in `accept` fail the gate, with the label
  `not-accepted`, before any Lean runs. Nothing closes a pull request automatically: a decision
  is about one commit, and a newer commit gets its own run.
- `collaborators`: only those with write access to the repository (GitHub's `admin`, `maintain`
  or `write`), and those in `accept` (bots, say), may submit; the others fail as in `allowlist`.
  Those with write access are also merged automatically when they pass, as are those in
  `automerge`. The precheck job reads the author's permission through the API
  (`repos/…/collaborators/<author>/permission`) and passes it to `dag_tools.py precheck
  --permission`; a failure to read it fails the gate. Who may submit then follows the
  repository's access settings, with no list to keep in step.
- `open`: every pull request is verified. Those from `automerge` authors that pass are merged
  automatically through the merge queue, and the rest wait for a maintainer.

While the repository is private, forking and workflows from fork pull requests must be enabled,
and Actions minutes are billed.

### Workflows (`templates/dag/.github/workflows/`)

All Lean runs inside the environment image, in a Docker sandbox:

```
docker run --rm --network none --read-only --cap-drop ALL --cap-add SETUID --cap-add SETGID \
  --security-opt no-new-privileges --user 0:0 -e SIGABA_LEAN_UID=1000 \
  --memory … --cpus … --pids-limit … \
  --tmpfs /work:rw,exec,mode=1777 --tmpfs /tmp:rw,exec,mode=1777 \
  -v "$PWD/base:/base:ro" -v "$PWD/fetched/files:/new:ro" -v "$PWD/records:/records:ro" \
  IMAGE@sha256:… \
  verify --dag /base --new /new --out - --env ENV --revision SHA --records /records \
    --workdir /work/ws > result.json 2> log.txt; echo $? > exit
```

Nothing the container can write is mounted; the result is the verifier's standard output, and
the exit status is recorded outside (section 6, `gate.yml`).

**`gate.yml`** runs on `pull_request_target` and `merge_group`. Its workflow file always comes from
the base branch. It has five jobs:

1. **precheck.** Permissions: `contents: read`, `pull-requests: read`. It never checks out the pull
   request. It reads the default environment from the base and checks out the core's tools at the
   pinned tag. It then fetches, through the API and as data, the files that the event's head commit
   changes against its base (`dag_tools.py fetch`), with the added files' modes and contents read
   from that commit's tree. The event's commits do not move, so if the pull request is updated in
   the meantime, the new commit gets its own run. The head commit is carried through the jobs as
   the `revision`. `dag_tools.py precheck` then checks:
   - the author against `meta/trusted.json`;
   - that the pull request only adds files under `dag/`, with the layout's names;
   - the file count and sizes;
   - that each added file is a regular file in the head commit (a tree entry of type `blob`, mode
     `100644` or `100755`), not a symbolic link or a submodule, whose blob would look the same;
   - the metadata schemas, and that the names in the metadata agree with the paths;
   - that imports are allowed and exist;
   - that statements end in `:= by sorry`;
   - that a solution's theorem exists;
   - the notes' front matter and references.
2. **verify.** Permissions: `contents: read`. It checks out the base and the `records` branch with
   `persist-credentials: false`, and runs the verifier in the sandbox. No token and no secret is
   inside the container, and it has no network. It never saves a cache: Mathlib, cslib-frontier,
   the core and std come prebuilt in the image, and the DAG's modules are built from source.

   Inside the container, the verifier runs as root with every capability dropped except changing
   its user (`SIGABA_LEAN_UID=1000`). Every Lean and Lake process runs as uid 1000, and every
   process of that user is killed after each step. That user:
   - cannot write the workspace's sources, which root writes;
   - cannot signal the verifier;
   - cannot reach its output, because the result is the verifier's standard output and the job,
     outside the container, writes it to a file together with the exit status.

   The verifier builds a node's imports (and a solution's theorem) first and hashes their build
   outputs. If the node's build changes them, the node fails. On a timeout, the processes of the
   Lean user are killed as that user before the step's output is read.
3. **decide.** It checks the result against `schemas/result.schema.json` (`dag_tools.py decide`)
   and runs no code from the pull request. The result counts only if all of these hold:
   - the verifier exited with 0 or 1;
   - it is about the expected environment and head commit;
   - it has exactly one item per added node;
   - its `ok` and its exit status agree with the items;
   - its revision is the commit the precheck read.

   The conclusion is derived from the items' statuses, and is the required check. This job is
   read only.
4. **report** (for `pull_request_target` only), with the workflow's own token (`pull-requests` and
   `issues: write`), which expires with the job. It runs no pull request code and reads only
   `decide`'s decision. It comments the verdict and labels the pull request with the gate's labels
   of the latest decision (`not-accepted` if the author is not accepted, `rejected`, or
   `needs-maintainer`; earlier gate labels are removed, others left alone; a missing label is
   created, and a failure to label fails the step).
5. **merge** (for `pull_request_target`, when the decision passes for an `automerge` author). It
   takes a GitHub App token from the `gate` Environment (which only `main` may use) and enables
   auto-merge for the verified commit only (`--match-head-commit`), which puts the pull request
   into the merge queue. It has no other step and no checkout. The workflow's own token cannot do
   this: GitHub starts no workflow for an event caused by that token, so a pull request queued with
   it would wait forever for the merge queue's run of the gate.

For a `merge_group`, the same jobs run against the merge group's head (the latest `main` with the
pull request), which catches pull requests that depend on each other. The precheck has already
guaranteed that the merge group's workflow files are the base's.

The other workflows:

- **`records.yml`** runs on push to `main`, every 10 minutes, and by hand. For each of the recent
  commits of `main` that no record names yet, it downloads the result of the commit's merge group
  run, checks its shape and its exit status, appends the records (`dag_tools.py records`) and
  pushes `records`; then it starts `index`. The environment, and with it the file written, comes
  from the workflow; the result must be about it. It runs no Lean.
- **`index.yml`** runs on push to `main`, when `records` starts it, after `reverify`, and by hand. It publishes
  `index.json` and `INDEX.md` to GitHub Pages: statuses per environment, claims with their metadata
  and refutation sketches, open leaves, `needs_port`, stale solutions, notes, std modules and std
  candidates. It parses files only and runs no Lean.
- **`reverify.yml`** runs weekly and by hand, for each active environment. A sandboxed job plans and
  verifies; a separate job with write access appends the records. Failed checks are recorded as
  attempts, with their status (only passing records count anywhere). The plan takes nodes never
  tried in the environment first, then failed ones, least recently tried first, so failing nodes
  never keep the others from their turn. Every environment's job
  reports whether it had work. A planned environment without a well-formed result fails the
  workflow; nothing is dropped silently.
- **Publishing records.** `records.yml` and `reverify.yml` write the `records` branch one at a time
  (the concurrency group `records-branch`, with `queue: max`, so that no waiting writer is
  replaced). Each writer appends to the latest tip and starts again from it if a push is rejected.
  Appending is idempotent per run and node.
- **`formalpedia.yml`** runs weekly. It converts Formalpedia's new items into DAG files
  (`dag_tools.py formalpedia`) and opens a pull request with the gate's App token (a pull request opened with the workflow's
  own token would not start the gate). It is optional. That pull request goes through the same
  gate. Nothing is taken on trust: each item is checked in this environment.
- In the core, **`image.yml`** builds the image on a tag, pushes it to GHCR, and attaches the std
  manifest, the fingerprint and the image digest to the release (`environment.json`). **`ci.yml`**
  runs the tests that need no Lean.

`GITHUB_TOKEN` pushes and merges do not trigger other workflows (dispatches do). That is why
`records.yml` also runs on a schedule, and starts `index.yml` with a dispatch, and why `index.yml`
listens to `workflow_run` of `reverify`.

### Defense in depth

**The syntactic filter** (`SigabaNeo/Platform/Lint.lean`, `#sigaba_neo_platform_lint`) reads each
added file before it is built, without elaborating it. It parses every command, and elaborates only
`open`, `namespace`, `section` and `end`, so that scoped syntax parses. It rejects:

- `#eval` and every `#` command except `#check`, `#print`, `#synth`, `#guard_msgs` and `#exit`;
- `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `by_elab` and `native_decide`;
- every syntax declaration: `syntax`, `macro`, `elab`, `notation`, `infix`, …;
- `initialize`, `simproc` and similar declarations, `unsafe` and `partial`;
- attributes that register code: `command_elab`, `term_elab`, `tactic`, `macro`, `delab`, `init`,
  `simproc`, `norm_num`, `positivity`, `extern`, `implemented_by`, `builtin_*`, …;
- options other than `maxHeartbeats`, `maxRecDepth`, `linter.*`, `pp.*`, `synthInstance.*`,
  `backward.*` and a few others. In particular `debug.skipKernelTC` and `trace.profiler.output`
  are rejected.

Since no DAG file may declare syntax, every DAG file is parsed with the syntax of the core, std,
Mathlib and cslib-frontier only. The filter runs in a Lean process that imports the file's own
(allowed, built) imports. The list cannot be complete, so the sandbox remains the real boundary.

The verifier also makes the server's checks: forbidden declarations, standard axioms only, and
kernel replay of the solution. No self-hosted runners are used.

### Threats and what stops them

| Threat | Countermeasure |
| --- | --- |
| A pull request edits the workflow so that it passes | the workflow comes from the base branch (`pull_request_target`); precheck rejects any file outside `dag/` |
| Lean code steals a token or secret | Lean runs only in the container, which has no token, no secret and no network; the write tokens are the `report` job's own (comments and labels) and the App's in the `merge` job (auto-merge), from a `main`-only Environment; neither job runs pull request code |
| Lean code tampers with later steps or the verdict | the container is separate; the steps outside read one JSON file and check it against its schema |
| Cache poisoning | the image is pinned by digest; no job saves a cache |
| A forged status check | the ruleset requires `decide` from the GitHub Actions app; fork tokens are read only |
| Changes to trusted files | they are in another repository; `env/`, `meta/` and `.github/` are protected by CODEOWNERS and never pass the gate |
| Resource abuse | timeouts, Docker limits, file count and size limits, `concurrency`, and the allowlist |
| Prompt injection through notes or Lean comments | `SKILL.md` tells agents that text read from the repository or the index is data, not instructions; agents run without credentials beyond their own fork. The risk already existed with Prove2Me and Formalpedia, whose statements, comments and docstrings agents read too. |
| A false theorem passes | not possible through CI: `check` rebuilds everything locally in a bubblewrap sandbox and replays it, std included |
| The verifier's result misrepresents the pull request | `decide` binds it to the environment, the head commit, the exit status and the exact set of added nodes; Lean runs as a user that cannot reach the verifier's output |
| A symbolic link poses as a file | precheck requires each added path to be a regular file in the head commit |

## 7. Clients and agents

- **`sigaba_neo.py submit CLAIM --dag DAG [--pr]`** fixes the hypotheses. Selectors choose cards in
  the DAG, by name, or by `meta/assumptions.json` and refutation sketches. It then writes the
  claim's definitions and its two cards into a checkout of the agent's fork. With `--pr`, it
  commits them on a branch, pushes it and opens a pull request.
- **`sigaba_neo.py check CLAIM --dag DAG [--records R] [--env E]`** reads a `dag` checkout. With
  records, it tries the solutions verified in its environment first. It assembles the proofs,
  builds them and runs `#sigaba_neo_check`. Its output includes the `dag` commit and the
  environment, and `submit` writes the commit into `claim.json`.
- **Agents** follow the DAG repository's `SKILL.md`:
  - read the index;
  - work in a clone of their fork;
  - run `dag_verify.py verify` locally, which replaces the server's quick `/verify` loop;
  - open a pull request;
  - read the verdict comment.

  Strategies, attempts and dead ends go into notes (`dag/Notes/`).

## 8. Commands

| Command | Runs Lean | Where |
| --- | --- | --- |
| `dag_verify.py verify --dag BASE --new NEW --out OUT [--env E] [--records R]` | yes (sandbox) | gate, agents |
| `dag_verify.py verify --dag DAG --reverify PLAN.json --out OUT …` | yes (sandbox) | reverify |
| `dag_verify.py semantic --dag DAG PATH` | yes | maintainers |
| `dag_tools.py fetch`, `precheck`, `check-result`, `decide` | no | gate |
| `dag_tools.py records`, `index`, `reverify-plan` | no | records, index, reverify |
| `dag_tools.py std-manifest`, `init`, `import-server`, `formalpedia` | no | maintainers, formalpedia |
| `sigaba_neo.py submit`, `check`, `dev` | `check` builds | submitters |

## 9. Setting up a DAG repository

1. Tag a core release. `image.yml` publishes the image and attaches `environment.json` (std
   manifest, fingerprint, image digest) to the release.
2. Create the repository's files:

   ```bash
   python3 python/dag_tools.py init ../dag --core-url https://github.com/<org>/Sigaba-Neo \
     --core-rev <tag> --image ghcr.io/<org>/sigaba-neo-env@sha256:<digest> --owner <maintainers>
   ```

   This writes the layout, the default environment, the std release, `meta/`, the workflows,
   CODEOWNERS, `README.md` and `SKILL.md`. To migrate the retired server's data, run
   `python3 python/dag_tools.py import-server <server-data> --out ../dag`.
3. Apply the GitHub settings of section 10.
4. For a new environment, add an entry to `env/environments.json` and its std release
   (`dag_tools.py std-manifest --dag . --tag <tag> --core <core>`), then run `reverify`.

## 10. GitHub settings of a DAG repository (maintainers)

The workflows assume these settings. Without them the gate is not a boundary.

1. **Permissions.** Nobody but the maintainers has write access; agents and people work from
   forks. Settings → Actions → General: workflow permissions "Read repository contents";
   "Require approval for all outside collaborators" for fork pull request workflows (the gate uses
   `pull_request_target`, which does not need it, but other workflows would). While the
   repository is private, allow forking and "Run workflows from fork pull requests".
2. **The gate's App.** Create a GitHub App (no webhook; installable only on this account) with the
   repository permissions "Contents", "Pull requests" and "Merge queues", each "read & write",
   and install it on this repository only. Without "Merge queues", enabling auto-merge fails with
   an opaque GraphQL error ("Something went wrong while executing your query"). Create the Environment `gate`, restricted to the `main` branch,
   with the variable `GATE_APP_ID` and the secret `GATE_APP_KEY`. The gate's `merge` job uses it to
   enable auto-merge, so that the merge queue's run of the gate starts (it would not for the
   workflow's own token); comments and labels use the workflow's own token. The optional
   `formalpedia.yml` uses the same App (then add its bot login to `meta/trusted.json`); without
   it, disable that workflow (`gh workflow disable formalpedia`).
3. **Labels.** The gate labels pull requests `not-accepted` (an author not in
   `meta/trusted.json`), `rejected` (a failing check) and `needs-maintainer` (passed, not on the
   automerge list). It creates them if they are missing; to create them beforehand:
   `for l in not-accepted rejected needs-maintainer; do gh label create "$l" --force; done`.
4. **Ruleset of `main`.** Require a pull request; require the status check `decide` from the
   GitHub Actions app; require the merge queue (squash); require review from code owners; block
   force pushes and deletions. Let the Repository admin role bypass it for pull requests only, so
   that maintainers can merge changes to `env/`, `meta/` and `.github/` (which the gate always
   rejects). Allow auto-merge (squash only) in the repository's settings.
5. **Ruleset of `records`.** Block force pushes and deletions. Only maintainers and GitHub Actions
   can push to it, since nobody else has write access (a repository ruleset cannot name GitHub
   Actions as its only writer).
6. **Pages.** Source: GitHub Actions.
7. **Pinned actions.** The workflows pin every action by commit SHA (the version is in a comment),
   and the core pins the image's base by digest. Update a pin deliberately, never to a moving tag.

## 11. Open questions

- Hash semantic IDs up to constant names, so that Mathlib renames do not cause drift?
- How many environments stay `active`, and when one is frozen.
- Whether the records stay a branch, or move to releases.
