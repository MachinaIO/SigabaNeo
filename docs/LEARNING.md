# Certified curriculum and collective learning

**Status:** implemented as of this revision, in two places:

- the **core** (this repository): the Lean side and the agent's client;
- the **DAG repository** (`DAG_REPO_URL`, the reference deployment is `MachinaIO/SigabaPark`):
  all of the CI that decides anything, in its own `ci/learning/` and `.github/workflows/`.

This document implements "SigabaNeo: Certified Curriculum and Collective Research Learning"
(proposed v1.0, 2026-11-28). It records the maintainers' decisions, the interfaces as built, and
the remaining deployment steps. Where they differ from the proposal, this document wins.

## 0. Decisions

| Decision | Effect |
| --- | --- |
| L1 CI lives in the DAG | The DAG repository verifies generators and notebooks in its own CI. Its logic is in `ci/learning/` there, not in the core. A pull request that changes `ci/`, `.github/`, `meta/` or `env/` fails both required checks, so only an administrator's bypass can merge it. |
| L2 Lean stays in the core | The trusted vocabulary (`SigabaNeo.Trusted.Benchmark`) and the commands (`SigabaNeo.Trusted.GeneratorCheck`) are core code. The DAG's CI runs them in the environment image, as it runs `dag_verify`. |
| L3 Authorization unchanged | `meta/trusted.json` keeps mode `collaborators`. Nothing grants access. Learning pull requests are never merged automatically: a maintainer merges them. |
| L4 Notebooks on `main` | The active notebook of a role is `notebooks/<role>.md` on the DAG's `main`. It changes only through an evaluated, merged notebook pull request; the activation record (compare-and-swap) is written after the merge. |
| L5 No paid inference by default | `meta/learning.json` has `evaluator.enabled = false`. Notebook comparisons stay `awaiting_evaluator` until a maintainer configures an authorized provider in the protected `learning-evaluator` Environment. |

Unchanged: the trusted check `#sigaba_neo_check`, the DAG gate's semantics for `dag/` nodes,
semantic IDs, statuses, goal approval and the research protocol ([RESEARCH_PROTOCOL.md](RESEARCH_PROTOCOL.md)).
A benchmark result never changes a registered assumption's strength. The adversary model is
classical.

## 1. Lean (core)

### 1.1 `SigabaNeo.Trusted.Benchmark` (definitions only, no axioms)

- `Seed k := Fin k → Bool`.
- `Family`: `Task`, an executable canonical serialization `encode`/`decode` with
  `decode_encode`, `Solvable`, `SameProblem`, and `sameProblem_equiv : Equivalence SameProblem`.
- `Certified F L k h gen`: `0 < L`, `h ≤ k`, and for every level `d` and seed `r`,
  `F.Solvable (gen d r)` and `2^h * Nat.card {s // F.SameProblem (gen d r) (gen d s)} ≤ 2^k`.
- `Target F bits`: the solver's statement for a sampled descriptor, `F.Solvable x` when
  `F.decode bits = some x`, and `False` otherwise.
- Design: `DesignAdapter` fixes a common comparison carrier (`Alg`, `sig`, `Params`, `prop`,
  `cost`, registry, pinned strengths, cap). It defines:
  - `AcceptDesign A x u := Spec (A.primitive x) A.registry u ∧ u.Valid A.strength ∧ u.N ≤ A.cap x`;
  - `SolvableDesign := ∃ u, AcceptDesign …`;
  - `SemanticAccept A x I := ∀ i, A.prop i (A.params x) I`;
  - `SameDesign x y := ∀ I, SemanticAccept x I ↔ SemanticAccept y I`, which compares accepted
    implementations rather than truth values. Since every generated task is solvable, comparing
    truth values would identify them all.
- Cryptanalysis: `AttackAdapter` defines:
  - `AcceptAttack A x M := 0 < gain ∧ cost ≤ 2^(bound x) · gain`;
  - `SolvableAttack`, which also requires `bound x < k` when the task claims to refute
    `HardAt k`;
  - `SameAttack x y := ∀ M, gain_x M = gain_y M`.

  `AttackAdapter.exists_acceptAttack_iff` is exactly `Assumption.Attack`, and
  `SolvableAttack.not_hardAt` refutes the claimed strength.

### 1.2 `SigabaNeo.Trusted.GeneratorCheck` (trusted commands)

Every expected statement is built from names and numerals as an `Expr`, never elaborated from
text. The only axioms allowed are `propext`, `Classical.choice` and `Quot.sound`. Workspace
modules, and std modules outside the family's import closure, are replayed in the kernel. Run each
command from the workspace's root: local modules are those built under `./.lake/build`.

| Command | Checks | Writes |
| --- | --- | --- |
| `#sigaba_generator_check "<module>" "<family>" "<generate>" "<certificate>" L k h` | the family is a core/std `Family` definition, not one declared in the workspace; `<certificate> : Certified <family> L k h <generate>` holds exactly | `generator-result.json` (`certified` / `rejected`) |
| `#sigaba_generator_sample "<module>" "<family>" "<generate>" L k level "<seed>" [hb]` | runs the compiled `encode (generate level seed)`, then has the kernel check `encode (generate ⟨level,_⟩ seed) = bits` | `sample-result.json` (`linked`, `descriptor`) |
| `#sigaba_generator_link … "<seed>" "<descriptor>" [hb]` | the same kernel check of a given descriptor, without running any generator code | `link-result.json` |
| `#sigaba_task_check "<module>" "<family>" "<bits>" "<theorem>" "<forbidden prefix>"…` | `<theorem> : Target <family> <bits>`; no module under a forbidden prefix (the generator's) is in the environment | `task-result.json` (`solved` / `rejected`) |

The DAG's runner accepts a descriptor only when a separate `link` process confirms the sampler's
output. The sampler process runs the generator's compiled code and could print anything.

### 1.3 `SigabaNeoStd.Benchmarks` (untrusted helpers, proven)

`Entropy.lean` holds the counting interpretation, so nothing ever enumerates the seed space.
Under a uniform seed, a class has probability `≤ 2^-h` (min-entropy) and two independent samples
collide with probability `≤ 2^-h`; this is entropy of the quotient by `SameProblem`, not a count
of techniques. It also holds the proof routes:

- `certified_of_injective`: injective modulo the equivalence;
- `diversity_of_recovery` / `certified_of_prefix`: partial seed recovery;
- `diversity_of_injection`: bounded fibers;
- `not_certified_const`: a constant generator is not certified for `h > 0`;
- `sameAttack_of_swap`: swapping real and ideal preserves every gain.

`Families/` holds maintainer-reviewed adapters. There are two bootstrap fixture families, honestly
labelled. They are not research benchmarks.

- `avoidDesignFamily`: implement an algorithm whose output is never the word `w`, within cost cap
  64.
- `avoidAttackFamily`: output anything but `w`, with cost at most `2^5 ×` gain, where the task
  claims 6 bits.

Both are solved by the explicit halting machine `Fixture.haltMachine` (cost 30), and their
diversity is proved with probe machines.

Metadata earns no entropy (L10): `DesignAdapter.sameDesign_of_params_eq`,
`AttackAdapter.sameAttack_of_problem_eq` and their `not_certified_of_params_const` /
`not_certified_of_problem_const` refuse a generator whose seeds only change caps, bounds, names or
other fields the propositions do not read.

`tests/generators/` and `python/tests/test_benchmark.py` hold valid fixtures for each role (one of
them multi-level) and negative fixtures. `Generators/Negatives.lean` proves, with the standard
axioms only, what the acceptance predicates refuse: `Spec` without the cap, a wrong
implementation and an inflated premise (L06); a zero-gain and a too-expensive machine, and an
unsolvable `c = k` task whose target is false (L07); cap-only and bound-only generators (L10). The negative fixtures cover:

- a constant generator;
- a wrong `h`, `L` or family;
- a family the generator declares itself;
- `sorry`, an extra axiom, and solvability proved for sampled seeds only;
- an `implemented_by` mismatch between compiled code and definition;
- a kernel timeout;
- a solver that imports the generator.

## 2. The DAG's CI (`ci/learning/`, workflow `learning`)

The records format is `ci/learning/RECORDS.md` in the DAG repository. The pull request types are:

| Type | Content | Check |
| --- | --- | --- |
| math | only `dag/` | `gate` (unchanged); `learning` passes |
| generator | one new immutable `generators/<role>/<family>/<id>/v<NNNN>/` with `manifest.json`, `Generate.lean`, `Certificate.lean` | `learning`: route, sandboxed build, `#sigaba_generator_check` with `L` from the manifest and `k`, `h` from the family's policy entry, then kernel-linked smoke samples; `gate` defers |
| notebook | exactly one of `notebooks/design.md`, `notebooks/cryptanalysis.md` | `learning`: paired screen (20 pairs), then an independent confirmation (100 pairs) against the active notebook. The test is the `cp-union-v1` lower bound: improvement if `LB > 0`; compression if the note is strictly shorter and `LB ≥ -0.05`. Without an evaluator: `awaiting_evaluator` |
| other or mixed | anything else | rejected by both checks (administrator bypass only) |

The route runs before anything is executed, and the author's admission comes first, as in the
gate. Drafts are skipped.

After a merge, the `learning` workflow:

1. re-certifies a merged generator at the merge commit, or activates a merged notebook with
   compare-and-swap on the incumbent's hash and the epoch (rollback and bootstrap need an
   administrator or maintainer);
2. appends the records to the branch `learning-records`;
3. publishes the static report to the branch `learning-report`. The report is self-contained:
   `index.html` with the eight required charts per role, `LEARNING.md`, `data.json` and CSV
   files.

Calibration and anchor assessments are manual `workflow_dispatch` runs.

## 3. The agent's client (core)

- `python/research/notebook.py`: when an episode starts, the controller pins the active notebook
  of the task's role from the DAG's `main`. It keeps the exact bytes, their SHA-256 and the size,
  enforces the policy's caps, and refuses symbolic links. The worker prompt carries the text as
  fenced data, and an event records the hash. A running episode never sees a later version.
- `python/research/learning.py`, used as `sigaba_research.py learning …`:
  - `doctor`;
  - `notebook show|propose --role R [--file F --rationale T --ready]`;
  - `generator publish --path DIR [--ready]`, which opens a draft pull request holding exactly
    the version's files;
  - `ci -- <command>`, which runs the DAG's own `ci/learning` CLI from its `main` checkout. Such
    a run is a local, untrusted preview, for example `ci -- sources --role R …` (DAG-driven
    source sampling) or `ci -- certify …`.

  The client never computes a score, a certificate or an activation.
- Skill: [`sigaba-research` › learning](../.claude/skills/sigaba-research/references/learning.md).

## 4. Deployment (maintainers)

1. Release the core with this change: tag it, and let the `image` workflow publish the
   environment image.
2. In the DAG, add the environment to `env/environments.json` and make it the default.
   Certification needs the commands of `SigabaNeo.Trusted.GeneratorCheck` in the image's core.
3. Merge the DAG's learning pull request with an administrator's bypass: it changes `ci/`,
   `.github/` and `meta/`. Then:
   - require the check `learning-decide` (the `learning` workflow's) next to the gate's
     `decide`, both from GitHub Actions. They are matched by job name, so the two jobs have
     different names;
   - let the merge queue build groups of one pull request (`max_entries_to_build` and
     `max_entries_to_merge` = 1). A group is checked as one change, so a learning pull request
     batched with a mathematical one would look mixed and fail both checks;
   - protect the branches `learning-records` and `learning-report`, and create
     `learning-records`;
   - create the Environment `learning-evaluator` with required reviewers.
4. Submit the bootstrap generators (one generator pull request each), whose families
   `meta/learning.json` already approves.
5. Only when a paid evaluation budget is authorized: designate the evaluator runner (the core
   built, the model's CLI installed; repository variable `LEARNING_EVALUATOR_RUNNER`), set
   `LEARNING_EVALUATOR_AUTHORIZED` and `LEARNING_EVALUATOR_CORE` in `learning-evaluator`, add a
   `local-cli` profile with `settings.solver: claude-code` and a budget, and set
   `evaluator.enabled`. The provider (`ci/learning/providers.py`) runs one solver program per
   trial in a fresh scrubbed directory under the profile's wall-clock limit; only the verifier
   scores, after the same source rules as generators. `scripted-fixture` is a model-free solver
   for the bootstrap families (pipeline tests).

## 5. Limits

- The bootstrap families are tiny and solved by one trivial machine. They exercise the pipeline;
  they measure nothing about research ability. Real families need maintainer review for vacuity
  and meaning, and the DAG has few complete Design or attack results to build generators from
  yet.
- Certified entropy is a lower bound relative to the approved equivalence and uniform seeds. It
  says nothing about the number of distinct techniques, and per-family bounds are never summed.
- Fresh seeds of public generators measure within-family learning only. Family-disjoint and
  future-family assessments are part of the record model, but need enough reserved families.
- The statistical rule is per comparison. Repeated adaptive testing is tracked, not corrected
  globally.
- The `claude-code` solver exists but has not been run here: no paid evaluation was authorized.
  Every real-Lean evaluation so far used the model-free `scripted-fixture` solver.

## 6. Acceptance tests (spec section 13)

Where each test lives. `core:` means this repository's `python/tests/`; `dag:` means the DAG's
`ci/learning/tests/`; `e2e` means a recorded end-to-end run with real Lean (section 7).

| ID | Covered by |
| --- | --- |
| L01 | core: `test_research`, `test_dag_tools`, `test_dag_verify`, `test_check`, `test_platform`, `test_client` (unchanged behavior); the gate only gains the defer step for learning paths |
| L02 | dag: `test_route` (admission first, nothing run for an unauthorized author); core writes stay maintainers-only |
| L03 | dag: `test_route` (mixed PRs; `ci/`, `.github/`, `meta/`, `env/` rejected) |
| L04 | dag: `test_route` (drafts skipped), `test_evaluate.test_head_and_epoch_staleness` |
| L05 | core: `test_benchmark.Certificates.test_valid`, `Solutions.test_good`; e2e |
| L06 | core: `test_benchmark.NegativeFacts` (`Generators/Negatives.lean`) |
| L07 | core: `test_benchmark.NegativeFacts`; synthetic results never touch `meta/assumptions.json` (no code path writes it) |
| L08 | core: `test_benchmark.Certificates` (`sorry`, extra axiom); dag: `test_route` (forbidden words, imports) |
| L09 | core: `test_benchmark.Certificates` (sampled-only, missing level, own family); dag: `test_route` (h from policy only) |
| L10 | core: `test_benchmark.NegativeFacts` (cap-only, bound-only), `sameAttack_of_swap` |
| L11 | core: `test_benchmark.Certificates` (constant at h = 8, prefix bound at h = 4 vs 8); dag: policy rejects `entropy_bits = 0` |
| L12 | core: `test_benchmark.Certificates.test_levels`; dag: `test_report` (diversity never summed) |
| L13 | core: `test_benchmark.Sampling`, `Linking`; dag: `test_certify` (determinism, link required) |
| L14 | dag: `test_certify.test_sample_failure_never_replaced`, `test_evaluate.test_generation_error_no_replacement`, `test_stats` (sampling) |
| L15 | dag: `test_records_cli` (`sources`) |
| L16 | core: `test_research.Notebooks`; dag: `test_route` (caps, UTF-8) |
| L17 | dag: `test_evaluate.test_full_pass_family_disjoint` (same task per pair, separate sessions) |
| L18 | core: `test_benchmark.Solutions` (generator import forbidden); dag: solver source scan before build |
| L19 | manual: Docker sandbox run (section 7): uid 1000 cannot change build outputs or plant files; no network, no secrets |
| L20 | dag: `test_evaluate.test_budget_and_self_report` |
| L21 | dag: `test_evaluate.test_awaiting_evaluator`, `test_infra_retries_bounded`, `test_providers` |
| L22 | dag: `test_evaluate.test_calibrate`, curriculum tests in `test_stats` |
| L23 | dag: `test_stats` (mixture weights by family, not by versions) |
| L24 | dag: `test_stats` (paired statistics on fixtures: n = 0, ties, all failures) |
| L25 | dag: `test_evaluate.test_screen_not_promising_stops`, `test_idempotent_rerun` |
| L26 | dag: `test_evaluate.test_provisional`, `test_full_pass_family_disjoint` |
| L27 | dag: `test_evaluate.test_fabricated_comparison_rejected` |
| L28 | dag: `test_evaluate.test_compare_and_swap`, `test_head_and_epoch_staleness` |
| L29 | dag: `test_evaluate.test_rollback_and_replay`, `test_no_evidence_no_activation`, `test_bootstrap` |
| L30 | dag: `test_report` (eight charts per role, units, uncertainty, no model calls) |
| L31 | dag: `test_report.test_anchor_series_never_spliced`, `test_pareto_only_comparable_points` |
| L32 | dag: `test_report.test_html_is_self_contained`, `test_escaping` |
| L33 | dag: `test_evaluate.test_idempotent_rerun`, `test_records_cli` (publish dedupes) |
| L34 | core: no axiom added, existing definitions unchanged; the certificates are reproducible with `#sigaba_generator_check` by anyone |

## 7. End-to-end runs (2026-11-28)

These were recorded on a maintainer's machine. They use this branch's core and the DAG's
`ci/learning` at its PR branch, the core's pinned toolchain, and real Lean throughout. No model was
called.

1. **Generator path.** Both bootstrap generators go through `route` → `certify` → `decide`
   (`success`, label `learning:needs-maintainer`) → `publish` → `report`. In both certificates the
   kernel accepted `Certified <family> L 8 8 generate`, and every smoke sample was confirmed by
   `#sigaba_generator_link`. A manifest that misstates its level count is rejected by the check.
   Republishing the same records is idempotent.
2. **Docker sandbox (L19).** The design generator was certified inside a container, with the
   workflow's flags:
   - `--network none --read-only --cap-drop ALL`;
   - `SETUID SETGID CHOWN FOWNER`;
   - `no-new-privileges`;
   - Lean running as uid 1000.

   After the build, uid 1000 could not overwrite an `.olean`, create files under `.lake`, or plant
   a root `lakefile`. Its per-call output directory stayed writable, and trusted commands still
   ran.
3. **Notebook path.** The DAG has one certified design generator, and the policy is a pilot one:
   - `local-cli` provider with the model-free `scripted-fixture` solver;
   - 4 calibration samples, 6 screen pairs, 20 confirm pairs;
   - preferred band from 0;
   - provisional within-family scope allowed.

   The run went as follows:
   - **Calibration** of the empty reference notebook: 8 trials, p̂ = 0, level 0 selected.
   - **Screen:** the candidate (a 149-byte note naming `avoidDesign_target`) solved 6 of 6, the
     incumbent 0 of 6 (`inconclusive`, promising).
   - **Independent confirmation:** 20 of 20 against 0 of 20, LB 0.663. Verdict
     `pass_performance`, scope `fresh_seed`, provisional.

   Then came the PR decision `success`, a simulated merge, a compare-and-swap activation
   (sequence 1), and the report with the new active notebook. Every solution was checked by
   `#sigaba_task_check` in a fresh workspace. 60 trials took 14 minutes, most of it Lean.

   The solver is scripted, so this tests the machinery, not a model.

Not run: the workflows on GitHub, since they run from the base branch after the DAG PR is merged;
the published environment image, since it needs a core release; and a paid model.
