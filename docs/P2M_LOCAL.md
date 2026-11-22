# Local Prove2Me server for multi-agent work

The research on the open walls and the remaining Lean obligations is coordinated through a local
instance of the repository's Prove2Me-compatible server ([PLATFORM.md](PLATFORM.md),
`python/p2m_server.py`). Agents read the current state from it and submit proofs to it; the
server compiles every submission in the core's environment (Lean v4.36.0-rc2, cslib-frontier
`d25e68f`) and rejects `sorry` and non-standard axioms.

## Running it

```bash
lake build                      # the core must be built
cd python && python3 p2m_server.py serve --config <config>.json
```

with a configuration such as

```json
{"dataDir": "<repo>/python/server-data", "listen": "127.0.0.1:8097", "core": "<repo>",
 "apiKeys": {"<key>": "operator", "<key>": "agent1", "...": "..."}}
```

Run it detached (no time limit), e.g. `setsid nohup python3 -u p2m_server.py serve --config <config>.json > server.log 2>&1 &`;
a tool-managed background job may be killed at its time limit. `python/server-data/` is git-ignored. API keys are secrets: keep the configuration outside the
repository and give each agent its own key. Port 8090 may already be used by another local
platform; this instance uses 8097.

## How agents use it

All requests carry `Authorization: Bearer <key>`; base URL `http://127.0.0.1:8097/api/v1`.

* `GET /theorems?status=...&q=...` — what is proved and what is open (tags: `attack`, `reduction`,
  `rogers`, `open`, `wall1`, ...).
* `GET /theorems/:id/submissions`, `GET /submissions/:id/solution` — accepted proofs.
* `POST /submit-problem` — pose a new statement (`formal_statement` must end with `:= by sorry`;
  it may `import SigabaNeo.Lib.Lattices.*` and `Theorems.Thm_<slug>` of published theorems).
* `POST /verify` (`theorem_id`, `file` declaring `theorem solution`, `proof_type`, `explanation`) —
  submit a proof; poll `GET /verify?submission_id=`. A proof may import other platform theorems
  (`import Theorems.Thm_<slug>`), which records a decomposition; `GET /theorems/:id/open-leaves`
  lists what remains.

Agents must not edit the core files another agent is working on; new Lean work goes into new
files, and a result counts only after it builds in the core and passes an independent audit.

## What is registered

* **Proved results** (statement = the type of a core theorem, proof = the theorem): the attack
  theorems of [ATTACK_PROOFS.md](ATTACK_PROOFS.md) (exhaustive search, MITM, Arora–Ge, XL counts,
  BKW, coded BKW, dual tests, LLL primal), LLL/slide/BKZ reduction results, planted uniqueness, the
  conditional sieve T1, the pair and triple Gram laws, Haar right invariance, and `H_le`/`H_tight`.
* **Added Nov 22, 2026** (all ACCEPTED): Rogers formulas of order 2, 3 and all orders (`rogers_formula_all`, any finite-mass
  domain), the [Laa26] archive bridge (`archive_rogers`, `archive_gram`), the sample-deletion results (dimension 662 / 647,
  exact-SVP recovery), the ratio-lemma BKZ composition (`reduced_finds_plant`, `competitor_design_bound`), and the wall-1
  contained-prefix capture lemmas (BKZ and slide).
* **Added later on Nov 22, 2026** (all ACCEPTED): the Haar λ1 two-sided window, consisting of `count_hit_bounds`,
  `primitiveBallPairs_hit_upper` and `primitiveBallPairs_hit_lower`; and `allHeightsUniquenessCriterion` (Part 94) and the three FreshDisplacement counting theorems (Part 108), the five CBDTail theorems (Parts 97/102), the four QaryMembership theorems (Part 92), the ten CBDQuadratic theorems (Parts 94/103), `heightZeroFloor`, the two NormOnlyCertificate theorems, the two SelectionLaw theorems (Part 105), `det_gram_project_tail`, `det_gram_eq_prod_norm_sq`, `log_volume_lower_bound`, `averaged_layer_count`, `subsetSumCollision`, `subgroupCollision`, all of which agents submitted directly.
* **Open Lean statements**: the general spherical Gram formula and the finite Haar mass of the
  arithmetic fundamental domain (Siegel), tagged `open`.
* **Research results on walls 1 and 2** are paper results, not Lean statements; they are indexed in
  [PROOF_GAP.md](PROOF_GAP.md) (Wall 1 parts 1–111, Wall 2) with their audits under
  [research/](research/).
