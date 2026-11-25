# Sigaba-Neo: design

Is a hardness assumption true under other hardness assumptions? Sigaba-Neo turns this question into
two Lean theorems, has AI agents prove one of them in a shared DAG of Lean files on GitHub, and
checks the answer locally.

## The three parties

| Party | Trusted by the submitter? | Runs |
| --- | --- | --- |
| **Submitter** | (itself) | the trusted check, through `python/sigaba_neo.py` |
| **Agents** | no | pull requests to the DAG repository, following its `SKILL.md` |
| **Maintainers and CI** | no | the DAG repository: its gate (`python/dag_verify.py`, `python/dag_tools.py`), records and index ([GITHUB_PLATFORM.md](GITHUB_PLATFORM.md)) |

The submitter trusts the following and nothing else:

- its own claim directory;
- Lean;
- the core's pinned packages (cslib-frontier, Mathlib);
- `SigabaNeo/Trusted/Check.lean`, about 150 lines;
- when a claim uses them, the definitions in `SigabaNeo/Trusted/` that give it meaning: the machine
  model (`Machine.lean`), assumptions and `HardAt` (`Assumption.lean`), primitives
  (`Primitive.lean`) and the `Spec` template (`Submission.lean`). They are read once, like the claim's own definitions.

`sigaba_neo.py` cannot make a false claim pass. It only has to run the check with this checkout's
core and show the check's report, which states the claim directory it read and what was
established.

## The submitter

The submitter writes a **claim directory**:

- `claim.json`: the target and the hypotheses,
  `{"target": "T", "hypotheses": ["H₀", "¬ H₁", …], "select": [{…}, …]}`;
- `Definitions/Def_*.lean`, the assumptions in Lean, as Prove2Me definition files (which import
  each other as `Definitions.Def_<name>`, and may import the core's libraries, such as
  `SigabaNeoStd.Lattices`, [LATTICES.md](LATTICES.md); `SigabaNeoStd` is the standard library, which
is not trusted, [GITHUB_PLATFORM.md](GITHUB_PLATFORM.md)).

`sigaba_neo.py` has two commands, `submit CLAIM` and `check CLAIM`, and a helper, `dev CLAIM`, that
makes the claim directory a Lake project requiring the core, so that an editor and `lake build`
resolve `import Definitions.…` there (the check does not use these files).

### Claims and hypotheses

Every claim is published as two cards that state the target alone:

- `theorem SigabaNeo.Claim_<d>.prove : T := by sorry`
- `theorem SigabaNeo.Claim_<d>.refute : ¬ T := by sorry`

The cards belong to the proposition, not to the claim. `<d>` is a SHA-256 of the target and the
definition files only, so everyone who claims `T`, under any hypotheses, shares the same two
cards. The two polarities are separate theorems, so a refute card is a proposition too (`¬ T`).

A hypothesis is a card: a prove card (the hypothesis `H`) or a refute card (`¬ H`). The cards form
one graph, shared by every agent:

| Work | On the cards |
| --- | --- |
| prove `T` under assumptions | a sketch on `T`'s card whose leaves are the assumptions' cards |
| look for a counterexample to an assumption `A` | a proof of `A`'s refute card |
| reduce `A` to a weaker assumption `B` | a sketch on `A`'s own prove card whose leaf is `B`'s card |

Reductions recorded by different agents compose. If `T` is reduced to `A` and `A` to `B`, then
`check` of a claim of `T` that allows only `B` follows `T → A → B` and accepts it.

The gate accepts every such sketch. Which unproved cards may remain is each submitter's choice,
made in `claim.json`, and `check` enforces it: a proof counts only if every card it leaves
unproved is one of the claim's hypotheses.

**Choosing hypotheses.** A claim has two ways to name hypotheses:

- `hypotheses` lists propositions in its own definitions (`H` or `¬ H`). `submit` writes each one
  as a claim of its own, and uses its prove card (refute card for `¬ H`).
- `select` lists selectors. Each selector is an object, and all its keys must hold. A card is
  chosen if any selector chooses it.

  | Selector | Chooses |
  | --- | --- |
  | `{"id": "<theorem name>"}` | that card (prove or refute) |
  | `{"tag": "well-established"}` | claims the maintainers tagged |
  | `{"minYears": X}` | claims first proposed at least X years ago (the maintainers' record) |
  | `{"minRefuteSketches": X}` | claims whose refute card has at least X sketches |

  The last three choose prove cards, and skip claims that are already refuted or disproved. The
  maintainers' metadata is the DAG's `meta/assumptions.json`, and the sketches are counted in the
  DAG's records (or the DAG's files, without records).

**`submit`** fixes the hypotheses once: each `hypotheses` entry gets its card, and the selected
cards are added with their definition files, which are copied into `Definitions/`. It writes the
result back to `claim.json` (`hypotheses`, `cards`, `resolvedAt`, and the DAG's commit `dag`).
From then on the claim does not change, and `submit` does not resolve again. The DAG's metadata
chose the selected cards, so read them in `claim.json` before trusting a result. Then `submit`
writes the definitions and the proposition's two cards into a checkout of the DAG, unless they
are already there; with `--pr` it opens the pull request.

**`check`** reads both cards in a checkout of the DAG (`--dag`, and optionally its records,
`--records`), and for each it works in four steps:

1. It takes a solution or sketch, those the records verified in its environment first. It follows
   every theorem the solution imports, recursively, through their solutions or sketches (the
   reductions). A card that is one of the claim's hypotheses may stay unproved, and becomes a leaf.
   Every other card must be proved this way, and a cycle proves nothing. It also takes every
   definition they import.
2. It lays them out in Prove2Me's layout in a Lake workspace that requires the core. The
   submitter's own definition files replace the DAG's copies.
3. It makes four edits:
   - each solution is wrapped in its own namespace, because all of them declare `solution`;
   - each imported statement is closed by its solution (`p2m_apply%`, `SigabaNeo/Assemble.lean`);
   - each hypothesis card becomes an axiom of its statement, `axiom SigabaNeo.Claim_<e>.prove : H`;
   - `Claim.lean` states the claim as `Claim.proof : H₀ → … → C`.
4. It builds and runs `#sigaba_neo_check` on the claim directory, and prints the check's report as it
   is.

Each report says what was established and whether that proves or refutes the target:

- `proved`: `H → T`, or `¬(H → ¬T)`;
- `refuted`: `H → ¬T`, or `¬(H → T)`.

The check accepts an axiom only if its type is exactly one of the hypotheses, and only when the
claim is not negated. The deduction theorem then turns `⊢ H → C` under an axiom `a : H` back into
`H → C`. The report lists these axioms as `hypothesis axioms`, and they count as referenced
hypotheses.

Both together mean the hypotheses are inconsistent; neither means the question is still open.

The DAG's files and the layout cannot make a false claim pass. If either is wrong, the build fails or
the check fails.

## The trusted check (`SigabaNeo/Trusted/Check.lean`)

`#sigaba_neo_check "CLAIM"` runs in the workspace. It reads the claim directory itself and checks:

1. the workspace's copies of the claim's definition files are byte for byte the claim's. These
   modules are built in the workspace and import nothing else built there;
2. the target and the hypotheses are declared by them;
3. the theorem's type is one of the four claims: `H → T`, `H → ¬T`, or the negation of either.
   Each claim is built as an expression from the names, never elaborated from text, so no macro
   can change it;
4. the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. This rules out
   `sorry`, `native_decide` and any declared axiom;
5. every declaration of every other module built in the workspace, and of every module of the
   standard library (`SigabaNeoStd`) that the claim's definitions do not import, passes the kernel
   again: it is replayed onto the rest. A module that bypassed the kernel while it was being built
   (for example with `debug.skipKernelTC`) is caught here. The std modules the definitions import
   are part of the claim's meaning, and are read like the core's definitions.

Its report gives the claim directory (resolved), the established proposition, the outcome
(`proved` or `refuted`), the axioms, and `referenced hypotheses`: the hypotheses whose variable
occurs in the proof.

**Vacuity.** A false hypothesis implies anything, so a claim under hypotheses is only as
meaningful as they are.

**Building is sandboxed.** Lean code can run arbitrary programs while it is built, so `check`
builds in a bubblewrap sandbox (`sigaba_neo.sandbox_prefix`) built from an empty root. It holds
only what a build needs, read only: the system's programs and libraries (`/usr`, `/etc`), the
toolchain, the core and its packages. The workspace is writable. Nothing else of the host is
there: not the home directory, nor `/run` and its sockets (Docker's, say), nor the host's `/tmp`.
There is no network, the environment is an allowlist, and every process is killed with the build. It
builds in two steps. The first step builds only the claim's definitions, which may import no other
definition, so that it runs only the submitter's own files. The definitions' build outputs are copied for
the check right then, and their sources are written for it from the claim itself. The second step
builds everything else, with the definitions' sources and build outputs read only. Nothing it
leaves under the definitions' names is ever used. The claim directory is not even visible inside, and the workspace's Lake
configuration is read only. `#sigaba_neo_check` then runs outside, once no process of the builds
is left, without anything of the workspace's configuration. It runs in a fresh directory that holds
only copies of the build outputs of the workspace's own modules (regular files under `Definitions`,
`Theorems`, `Solutions`, and the claim's module). It uses the core's Lean executable and search
path, with the core's packages first, so that no built module can stand in for one of theirs. Its
report counts only if it exits normally. The check runs in a sandbox of its own as well: it sees
the claim, read only, and writes only its own directory, so a malformed build output cannot reach
the host.

**What remains assumed.** The check loads the compiled modules the build produced (`.olean`
files), and the proof's code ran while they were produced. Lean's loader expects files that Lean
wrote, so the verdict assumes that the loader reads a crafted file faithfully, or at least that a
crafted file cannot turn a rejection into an acceptance. Removing this assumption means replaying
the declarations from a validated serialization in an independent checker (`lean4export` with an
external kernel); that is future work. Without bubblewrap, `check` refuses to build unless `--no-sandbox` is given; a
proof could then overwrite, for example, the build outputs of the submitter's definitions, and the
check could not detect that.

## Agents

Agents work on the DAG repository from their forks, following its `SKILL.md`
(`templates/dag/SKILL.md`):

- they read the index (statuses, open leaves, claims, notes);
- they add definitions, theorems, solutions and notes under `dag/`, and check them locally with
  `python3 python/dag_verify.py verify`;
- they open pull requests, and the gate checks them in a sandbox and comments its verdict;
- they work on the theorems `SigabaNeo.Claim_*` and the leaves below them.

## The DAG repository and its gate

See [GITHUB_PLATFORM.md](GITHUB_PLATFORM.md).

## Repository

| Path | Party | Contents |
| --- | --- | --- |
| `SigabaNeo/Trusted/Check.lean` | submitter (trusted) | `#sigaba_neo_check` |
| `SigabaNeo/Trusted/Machine.lean` | all (trusted) | the machine model of algorithms and attackers |
| `SigabaNeo/Trusted/Assumption.lean` | all (trusted) | assumptions with a security function ([ASSUMPTIONS.md](ASSUMPTIONS.md)) |
| `SigabaNeo/Trusted/Primitive.lean` | all (trusted) | primitives ([PRIMITIVES.md](PRIMITIVES.md)) |
| `SigabaNeo/Trusted/Submission.lean` | all (trusted) | submissions and `Spec` ([PRIMITIVES.md](PRIMITIVES.md)) |
| `AdvancedEncryption/` | all | a Lake project of primitives in this form: predicate encryption |
| `SigabaNeoStd/` | all (not trusted) | the standard library: lattices (discrete Gaussians, gadget, LWE/RingLWE/ModuleLWE, trapdoor sampling, [LATTICES.md](LATTICES.md)), the estimator and attacks, machines and programs, encodings |
| `SigabaNeo/Assemble.lean` | submitter | `p2m_apply%` (cannot make a false claim pass) |
| `python/sigaba_neo.py` | submitter | `submit`, `check` (runs the check and shows its report), `dev` |
| `SigabaNeo/Platform.lean`, `SigabaNeo/Platform/` | CI | the gate's Lean commands: module and submission checks, the syntactic filter, semantic IDs |
| `python/dag.py`, `python/dag_verify.py`, `python/dag_tools.py` | CI, maintainers | the DAG's layout and statuses, the verifier, the gate's other steps, `init` ([GITHUB_PLATFORM.md](GITHUB_PLATFORM.md)) |
| `python/formalpedia.py` | CI | a mirror of Formalpedia, converted into DAG files |
| `schemas/`, `templates/dag/`, `docker/` | maintainers | JSON schemas; the DAG repository's template (workflows, `SKILL.md`); the environment image |
| `tests/`, `python/tests/` | | tests (`./tests/run.sh`) |
