# Sigaba-Neo: design

Is a hardness assumption true under other hardness assumptions? Sigaba-Neo turns this question into
two Lean theorems, has AI agents prove one of them on a Prove2Me-compatible server, and checks the
answer locally.

## The three parties

| Party | Trusted by the submitter? | Runs |
| --- | --- | --- |
| **Submitter** | (itself) | the trusted check, through `python/sigaba_neo.py` |
| **Agents** | no | Prove2Me's agent workspace (`prove2me_workspace/`, a submodule) |
| **Server operator** | no | `python/p2m_server.py`, a server with Prove2Me's API and the core's environment (cslib-frontier included) |

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
  `SigabaNeo.Lib.Lattices`, [LATTICES.md](LATTICES.md)).

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

The server accepts every such sketch. Which unproved cards may remain is each submitter's choice,
made in `claim.json`, and `check` enforces it: a proof counts only if every card it leaves
unproved is one of the claim's hypotheses.

**Choosing hypotheses.** A claim has two ways to name hypotheses:

- `hypotheses` lists propositions in its own definitions (`H` or `¬ H`). `submit` publishes each
  one as a claim of its own, and uses its prove card (refute card for `¬ H`).
- `select` lists selectors. Each selector is an object, and all its keys must hold. A card is
  chosen if any selector chooses it.

  | Selector | Chooses |
  | --- | --- |
  | `{"id": "<theorem id or name>"}` | that card (prove or refute) |
  | `{"tag": "well-established"}` | claims the server's operator tagged |
  | `{"minYears": X}` | claims first proposed at least X years ago (the operator's record) |
  | `{"minRefuteSketches": X}` | claims whose refute card has at least X accepted sketches |

  The last three choose prove cards, and skip claims that are already refuted or disproved. They
  need the compatible server, which lists the claims with the operator's metadata
  (`GET /sigaba-neo/assumptions`, `p2m_server.py annotate`). `id` works with any server.

**`submit`** fixes the hypotheses once: each `hypotheses` entry gets its card, and the selected
cards are added with their definition files, which are copied into `Definitions/`. It writes the
result back to `claim.json` (`hypotheses`, `cards`, `resolvedAt`). From then on the claim does not
change, and `submit` does not resolve again. The server chose the selected cards, so read them in
`claim.json` before trusting a result. Then `submit` publishes the definitions and the
proposition's two cards, unless they are already published.

**`check`** asks the server about both cards, and for each it works in four steps:

1. It downloads an accepted solution or sketch. It follows every platform theorem the solution
   imports, recursively, through their accepted solutions or sketches (the reductions). A card
   that is one of the claim's hypotheses may stay unproved, and becomes a leaf. Every other card
   must be proved this way, and a cycle proves nothing. It also downloads every platform
   definition they import.
2. It lays them out in Prove2Me's layout in a Lake workspace that requires the core. The
   submitter's own definition files replace the server's copies.
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

The download and the layout cannot make a false claim pass. If either is wrong, the build fails or
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
5. every declaration of every other module built in the workspace passes the kernel again: it is
   replayed onto the rest. A downloaded module that bypassed the kernel while it was being built
   (for example with `debug.skipKernelTC`) is caught here.

Its report gives the claim directory (resolved), the established proposition, the outcome
(`proved` or `refuted`), the axioms, and `referenced hypotheses`: the hypotheses whose variable
occurs in the proof.

**Vacuity.** A false hypothesis implies anything, so a claim under hypotheses is only as
meaningful as they are.

**Building is not sandboxed.** Lean code can run arbitrary programs while it is built. Downloaded
proofs should therefore be checked in a sandbox (a container without the submitter's credentials).
Otherwise a proof could, for example, overwrite the build outputs of the submitter's definitions.
The check cannot detect that.

## Agents

Agents use Prove2Me's agent workspace as it is (`SKILL.md`, `references/`, `Definitions/`,
`Theorems/`, `Solutions/`) with three changes:

- they use this server's base URL and an API key;
- the workspace's local Lake files come from `python3 p2m_server.py workspace
  ../prove2me_workspace`, so that it builds with the server's environment;
- they work on the theorems `SigabaNeo.Claim_*`.

The workspace has no license file, so it is a submodule, not a copy.

## The server

See [PLATFORM.md](PLATFORM.md).

## Repository

| Path | Party | Contents |
| --- | --- | --- |
| `SigabaNeo/Trusted/Check.lean` | submitter (trusted) | `#sigaba_neo_check` |
| `SigabaNeo/Trusted/Machine.lean` | all (trusted) | the machine model of algorithms and attackers |
| `SigabaNeo/Trusted/Assumption.lean` | all (trusted) | assumptions with a security function ([ASSUMPTIONS.md](ASSUMPTIONS.md)) |
| `SigabaNeo/Trusted/Primitive.lean` | all (trusted) | primitives ([PRIMITIVES.md](PRIMITIVES.md)) |
| `SigabaNeo/Trusted/Submission.lean` | all (trusted) | submissions and `Spec` ([PRIMITIVES.md](PRIMITIVES.md)) |
| `AdvancedEncryption/` | all | a Lake project of primitives in this form: predicate encryption |
| `SigabaNeo/Lib/Lattices/` | all | the lattice library: discrete Gaussians, gadget, LWE/RingLWE/ModuleLWE, trapdoor sampling ([LATTICES.md](LATTICES.md)) |
| `SigabaNeo/Assemble.lean` | submitter | `p2m_apply%` (cannot make a false claim pass) |
| `python/sigaba_neo.py` | submitter | `submit`, `check` (runs the check and shows its report) |
| `SigabaNeo/Platform.lean`, `python/p2m_server.py` | operator | the server and its Lean commands; `workspace` for agents; `annotate` (assumption metadata); `sync` |
| `python/formalpedia.py` | operator | a mirror of Formalpedia for `sync` (docs/PLATFORM.md) |
| `prove2me_workspace/` | agents | Prove2Me's agent workspace (submodule) |
| `tests/`, `python/tests/` | | tests (`./tests/run.sh`) |
