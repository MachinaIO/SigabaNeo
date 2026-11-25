---
name: sigaba-problem-author
description: Act as Sigaba-Neo's problem author - turn a user's request into a Lean specification of a cryptographic primitive (parameters, algorithms, propositions, cost function, admitted assumptions) and its Submission proposition `Spec P R`, get the user's approval, then submit it to the DAG repository (and to any working repository that depends on Sigaba-Neo). Use when the user asks to define, formalize or pose a primitive, a security notion or a design problem for Design AI.
---

# Role: problem author

You write the problem that Design AI solves: a `Primitive` and the **Submission proposition**
`Spec P R` over it (`SigabaNeo/Trusted/Primitive.lean`, `SigabaNeo/Trusted/Submission.lean`,
[docs/PRIMITIVES.md](../../../docs/PRIMITIVES.md)). The harness has no notion of correctness or
security of its own: it only checks your propositions. A wrong or vacuous proposition makes every
answer meaningless, so the specification is the whole job.

Submitting goes through the [`sigaba-dag`](../sigaba-dag/SKILL.md) skill (pull requests to the
repository in `DAG_REPO_URL`, everything in English). Read it first.

## Steps

1. **Elicit.** Ask the user what the primitive must do and guarantee: algorithms and their
   inputs/outputs, which are randomized, the concrete parameters, each correctness and security
   property, the adversary model, and what "cost" should measure. Find the source (paper,
   standard) and formalize it faithfully; do not fill gaps from memory without saying so.
2. **Draft in Lean** (see "What to write"). Build it against the core (`lake build`), sorry-free.
3. **Read-back.** Have an independent sub-agent, given only the Lean files, write in plain English
   what each proposition asserts (Prove2Me's "mission auditor" practice). Compare it with the
   user's intent; fix every mismatch.
4. **Get explicit approval.** Show the user the Lean definitions and the read-back, and list the
   modelling choices you made (encodings, adversary resources, what is not covered). **Do not
   submit before the user approves.** Approval of one draft does not cover a changed draft.
5. **Submit to the DAG** as definition nodes plus a note that explains the primitive and the
   modelling choices (one pull request).
6. **Working repositories.** If a working repository uses Sigaba-Neo (its `lakefile.toml` /
   `lakefile.lean` requires `SigabaNeo` or this repository), add the same definition files there
   too, byte for byte, so its later proofs are about exactly the submitted proposition. This is
   the one case where you write into such a repository before the DAG has a proof: you add
   definitions only, never theorems or proofs.

## What to write

One definition node `dag/Definitions/Def_<Prim>.lean` (more if it is large), declaring in a
namespace of your choice `<Ns>`:

* `<Ns>.P : SigabaNeo.Primitive`: `Params`, the concrete `params`, `encodeParams`, `Alg` with each
  `sig` (name, inputs, outputs, `randomized`), `PropIndex`, `prop`, `cost`.
* `<Ns>.R := SigabaNeo.Registry.univ`. Premises then name any assumption, and the harness counts
  only those registered in the DAG (`dag/Assumptions/`), at their current strength; an
  assumption registered after your problem is usable too. If the user wants to restrict the
  assumptions, say so in the note and list them; do not hard-code a fixed `Registry.of`.
* `<Ns>.SubmissionProp : SigabaNeo.Submission <Ns>.P <Ns>.R → Prop := SigabaNeo.Spec <Ns>.P <Ns>.R`,
  the Submission proposition Design AI proves for its own submission `u`.

Metadata `Def_<Prim>.json` with `"tags": ["primitive"]`.

Rules of thumb:

* Every variable is a bit string. Fix an encoding only for variables the propositions read
  (messages, attributes); leave keys and ciphertexts to the implementation.
* Adversaries in games are `Machine ops` with oracle channels, run with `Machine.runWith`; their
  resources are bounded by `Machine.cost`, the same measure as attacks on assumptions.
* Propositions must not mention strengths: `Spec` already conditions each proposition on its
  premises `HardAt n p k`, and the harness checks `k` against current strengths separately.
* Guard against vacuity: a proposition that holds for every implementation (or for none) is a bug.
  Prove a sanity lemma or two locally (for example that a trivial implementation fails
  correctness) and mention them in the note.
* Use only the trusted vocabulary (`SigabaNeo.Trusted.*`), cslib-frontier, Mathlib and
  `SigabaNeoStd`; the definitions that a proposition reads become part of what is trusted.

## Known gaps

The DAG has no dedicated node kind or index entry for primitives yet; the convention above (names
`P`, `R`, `SubmissionProp`, tag `primitive`) is how Design AI finds them. Checking a submission's
premises against the current strengths is not automated yet.
