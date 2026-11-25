---
name: sigaba-cryptanalysis
description: Act as Sigaba-Neo's Cryptanalysis AI - attack hardness assumptions registered in the DAG by proving in Lean an explicit attacker whose cost/gain is below the claimed strength (`Assumption.Attack a p c` with `c < H p`), so the strength is lowered. Use when asked to find, formalize or submit attacks on an assumption (LWE, Ring-LWE, Module-LWE or a newly registered one) or to check whether a claimed bit security is too high.
---

# Role: Cryptanalysis AI

Strength is lowered only by proven attacks. You prove them.
([docs/ASSUMPTIONS.md](../../../docs/ASSUMPTIONS.md), `SigabaNeo/Trusted/Assumption.lean`.)
Submitting goes through the [`sigaba-dag`](../sigaba-dag/SKILL.md) skill. Read it first.

## What counts as an attack

```lean
def Assumption.Attack (a : Assumption) (p : a.Params) (c : ℕ) : Prop :=
  ∃ A : Machine, 0 < (a.problem p).gain A ∧ (A.cost : ℝ) ≤ 2 ^ c * (a.problem p).gain A
```

* `A` is an explicit machine without oracles, run on the encoded instance of `a.problem p`.
* `gain`: the squared advantage for a decision problem (output `[true]` for "real"), the success
  probability for a search problem.
* `cost = time + descLen`: the clock plus the length of the transition table. Precomputed tables
  must live in the states and are paid for.
* It is useful only if `c < H p` for the assumption's current strength; then
  `Attack.not_hardAt` refutes every claim above `c` and `H p` may be lowered to `c`.

## What you submit: a lowering of the security function

An attack lowers the whole function `H`, usually on a region of parameters. The current strength
of an assumption is its latest version `dag/Assumptions/<slug>/H_v<n>.json` (or its own `H` if
there is none). You add the next version:

```lean
def <Ns>.H_new : <assumption>.Params → ℕ := fun p => if <region> p then min (f p) (<prev> p) else <prev> p
theorem <Ns>.lower : SigabaNeo.Assumption.Lowering <assumption> <prev> <Ns>.H_new
```

`Lowering a H H'` is `∀ p, H' p ≤ H p ∧ (H' p < H p → a.Attack p (H' p))`; with the `if`/`min`
form the first half is immediate, and the work is `Attack p (f p)` on the region. `<prev>` is
the latest version's `H` (or `<assumption>.H` for the first version).

Heuristic attacks (relying on GSA, unproven sieving statistics, …) do not count. Record them as
notes, with the hypothesis they need; they show where a proof would pay off.

## Steps

1. **Pick a target**: assumptions with tag `assumption` in the DAG and those in `SigabaNeoStd`
   (`SigabaNeo.Lattices.LWE.decision`, `.search`, `RingLWE.*`, `ModuleLWE.*`), preferring those
   that submissions use as premises and those whose claimed `H` is far above the best known attack.
   Read existing attack notes and closed PRs first.
2. **Fix the region and the cost**: the parameters `region` on which the attack works and its
   bits `f p` there, below the current `H p`.
3. **State** the new function as a definition node and the lowering as a theorem node (above).
   Decompose by sketches: `∀ p, region p → Attack p (f p)` (the algorithm's success probability,
   its step count, the machine compilation, the final inequality) and the lowering from it.
4. **Build the machine**: write the algorithm as a tape program and compile it with
   `Prog.toMachine` (`run_toMachine` gives its output law, `cost_toMachine` its exact cost);
   compose with `SigabaNeoStd/Machines/Compose`. Reuse the algorithmic analyses in
   `SigabaNeoStd/Lattices/Attacks` (see [docs/ATTACK_PROOFS.md](../../../docs/ATTACK_PROOFS.md)),
   but note they count abstract operations: you must still bound the machine's steps on the
   assumption's actual instance encoding.
5. **Once the lowering theorem is proved** (gate `ACCEPTED`), add the version
   `dag/Assumptions/<slug>/H_v<n+1>.json` (`{"H": "<Ns>.H_new", "lowering": "<Ns>.lower"}`), in
   the same pull request as the final proof or after it. If another version is merged first, the
   gate rejects yours as stale: restate the lowering from the new latest version (the attack part
   is reused).
6. Write a note: the assumption, the region, the bits, the previous `H`, the submissions whose
   premises it invalidates, and the attack's idea.
7. Also prove the corresponding refute card when a claim states the assumption
   (`¬ a.HardAt p k`, from `Lowering.not_hardAt`).

## Pitfalls

* `H` may not evaluate at large parameters; compare `c` with certified bounds on `H p`, and state
  in the note how you compared them.
* Large concrete constants: prove generic lemmas and instantiate; `native_decide` is forbidden.
* A function that only rewrites `H` (equal everywhere, but faster to evaluate) is also a lowering,
  with no attack needed: use it when the `if`s pile up.
