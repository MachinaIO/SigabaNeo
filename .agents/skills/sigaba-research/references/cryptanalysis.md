# Domain: cryptanalysis (Cryptanalysis AI)

Strength is lowered only by proven attacks. You prove them.
([docs/ASSUMPTIONS.md](../../../../docs/ASSUMPTIONS.md), `SigabaNeo/Trusted/Assumption.lean`.)
Submitting goes through the [`sigaba-dag`](../../sigaba-dag/SKILL.md) skill; in a research run
you are a worker ([worker.md](worker.md)) and the controller does the Git and GitHub steps.

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

Heuristic attacks (relying on GSA, unproven sieving statistics, …) do not count. Record them as
notes, with the hypothesis they need; they show where a proof would pay off.

## Steps

1. **Pick a target**: assumptions with tag `assumption` in the DAG and those in `SigabaNeoStd`
   (`SigabaNeo.Lattices.LWE.decision`, `.search`, `RingLWE.*`, `ModuleLWE.*`), preferring those
   that submissions use as premises and those whose claimed `H` is far above the best known attack.
   Read existing attack notes and closed PRs first.
2. **Fix the parameters** `p` (a definition node, or the parameters a submission's premise names)
   and the target bits `c` (a numeral below the current `H p`).
3. **State** the theorem node `theorem <Ns>.attack_<id> : (<assumption>).Attack <p> <c> := by sorry`.
   For a family of parameters, state `∀ p, <condition> → (<assumption>).Attack p (f p)` instead.
   Decompose by sketches: the algorithm's correctness/success probability, its step count, the
   machine compilation, and the final inequality.
4. **Build the machine**: write the algorithm as a tape program and compile it with
   `Prog.toMachine` (`run_toMachine` gives its output law, `cost_toMachine` its exact cost);
   compose with `SigabaNeoStd/Machines/Compose`. Reuse the algorithmic analyses already in the DAG
   (definitions, theorems and notes tagged `lattice-attack`), but note they count abstract operations: you must still bound the machine's steps on the
   assumption's actual instance encoding.
5. **Submit** the proof with a note: the assumption, `p`, `c`, the current `H p`, the submissions
   whose premises the attack invalidates, and the attack's idea.
6. Also prove the corresponding refute card when a claim states the assumption
   (`¬ a.HardAt p k` for `k > c`, from `Attack.not_hardAt`).

## Pitfalls

* `H` may not evaluate at large parameters; compare `c` with certified bounds on `H p`, and state
  in the note how you compared them.
* Large concrete constants: prove generic lemmas and instantiate; `native_decide` is forbidden.
* Lowering the strength is not automatic yet (the harness does not apply attacks itself); say in
  the PR that maintainers should apply it.
