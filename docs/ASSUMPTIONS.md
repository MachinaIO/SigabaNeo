# Assumptions with a security function (`SigabaNeo/Trusted/Assumption.lean`)

This is the form of assumptions in Section 3.3 of the Sigaba Neo concept. An assumption is a
parameter type, the problem given to the attacker at each parameter, and a security function `H`.
`H p` is the number of bits the assumption claims at `p`.

```lean
structure Assumption where
  Params  : Type
  problem : Params → Problem
  H       : Params → ℕ

def Assumption.HardAt (a : Assumption) (p : a.Params) (k : ℕ) : Prop := (a.problem p).HardAt k
def Assumption.Holds  (a : Assumption) : Prop := ∀ p, a.HardAt p (a.H p)
```

## Attackers and their cost

An attacker is a `Machine` (`SigabaNeo/Trusted/Machine.lean`), the same machine model as the
algorithms of primitives ([PRIMITIVES.md](PRIMITIVES.md)). `Machine ops` is cslib-frontier's
fair-coin `Turing.MultiTapePTM tapes Bool (Fin states) (Fin ops)`, run for `time` steps; an attacker
on an assumption has no oracle (`Machine = Machine 0`) and runs on the encoded instance. Its cost is

```
cost = time + descLen
descLen = 6 · states · 3^tapes · 3^ops · (4 + 4·tapes + 4·ops + size(ops) + size(states))
```

which for `ops = 0` is `6 · states · 3^tapes · (4 + 4·tapes + size(states))`.

`descLen` is the length of the canonical fixed-width encoding of the transition table. The table has
one entry per state, per symbol under the input head (3 values), per symbols under the work heads
(3^tapes), per symbols under the answer heads (3^ops) and per coin value (2). Each entry holds the
head moves, the writes, the output symbol, the query symbols, the channel submitted (if any) and
the next state. Counting the description excludes the attackers with a hard-wired table that exist
non-constructively at fixed parameters (Bernstein–Lange, De–Trevisan–Tulsiani). A table must be
stored in the control states, so it is paid for in `descLen`.

## Problems and `HardAt`

* `Problem.decision real ideal`: two laws on encoded instances. The attacker outputs `[true]` to
  say "real". The gain is the squared advantage (Micciancio–Walter).
* `Problem.search instances`: a law on pairs of an encoded instance and its set of encoded
  solutions. The gain is the success probability.

`Problem.HardAt P k` is `∀ A, 2^k · gain A ≤ cost A`, that is, `cost / gain ≥ 2^k`.

| Theorem | Statement |
| --- | --- |
| `Problem.HardAt.mono` | `HardAt k → k' ≤ k → HardAt k'` |
| `Problem.hardAt_zero` | `HardAt 0` (gains are at most 1, costs at least 1), so a claim of `0` bits is no claim |
| `Assumption.Holds.hardAt` | `a.Holds → k ≤ a.H p → a.HardAt p k`: the premise `(a, p, k)` of a submission |
| `Assumption.Attack.not_hardAt` | an explicit attacker with `cost ≤ 2^c · gain` and a positive gain refutes `HardAt a p k` for every `k > c` |
| `Assumption.Attack.le` | the same, as `HardAt a p k → k ≤ c` |

`Attack.not_hardAt` justifies the update rule: once an attack at `c` is proven, `H p` may be
lowered to `c` and no true claim is lost.

## Lowerings

Every update of a strength is a whole new security function, not a value at one parameter. An
attack that works on a region of parameters is written as a function with that region lowered,
typically `H' p = if region p then min (f p) (H p) else H p`.

```lean
def Assumption.Lowering (a : Assumption) (H H' : a.Params → ℕ) : Prop :=
  ∀ p, H' p ≤ H p ∧ (H' p < H p → a.Attack p (H' p))
```

| Theorem | Statement |
| --- | --- |
| `Lowering.refl` | `a.Lowering H H` |
| `Lowering.trans` | lowerings compose |
| `Lowering.not_hardAt` | where `H' p < H p`, every claim above `H' p` is false |
| `Lowering.hardAt` | `HardAt a p (H p) → HardAt a p (H' p)`: no true claim is lost |

A function that only rewrites `H` (equal everywhere, but faster to evaluate) is a lowering with no
attack at all.

## The registry and premises

The strength of an assumption changes; its problem does not. The harness therefore keeps the two
apart:

* `Registry`: the admitted assumptions by name (`Name`), with the parameter set and the problem of
  each. `Registry.of as` registers `Assumption`s.
* `R.Strength`: the current strengths, `(n : R.Name) → R.Params n → ℕ`, owned by the harness.
  `Registry.initial as` takes each assumption's own `H`. They only go down.
* `R.Holds H n`: assumption `n` has `H n p` bits at every `p`.
* `Premise R`: a submission's premise `(n, p₀, k)`, naming a registered assumption.
  `Premise.Valid H`: `k ≤ H n p₀`.

`Registry.univ` names every assumption by itself (`Name := Assumption`). A submission over it may
use any assumption, but only the registered ones count: the harness gives an unregistered
assumption strength `0`, so a premise on it can ask only for `0` bits, which always hold. Problem
authors use `Registry.univ`, so that an assumption registered after the problem can still be a
premise.

| Theorem | Statement |
| --- | --- |
| `Registry.Holds.mono` | `R.Holds H n → H' n ≤ H n → R.Holds H' n`: lowering a strength keeps every true claim |
| `Registry.holds_initial` | `(as n).Holds → (of as).Holds (initial as) n` |
| `Premise.hardAt` | `d.Valid H → R.Holds H d.n → R.HardAt d.n d.p d.k` |

## Lattice assumptions

`ModuleLWE.decision`, `ModuleLWE.search`, `RingLWE.decision`, `RingLWE.search`, `LWE.decision` and
`LWE.search` are `Assumption`s ([LATTICES.md](LATTICES.md)). Their `H` is the floor of the cheapest
attack of the lattice estimator, formalized in `SigabaNeoStd/Lattices/Estimator/`
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). It is computable, so the harness compares `#eval LWE.H p`
with `k`:

```lean
def kyber512 : ModuleLWE.Params :=
  { N := 256, rank := 2, m := 2, q := 3329, error := .cbd 3, secret := .cbd 3 }
#eval ModuleLWE.H kyber512
```

At large parameters the evaluation does not finish (the hybrids and Arora–GB search over spaces of
size `n`, and the kernel cannot hold a modulus such as `2^(2^25)`). There a premise `k ≤ H p` is
proved from certified lower bounds on each attack instead (`Estimator.estimatorBits_ge_of`,
`Estimator.cbd16_estimatorBits_ge`; [LWE_ESTIMATOR.md](LWE_ESTIMATOR.md#large-parameters)). For
example `2650 ≤ RingLWE.H` at ring degree `2^34`, `q = 2^(2^25)`
(`AdvancedEncryption/PE/Impl/DualUse/Params/Strength.lean`).

## Assumptions and strengths in the DAG

Anyone may register an assumption in the DAG repository, AI agents included; Cryptanalysis AI
lowers the strength of the ones that claim too much. The layout and the gate's checks are in
[GITHUB_PLATFORM.md](GITHUB_PLATFORM.md), section 2.

* **Registration**: `dag/Assumptions/<slug>/Asm.json` names a constant of type
  `SigabaNeo.Assumption` (in a definition node or in std) and gives the rationale of its `H`. An
  assumption is identified by its parameter set and its problem, not by `H`: registering an
  existing problem again, with another `H`, is a `DUPLICATE`, so a problem cannot escape its
  lowered strength by being registered again.
* **Strength versions**: `dag/Assumptions/<slug>/H_v<n>.json` gives a new security function `H` and
  a proved theorem node `lowering` with the statement `Lowering <assumption> <previous> <H>`, where
  `<previous>` is the assumption's own `H` for `H_v1` and the function of `H_v(n-1)` after that.
* **The current strength is the latest version.** It is stored, not recomputed: since every version
  lowers the one before (and lowerings compose), the latest is the lowest, and finding it reads one
  directory. Versions are numbered in order and paths are first come, so two lowerings from the
  same version cannot both be merged; the second is restated from the new latest version.
* A conservative reading is always safe for whoever relies on a submission: checking premises
  against a lower `H` can only reject more. What must not happen is a version that is higher than
  its predecessor, and the gate rejects it unless its lowering is proved.
