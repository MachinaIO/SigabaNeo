# Assumptions with a security function (`SigabaNeo/Lib/Assumption.lean`)

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

An `Attacker` is an explicit fair-coin multi-tape Turing machine over `Bool`. It is
cslib-frontier's `Turing.MultiTapePTM tapes Bool (Fin states)` with no oracle, run for `time`
steps on the encoded instance. Its cost is

```
cost = time + descLen,   descLen = 6 · states · 3^tapes · (4 + 4·tapes + size(states))
```

`descLen` is the length of the canonical fixed-width encoding of the transition table. The table has
one entry per state, per symbol under the input head (3 values), per symbols under the work heads
(3^tapes) and per coin value (2). Each entry holds the head moves, the writes, the output symbol and
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

## Lattice assumptions

`ModuleLWE.decision`, `ModuleLWE.search`, `RingLWE.decision`, `RingLWE.search`, `LWE.decision` and
`LWE.search` are `Assumption`s ([LATTICES.md](LATTICES.md)). Their `H` is the floor of the cheapest
attack of the lattice estimator, formalized in `SigabaNeo/Lib/Lattices/Estimator/`
([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)). It is computable, so the harness compares `#eval LWE.H p`
with `k`:

```lean
def kyber512 : ModuleLWE.Params :=
  { N := 256, rank := 2, m := 2, q := 3329, error := .cbd 3, secret := .cbd 3 }
#eval ModuleLWE.H kyber512
```
