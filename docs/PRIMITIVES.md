# Primitives, submissions and `Spec`

This is the form of primitives in Section 3.1 of the Sigaba Neo concept
(`SigabaNeo/Trusted/Primitive.lean`), and of submissions and their final statement in Section 3.2
(`SigabaNeo/Trusted/Submission.lean`). Assumptions are in [ASSUMPTIONS.md](ASSUMPTIONS.md).

## Primitives

```lean
structure AlgSig where
  name : String
  inputs : List String      -- the parameters come first and are not listed
  outputs : List String
  randomized : Bool

structure Primitive where
  Params       : Type
  params       : Params                    -- the concrete values
  encodeParams : Params → List Bool        -- given to every algorithm first
  Alg          : Type
  sig          : Alg → AlgSig
  PropIndex    : Type
  prop         : PropIndex → Params → Impl sig → Prop
  cost         : Params → Impl sig → ℕ
```

The types of the variables are not fixed: every variable is a bit string. A primitive fixes an
encoding only for the variables its propositions read (for PE: attributes, predicates, messages),
and the implementation chooses the others (keys, ciphertexts).

**Implementations.** `Impl sig` gives a `Machine` for each algorithm, and a proof that each
algorithm whose signature takes no randomness is `Deterministic` (its transitions ignore the coin).
A `Machine` (`SigabaNeo/Trusted/Machine.lean`, the same model as attackers,
[ASSUMPTIONS.md](ASSUMPTIONS.md)) is cslib-frontier's fair-coin
`Turing.MultiTapePTM tapes Bool (Fin states)` with a clock `time`; it is stopped after `time` steps
if it has not halted, so its worst-case number of steps over all inputs and coins is at most
`time`. Internal parameters chosen by the
implementation (a lattice dimension, say) live in the machines.

**Running an algorithm.** `Impl.run impl a pw xs` writes `encodeTuple (pw :: xs)` on the input tape,
where `encodeTuple` is cslib-frontier's `encList encBits` (each variable framed, then concatenated),
and decodes the output word with `decodeTuple (sig a).outputs.length`. A malformed output word
decodes to empty variables. `Primitive.run P p impl a xs` does this with `pw = P.encodeParams p`.

## Submissions and `Spec`

```lean
structure Submission (P : Primitive) (R : Registry) where
  impl : Impl P.sig
  deps : P.PropIndex → List (Premise R)   -- (n, p₀, k): a registered assumption's name
  N    : ℕ

def Spec (P : Primitive) (R : Registry) (u : Submission P R) : Prop :=
  (∀ i, (∀ d ∈ u.deps i, R.HardAt d.n d.p d.k) → P.prop i P.params u.impl) ∧
  P.cost P.params u.impl ≤ u.N

def Submission.Valid (u : Submission P R) (H : R.Strength) : Prop :=
  ∀ i, ∀ d ∈ u.deps i, d.k ≤ H d.n d.p
```

A premise names an assumption of the harness's registry `R` ([ASSUMPTIONS.md](ASSUMPTIONS.md)),
so a submission cannot bring its own problem or its own strength. A new assumption that Design AI
introduces is registered first, with its claimed strength, and then named.

The two conditions of validity in Section 3.3 are separate:

1. `Spec P R u` is proven once. It mentions only the registered problems, never the strengths, so
   it stays proven when they are lowered.
2. `Submission.Valid u H` compares each `k` with the harness's current strengths `H`. The harness
   redoes it whenever it lowers `H`.

`Spec.prop_of_valid`: with both, each proposition follows from the claims, at `H`, of the
assumptions its premises name (`R.Holds H n`: `HardAt n p (H n p)` for every `p`).

## Attackers with oracles

Propositions about games quantify over `Machine ops`, a machine with `ops` query channels
(cslib-frontier's `runOracle`), run for `time` steps against a stateful oracle handler
`Fin ops × List Bool → StateT σ PMF (List Bool)` (`Machine.runWith`). Its cost is `Machine.cost`,
the same as for attackers on assumptions, whose `descLen` counts the channels
([ASSUMPTIONS.md](ASSUMPTIONS.md)).

## Primitives defined with this form

| Project | Primitive |
| --- | --- |
| `AdvancedEncryption/` | predicate encryption, weakly attribute-hiding (`AdvancedEncryption.PE`) |
