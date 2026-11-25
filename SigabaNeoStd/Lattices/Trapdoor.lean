import SigabaNeoStd.Lattices.Gaussian
import SigabaNeoStd.Lattices.Encoding
import CslibFrontier.Crypto.Computational.Basic
import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary

/-!
# Lattice trapdoors and preimage sampling

**The ideal distribution.** For `B ∈ Z_q^{n×m}` and `P ∈ Z_q^{n×k}`, `preimage B P τ` draws each
column `K_j` of `K ∈ Z^{m×k}` independently from the discrete Gaussian of width `τ` on the coset
`{x ∈ Z^m : B·x = P_j (mod q)}` (`cosetGauss`), or is `none` if some coset is empty. `ideal P τ`
draws a uniform `B` and then `preimage B P τ`.

**A trapdoor sampler** (`Sampler n m k q τ`) is a pair of algorithms, in the sense of [GPV08] and
[MP12]:

* `gen` (`GenTrap`) on `(κ, q)` (`κ` in unary, `q` in binary) outputs `B` (as `matVals B`) and a
  trapdoor of any type `T` with any encoding;
* `pre` (`SamplePre`) on `(κ, q)`, the trapdoor and `P` (as `matVals P`) outputs the columns of `K`;

both strict PPT (cslib-frontier's `IsPPTOn`: one machine and one polynomial clock for every
input), such that for a negligible `err`, for all large `κ` and every `P`, the pair `(B, K)` they
produce is within statistical distance `err κ` of `ideal P (τ κ)` (`pipeline`, `encodeOut`).

`Trapdoor.Exists n m k q τ` states that one exists. `SigabaNeoStd.Lattices.Trapdoor.Family` proves
it for one parameter family (`Trapdoor.Family.exists_sampler`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

namespace Trapdoor

/-- `K`, column by column: the coset Gaussian of width `τ` on `{x : B·x = P_j}` for each column
`P_j` of `P`, or `none` if some coset is empty. -/
noncomputable def preimage {n m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (P : Matrix (Fin n) (Fin k) (ZMod q)) (τ : ℝ) (hτ : 0 < τ) :
    PMF (Option (Matrix (Fin m) (Fin k) ℤ)) :=
  (sampleOptList ((List.finRange k).map fun j => cosetGauss B (fun i => P i j) τ hτ)).map
    (Option.map fun cols r j => (cols.getD j.val 0) r)

/-- The ideal distribution: a uniform `B` and the coset Gaussian preimage of `P`. -/
noncomputable def ideal {n m k q : ℕ} [NeZero q] (P : Matrix (Fin n) (Fin k) (ZMod q)) (τ : ℝ)
    (hτ : 0 < τ) : PMF (Matrix (Fin n) (Fin m) (ZMod q) × Option (Matrix (Fin m) (Fin k) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun B =>
    (preimage B P τ hτ).map (B, ·)

/-- `K` as its list of columns. -/
def cols {m k : ℕ} (K : Matrix (Fin m) (Fin k) ℤ) : List (List ℤ) :=
  List.ofFn fun j => List.ofFn fun r => K r j

/-- `(B, K)` as lists: the entries of `B` and the columns of `K`. -/
def encodeOut {n m k q : ℕ} (x : Matrix (Fin n) (Fin m) (ZMod q) × Option (Matrix (Fin m) (Fin k) ℤ)) :
    List ℕ × Option (List (List ℤ)) :=
  (matVals x.1, x.2.map cols)

/-- The trapdoor holder: `gen (κ, q)`, then `pre` on the trapdoor and `P`. -/
noncomputable def pipeline {T : Type} (gen : ℕ × ℕ → ProbComp (List ℕ × T))
    (pre : (ℕ × ℕ) × T × List ℕ → ProbComp (List (List ℤ))) (κ q : ℕ) {n k : ℕ}
    (P : Matrix (Fin n) (Fin k) (ZMod q)) : ProbComp (List ℕ × Option (List (List ℤ))) := do
  let g ← gen (κ, q)
  let K ← pre ((κ, q), g.2, matVals P)
  pure (g.1, some K)

/-- A trapdoor sampler for `B ∈ Z_q^{n×m}`, `k` targets at a time, and Gaussian width `τ`. -/
structure Sampler (n m k q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (τ : ℕ → ℝ) (hτ : ∀ κ, 0 < τ κ) where
  /-- The trapdoor. -/
  T : Type
  /-- Its encoding. -/
  encT : T ↪ List Bool
  /-- `GenTrap`: `B` and the trapdoor. -/
  gen : ℕ × ℕ → ProbComp (List ℕ × T)
  /-- `SamplePre`: the columns of `K`. -/
  pre : (ℕ × ℕ) × T × List ℕ → ProbComp (List (List ℤ))
  gen_isPPT : IsPPTOn (encPair encUnary encNat) (encPair (encList encNat) encT) gen
  pre_isPPT : IsPPTOn (encPair (encPair encUnary encNat) (encPair encT (encList encNat)))
    (encList (encList encIntBin)) pre
  /-- The statistical error. -/
  err : ℕ → ℝ≥0
  err_negligible : Negligible err
  close : ∀ᶠ κ in Filter.atTop, ∀ P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)),
    CloseTo (ProbComp.eval (pipeline gen pre κ (q κ) P))
      ((ideal (m := m κ) P (τ κ) (hτ κ)).map encodeOut) (err κ)

/-- A trapdoor sampler exists. -/
def Exists (n m k q : ℕ → ℕ) [∀ κ, NeZero (q κ)] (τ : ℕ → ℝ) (hτ : ∀ κ, 0 < τ κ) : Prop :=
  Nonempty (Sampler n m k q τ hτ)

end Trapdoor

end SigabaNeo.Lattices
