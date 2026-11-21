import PE.Impl.RingBTVW.Laws
import SigabaNeo.Lib.Lattices.Stat
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# Security of the ring variant: the hybrid argument and the reduction to Ring-LWE

The selective weak attribute-hiding game (BTVW17 Definition 3.3 in its indistinguishability form):
the adversary names two attributes `x₀, x₁` and two messages `M₀, M₁`, gets `mpk` and a challenge
`Enc(mpk, x_β, M_β)`, and may ask keys for every `f` with `f(x₀) ≠ 0` and `f(x₁) ≠ 0`; a key for
another `f` is answered with the zero key (`keyOracle`). The adversary is a program with a key
oracle (`Adversary`); `game A x₀ x₁ x M` is the law of its output bit for the challenge `(x, M)`.

Keys come from a key sampler, whose law depends on `(B, B_f̂, p)` only (`KeySampler`), so the key
oracle depends on `mpk` only and the game is a fixed continuation `run` of the law of `(mpk, ct)`.
This makes the hybrids of BTVW17 Theorem 4.2 statements about the laws of `(mpk, ct)`:

* `H0 = realLaw x M`: the real `Setup` and `Enc`.
* `H1 = h1Law x M`: `Setup*`, `Enc*` on a Ring-LWE sample `((B, p), (c, p₀))` with
  `(c, p₀) = s (B, p) + (e, e')` (`simMap`): `B_j = B W'_j + ψ_j G̲`, `Ψᵢ = [B; c] Rᵢ + xᵢ G`,
  `c_j = c W'_j`, `κ = p₀ + M ⌊q/2⌋`. (With the key sampler, `KeyGen*` is `KeyGen`: hybrid `H2` of
  the paper is `H1`.)
* `H3 = h3Law x M`: the same on a uniform sample.

The reduction to Ring-LWE is exact (`game_h1`, `game_h3`): on `H1` and `H3` the game is
`ringLWEReal.bind (reduction …)` and `ringLWEUniform.bind (reduction …)`, so the distance between
them is the advantage of the explicit distinguisher `reduction A x₀ x₁ x M` against Ring-LWE with
`2k + 1` samples and a uniform secret.

**Security** (`attributeHiding`): the games for `(x₀, M₀)` and `(x₁, M₁)` are within
`ε₀ + δ₀ + ε + δ₁ + ε₁`, where

* `ε₀`, `ε₁` bound `H0 ≈ H1` for each challenge: statistical (the regularity of the trapdoor
  matrix `B`, the leftover hash lemma for `B W'_j`, and noise flooding for `c_j = s(B_j − ψ_j G̲) +
  e W'_j` against fresh errors, `encodings_sim`);
* `δ₀`, `δ₁` are the Ring-LWE advantages of the two reductions;
* `ε` bounds `H3(x₀, M₀) ≈ H3(x₁, M₁)`: statistical (the leftover hash lemma for `[B; c] Rᵢ` with
  `c` uniform, which hides `x`, and the uniform `p₀`, which hides `M`).

These statistical bounds are hypotheses here.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

variable {N q k : ℕ} [NeZero q] (hk : q ≤ 2 ^ k) {Attr : Type} [Fintype Attr]

instance : Inhabited (SecretKey (R := Negacyclic (ZMod q) N) (k := k)) := ⟨⟨0, 0⟩⟩

variable (N) (Attr) in
/-- An adversary: given `mpk` and the challenge, a program that may ask keys for circuits and
outputs a bit. -/
abbrev Adversary :=
  MPK (ringSetting N q k hk Attr) → Ciphertext (ringSetting N q k hk Attr) →
    ProbOracleComp (fun _ : Circuit Attr => SecretKey (R := Negacyclic (ZMod q) N) (k := k)) Bool

variable {hk}

/-- The key oracle: keys for the circuits unauthorized for both `x₀` and `x₁`, the zero key
otherwise. -/
noncomputable def keyOracle (ks : KeySampler (Negacyclic (ZMod q) N) k) (x₀ x₁ : Attr → Bool) (mpk : MPK (ringSetting N q k hk Attr)) :
    (f : Circuit Attr) → StateT Unit PMF (SecretKey (R := (Negacyclic (ZMod q) N)) (k := k)) := fun f _ =>
  (if f.evalBool x₀ = true ∧ f.evalBool x₁ = true then keyGenLaw ks mpk f
    else PMF.pure default).map fun sk => (sk, ())

/-- The run of the adversary on `(mpk, ct)`. -/
noncomputable def run (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ : Attr → Bool)
    (v : MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) : PMF Bool :=
  (ProbOracleComp.runWith (keyOracle ks x₀ x₁ v.1) (A v.1 v.2) ()).map Prod.fst

variable (χ : PMF (ZMod q))

/-- `H0`: the law of `(mpk, ct)` in the real game for the challenge `(x, M)`. -/
noncomputable def realLaw (x : Attr → Bool) (M : Bool) : PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) := do
  let (mpk, _) ← setupLaw hk Attr
  let ct ← encLaw hk Attr χ mpk x M
  pure (mpk, ct)

/-- The game for the challenge `(x, M)`: the law of the adversary's bit. -/
noncomputable def game (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ x : Attr → Bool)
    (M : Bool) : PMF Bool :=
  (realLaw χ x M).bind (run ks A x₀ x₁)

/-- A Ring-LWE sample with `2k + 1` samples: `((B, p), (c, p₀))`. -/
abbrev RLWESample (N q k : ℕ) :=
  (Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N) × Negacyclic (ZMod q) N) ×
    (Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N) × Negacyclic (ZMod q) N)

/-- Real Ring-LWE samples: `(c, p₀) = s (B, p) + (e, e')` with `s` uniform and errors from `χ`. -/
noncomputable def ringLWEReal : PMF (RLWESample N q k) := do
  let B ← matLaw (polyLaw uniformCoeff)
  let p ← polyLaw uniformCoeff
  let s ← polyLaw uniformCoeff
  let e ← matLaw (polyLaw χ)
  let e' ← polyLaw χ
  pure ((B, p), (scalar s * B + e, s * p + e'))

/-- Uniform samples. -/
noncomputable def ringLWEUniform : PMF (RLWESample N q k) := do
  let B ← matLaw (polyLaw uniformCoeff)
  let p ← polyLaw uniformCoeff
  let c ← matLaw (polyLaw uniformCoeff)
  let p₀ ← polyLaw uniformCoeff
  pure ((B, p), (c, p₀))

/-- `[B; c]`. -/
def stackRows (B c : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)) : Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N) :=
  Matrix.of fun a col => if a = 0 then B 0 col else c 0 col

variable (hk) (Attr)

/-- `Setup*` and `Enc*` on a sample `((B, p), (c, p₀))`, for the challenge `(x, M)`. -/
noncomputable def simMap (x : Attr → Bool) (M : Bool) (rs : RLWESample N q k) :
    PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) := do
  let W' ← sampleFun (ι := Attr × (coeffBits N q k hk (Fin 2) (Col k)).Index)
    (matLaw (r := Col k) (c := Col k) (polyLaw (N := N) binaryCoeff))
  let Rm ← sampleFun (ι := Attr) (matLaw (r := Col k) (c := Col k) (polyLaw (N := N) binaryCoeff))
  let Ψ := fun i => stackRows rs.1.1 rs.2.1 * Rm i + bitR (R := (Negacyclic (ZMod q) N)) (x i) • (ringSetting N q k hk Attr).Γ.G
  pure ({ B := rs.1.1, Bj := fun j => rs.1.1 * W' j + bitsOf (ringSetting N q k hk Attr) Ψ j • (ringSetting N q k hk Attr).Γ₁.G, p := rs.1.2 },
    { Ψ := Ψ, c₀ := rs.2.1, cj := fun j => rs.2.1 * W' j,
      κ := rs.2.2 + (if M then (ringSetting N q k hk Attr).half else 0) })

variable {hk} {Attr}

/-- `H1`: `Setup*`, `Enc*` on a real Ring-LWE sample. -/
noncomputable def h1Law (x : Attr → Bool) (M : Bool) : PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) :=
  (ringLWEReal χ).bind (simMap hk Attr x M)

/-- `H3`: `Setup*`, `Enc*` on a uniform sample. -/
noncomputable def h3Law (x : Attr → Bool) (M : Bool) : PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) :=
  ringLWEUniform.bind (simMap hk Attr x M)

/-- **The reduction to Ring-LWE**: on a sample, run `Setup*`, `Enc*` and the adversary. -/
noncomputable def reduction (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ x : Attr → Bool)
    (M : Bool) (rs : RLWESample N q k) : PMF Bool :=
  (simMap hk Attr x M rs).bind (run ks A x₀ x₁)

/-- On `H1`, the game is the reduction on real Ring-LWE samples. -/
theorem game_h1 (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ x : Attr → Bool) (M : Bool) :
    (h1Law χ x M).bind (run ks A x₀ x₁) = (ringLWEReal χ).bind (reduction ks A x₀ x₁ x M) :=
  PMF.bind_bind _ _ _

/-- On `H3`, the game is the reduction on uniform samples. -/
theorem game_h3 (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ x : Attr → Bool) (M : Bool) :
    (h3Law (N := N) (hk := hk) x M).bind (run ks A x₀ x₁) =
      (ringLWEUniform (N := N) (q := q) (k := k)).bind (reduction ks A x₀ x₁ x M) :=
  PMF.bind_bind _ _ _

omit [NeZero q] in
/-- `H1` is the real game with `Setup*`, `Enc*`: the bottom row of `[B; c]` is `sB + e` and
`c W'_j` is a real encoding with the error `e W'_j` (`encodings_sim`). -/
theorem stackRows_real (B e : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)) (s : (Negacyclic (ZMod q) N)) :
    stackRows B (scalar s * B + e) = stackKey B e s := by
  ext a c
  fin_cases a <;> simp [stackRows, stackKey, scalar, Matrix.mul_apply]

/-- **Security of the ring variant** (BTVW17 Theorem 4.2): the games for `(x₀, M₀)` and `(x₁, M₁)`
are within `ε₀ + δ₀ + ε + δ₁ + ε₁`, given the statistical steps `H0 ≈ H1` (`ε₀`, `ε₁`) and
`H3(x₀, M₀) ≈ H3(x₁, M₁)` (`ε`), and the Ring-LWE advantages `δ₀`, `δ₁` of the reductions. -/
theorem attributeHiding (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr) (x₀ x₁ : Attr → Bool)
    (M₀ M₁ : Bool) {ε₀ ε₁ ε δ₀ δ₁ : ℝ≥0∞}
    (hstat₀ : CloseTo (realLaw (N := N) (hk := hk) χ x₀ M₀) (h1Law χ x₀ M₀) ε₀)
    (hstat₁ : CloseTo (realLaw (N := N) (hk := hk) χ x₁ M₁) (h1Law χ x₁ M₁) ε₁)
    (hrlwe₀ : CloseTo ((ringLWEReal χ).bind (reduction ks A x₀ x₁ x₀ M₀))
      (ringLWEUniform.bind (reduction ks A x₀ x₁ x₀ M₀)) δ₀)
    (hrlwe₁ : CloseTo ((ringLWEReal χ).bind (reduction ks A x₀ x₁ x₁ M₁))
      (ringLWEUniform.bind (reduction ks A x₀ x₁ x₁ M₁)) δ₁)
    (hlhl : CloseTo (h3Law (N := N) (hk := hk) x₀ M₀) (h3Law (N := N) (hk := hk) x₁ M₁) ε) :
    CloseTo (game χ ks A x₀ x₁ x₀ M₀) (game χ ks A x₀ x₁ x₁ M₁) (ε₀ + δ₀ + ε + δ₁ + ε₁) := by
  have h0 := hstat₀.bind_left (run ks A x₀ x₁)
  rw [game_h1] at h0
  have h3 := hlhl.bind_left (run ks A x₀ x₁)
  rw [game_h3, game_h3] at h3
  have h1 := hstat₁.symm.bind_left (run ks A x₀ x₁)
  rw [game_h1] at h1
  exact (((h0.trans hrlwe₀).trans h3).trans hrlwe₁.symm).trans h1

end AdvancedEncryption.RingBTVW
