import PE.Impl.RingBTVW.Laws
import SigabaNeo.Lib.Lattices.Stat
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Probability.PMF

/-!
# Security of the ring variant under Ring-LWE

The selective weak attribute-hiding game (BTVW17 Definition 3.3 in its indistinguishability form):
the adversary names two attributes `x₀, x₁` and two messages `M₀, M₁`, gets `mpk` and a challenge
`Enc(mpk, x_β, M_β)`, and may ask keys for every `f` with `f(x₀) ≠ 0` and `f(x₁) ≠ 0`; a key for
another `f` is answered with the zero key (`keyOracle`). The adversary is a program with a key
oracle (`Adversary`); `game A x₀ x₁ x M` is the law of its output bit for the challenge `(x, M)`.

Keys come from a key sampler, whose law depends on `(B, B_f̂, p)` only (`KeySampler`), so the key
oracle depends on `mpk` only and the game is a fixed continuation `run` of the law of `(mpk, ct)`.

**The reduction.** A Ring-LWE instance (`Inst`) has public parts `(B, p, aᵢ, a_j)` and the parts
`(c, p₀, bᵢ, b_j)`, either `s · (public part) + error` (`ringLWEReal`) or uniform (`ringLWEUniform`).
`simMap` builds `(mpk, ct)` from an instance: `Ψᵢ = [aᵢ; bᵢ] + xᵢ G`, `B_j = a_j + ψ_j G̲`,
`c₀ = c`, `c_j = b_j`, `κ = p₀ + M ⌊q/2⌋`.

* `H0 = H1` exactly (`realLaw_eq`): on a real instance, `simMap` gives the real `(mpk, ct)`; the
  uniform `B_j` of `Setup` is `a_j + ψ_j G̲` for a uniform `a_j` (a one-time pad), and then
  `c_j = s(B_j − ψ_j G̲) + e_j = s a_j + e_j`.
* `H3` does not depend on the challenge (`h3Law_eq`): on a uniform instance, `[aᵢ; bᵢ] + xᵢ G` and
  `p₀ + M ⌊q/2⌋` are uniform whatever `x` and `M` are.

**Security** (`attributeHiding`): the games for `(x₀, M₀)` and `(x₁, M₁)` are within `δ₀ + δ₁`, the
Ring-LWE advantages of the explicit distinguishers `reduction A x₀ x₁ x₀ M₀` and
`reduction A x₀ x₁ x₁ M₁`. No statistical step remains.

**Limitation: the reduction is not efficient.** The distinguishers answer key queries by drawing
from the key sampler's law at `(B, B_f̂, p)` (the ideal law, `keyOracle`), with no trapdoor of
`B` or of `[B | B_f̂]`. The statement is an exact equality of laws, but it does not bound the
cost of the distinguishers, so it does not yet give attribute hiding against Ring-LWE as a
computational assumption. BTVW17 simulates keys with the trapdoor `W_f` of
`[B | B W_f + f(x) G]` after setting `B_j = B W_j + ψ_j G̲`; over this ring that needs
`(B, B W_j, e₀ W_j)` to be indistinguishable from `(B, U, e₀ W_j)`, which is not formalized.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

variable {N q k : ℕ} [NeZero q] (hk : q < 2 ^ k) {Attr : Type} [Fintype Attr] [DecidableEq Attr]

instance : Inhabited (SecretKey (R := Negacyclic (ZMod q) N) (k := k)) := ⟨⟨0, 0⟩⟩

variable (N) (Attr) in
/-- An adversary: given `mpk` and the challenge, a program that may ask keys for predicates and
outputs a bit. -/
abbrev Adversary :=
  MPK (ringSetting N q k hk Attr) → Ciphertext (ringSetting N q k hk Attr) →
    ProbOracleComp (fun _ : SLP Attr × Wire Attr => SecretKey (R := Negacyclic (ZMod q) N) (k := k)) Bool

variable {hk}

/-- The key oracle: keys for the predicates unauthorized for both `x₀` and `x₁`, the zero key
otherwise. -/
noncomputable def keyOracle (ks : KeySampler (Negacyclic (ZMod q) N) k) (x₀ x₁ : Attr → Bool)
    (mpk : MPK (ringSetting N q k hk Attr)) :
    (f : SLP Attr × Wire Attr) → StateT Unit PMF (SecretKey (R := Negacyclic (ZMod q) N) (k := k)) :=
  fun f _ => (if SLP.evalBool x₀ f.1 f.2 = true ∧ SLP.evalBool x₁ f.1 f.2 = true then keyGenLaw ks mpk f
    else PMF.pure default).map fun sk => (sk, ())

/-- The run of the adversary on `(mpk, ct)`. -/
noncomputable def run (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ : Attr → Bool)
    (v : MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) : PMF Bool :=
  (ProbOracleComp.runWith (keyOracle ks x₀ x₁ v.1) (A v.1 v.2) ()).map Prod.fst

variable (χ : PMF (ZMod q))

/-- `H0`: the law of `(mpk, ct)` in the real game for the challenge `(x, M)`. -/
noncomputable def realLaw (x : Attr → Bool) (M : Bool) :
    PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) := do
  let mpk ← setupLaw hk Attr
  let r ← encCoinsLaw hk Attr χ
  pure (mpk, encrypt mpk x M r)

/-- The game for the challenge `(x, M)`: the law of the adversary's bit. -/
noncomputable def game (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ x : Attr → Bool) (M : Bool) : PMF Bool :=
  (realLaw (hk := hk) χ x M).bind (run ks A x₀ x₁)

variable (N) (hk) (Attr) in
/-- The positions of the encodings. -/
abbrev J := (ringSetting N q k hk Attr).Attr × (ringSetting N q k hk Attr).ctBits.Index

variable (N) (hk) (Attr) in
/-- One side of a Ring-LWE instance: a row for `B` (or `c`), a ring element for `p` (or `p₀`), a row
for every attribute bit and a row for every encoding. -/
abbrev Side := Row N q k × Negacyclic (ZMod q) N × (Attr → Row N q k) × (J N hk Attr → Row N q k)

variable (N) (hk) (Attr) in
/-- A Ring-LWE instance: the public side and the other side. -/
abbrev Inst := Side N hk Attr × Side N hk Attr

/-- Real Ring-LWE: the public side uniform and the other side `s · (public side) + errors`, with
the secret and the errors of `Enc`'s coins. -/
noncomputable def ringLWEReal : PMF (Inst N hk Attr) := do
  let B ← unif (Row N q k)
  let p ← unif (Negacyclic (ZMod q) N)
  let r ← encCoinsLaw hk Attr χ
  let aJ ← unif (J N hk Attr → Row N q k)
  pure ((B, p, r.a, aJ),
    (scalar r.s * B + r.e₀, r.s * p + r.e', fun i => scalar r.s * r.a i + r.eΨ i,
      fun j => scalar r.s * aJ j + r.ej j))

/-- Uniform instances. -/
noncomputable def ringLWEUniform : PMF (Inst N hk Attr) := unif (Inst N hk Attr)

/-- `[a; b]`. -/
def stackRows (a b : Row N q k) : Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N) :=
  Matrix.of fun i col => if i = 0 then a 0 col else b 0 col

omit [NeZero q] in
theorem stackKey_eq (a e : Row N q k) (s : Negacyclic (ZMod q) N) :
    stackKey a e s = stackRows a (scalar s * a + e) := by
  ext i c
  fin_cases i <;> simp [stackRows, stackKey, scalar, Matrix.mul_apply]

/-- The attribute ciphertexts of an instance: `Ψᵢ = [aᵢ; bᵢ] + xᵢ G`. -/
noncomputable def instΨ (x : Attr → Bool) (v : Inst N hk Attr) :
    Attr → Matrix (Fin 2) (Col k) (Negacyclic (ZMod q) N) :=
  fun i => stackRows (v.1.2.2.1 i) (v.2.2.2.1 i) +
    bitR (R := Negacyclic (ZMod q) N) (x i) • (ringSetting N q k hk Attr).Γ.G

/-- `Setup*` and `Enc*` on an instance, for the challenge `(x, M)`. -/
noncomputable def simMap (x : Attr → Bool) (M : Bool) (v : Inst N hk Attr) :
    MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr) :=
  ({ B := v.1.1, p := v.1.2.1,
     Bj := fun j => v.1.2.2.2 j +
       bitsOf (ringSetting N q k hk Attr) (instΨ x v) j • (ringSetting N q k hk Attr).Γ₁.G },
   { Ψ := instΨ x v, c₀ := v.2.1, cj := v.2.2.2.2,
     κ := v.2.2.1 + (if M then (ringSetting N q k hk Attr).half else 0) })

/-- `H1`: `Setup*`, `Enc*` on a real instance. -/
noncomputable def h1Law (x : Attr → Bool) (M : Bool) :
    PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) :=
  (ringLWEReal χ).map (simMap x M)

/-- `H3`: `Setup*`, `Enc*` on a uniform instance. -/
noncomputable def h3Law (x : Attr → Bool) (M : Bool) :
    PMF (MPK (ringSetting N q k hk Attr) × Ciphertext (ringSetting N q k hk Attr)) :=
  (ringLWEUniform (N := N) (hk := hk) (Attr := Attr)).map (simMap x M)

/-! ### `H0 = H1` -/

/-- The real `mpk` with `B_j = a_j + ψ_j G̲`, `ψ` the bits of the real `Ψ`. -/
noncomputable def realMPK (x : Attr → Bool) (B : Row N q k) (p : Negacyclic (ZMod q) N)
    (r : EncCoins (ringSetting N q k hk Attr)) (aJ : J N hk Attr → Row N q k) :
    MPK (ringSetting N q k hk Attr) where
  B := B
  p := p
  Bj := fun j => aJ j + bitsOf (ringSetting N q k hk Attr)
    (fun i => stackKey (r.a i) (r.eΨ i) r.s +
      bitR (R := Negacyclic (ZMod q) N) (x i) • (ringSetting N q k hk Attr).Γ.G) j •
    (ringSetting N q k hk Attr).Γ₁.G

omit [DecidableEq Attr] [Fintype Attr] in
/-- On a real instance, `Setup*`, `Enc*` give the real `(mpk, ct)` with `B_j = a_j + ψ_j G̲`. -/
theorem simMap_real (x : Attr → Bool) (M : Bool) (B : Row N q k) (p : Negacyclic (ZMod q) N)
    (r : EncCoins (ringSetting N q k hk Attr)) (aJ : J N hk Attr → Row N q k) :
    simMap x M ((B, p, r.a, aJ), (scalar r.s * B + r.e₀, r.s * p + r.e',
      fun i => scalar r.s * r.a i + r.eΨ i, fun j => scalar r.s * aJ j + r.ej j)) =
    (realMPK x B p r aJ, encrypt (realMPK x B p r aJ) x M r) := by
  have hΨ : instΨ (hk := hk) x ((B, p, r.a, aJ), (scalar r.s * B + r.e₀, r.s * p + r.e',
      fun i => scalar r.s * r.a i + r.eΨ i, fun j => scalar r.s * aJ j + r.ej j)) =
      fun i => stackKey (r.a i) (r.eΨ i) r.s +
        bitR (R := Negacyclic (ZMod q) N) (x i) • (ringSetting N q k hk Attr).Γ.G := by
    funext i; simp only [instΨ, stackKey_eq]
  unfold simMap
  erw [hΨ]
  simp only [encrypt, realMPK, add_sub_cancel_right]

/-- **`H0 = H1`.** The real game's `(mpk, ct)` is `Setup*`, `Enc*` on a real Ring-LWE instance. -/
theorem realLaw_eq (x : Attr → Bool) (M : Bool) :
    realLaw (N := N) (hk := hk) χ x M = h1Law (N := N) (hk := hk) χ x M := by
  simp only [realLaw, setupLaw, h1Law, ringLWEReal, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
  refine congrArg (PMF.bind _) (funext fun B => ?_)
  refine congrArg (PMF.bind _) (funext fun p => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  simp only [simMap_real]
  exact (unif_bind_add (fun Bj => PMF.pure ((⟨B, Bj, p⟩ : MPK (ringSetting N q k hk Attr)),
    encrypt (⟨B, Bj, p⟩ : MPK (ringSetting N q k hk Attr)) x M r)) _).symm

/-! ### `H3` does not depend on the challenge -/

/-- The shift of an instance that moves the challenge `(x, M)` to `(x', M')`. -/
noncomputable def challengeShift (x x' : Attr → Bool) (M M' : Bool) : Inst N hk Attr :=
  ((0, 0, fun i => topRow ((bitR (R := Negacyclic (ZMod q) N) (x i) -
      bitR (x' i)) • (ringSetting N q k hk Attr).Γ.G), 0),
   (0, (if M then (ringSetting N q k hk Attr).half else 0) -
      (if M' then (ringSetting N q k hk Attr).half else 0),
    fun i => botRow ((bitR (R := Negacyclic (ZMod q) N) (x i) - bitR (x' i)) •
      (ringSetting N q k hk Attr).Γ.G), 0))

omit [DecidableEq Attr] [Fintype Attr] in
/-- `Setup*`, `Enc*` for `(x, M)` are those for `(x', M')` on the shifted instance. -/
theorem simMap_shift (x x' : Attr → Bool) (M M' : Bool) (v : Inst N hk Attr) :
    simMap x M v = simMap x' M' (v + challengeShift x x' M M') := by
  have hΨ : instΨ (hk := hk) x' (v + challengeShift x x' M M') = instΨ x v := by
    funext i a c
    fin_cases a <;>
      simp only [instΨ, challengeShift, stackRows, topRow, botRow, Matrix.add_apply,
        Matrix.smul_apply, Matrix.of_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply,
        smul_eq_mul, Fin.zero_eta, Fin.isValue, Fin.mk_one, ite_true, one_ne_zero, ite_false,
        sub_mul] <;> abel
  unfold simMap
  erw [hΨ]
  simp only [challengeShift, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero,
    Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  congr 1
  abel

/-- **`H3` does not depend on the challenge**: on a uniform instance, `[aᵢ; bᵢ] + xᵢ G` and
`p₀ + M ⌊q/2⌋` are uniform. -/
theorem h3Law_eq (x x' : Attr → Bool) (M M' : Bool) :
    h3Law (N := N) (hk := hk) x M = h3Law (N := N) (hk := hk) x' M' := by
  have h : (ringLWEUniform (N := N) (hk := hk) (Attr := Attr)).map
      (· + challengeShift x x' M M') = ringLWEUniform := by
    rw [ringLWEUniform, unif, ProbComp.eval_uniform]
    exact PMF.uniformOfFintype_map_equiv (Equiv.addRight _)
  simp only [h3Law]
  conv_rhs => rw [← h, PMF.map_comp]
  congr 1
  funext v
  exact simMap_shift x x' M M' v

/-! ### The reduction and the security theorem -/

/-- **The reduction to Ring-LWE**: on an instance, run `Setup*`, `Enc*` and the adversary. -/
noncomputable def reduction (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ x : Attr → Bool) (M : Bool) (v : Inst N hk Attr) : PMF Bool :=
  run ks A x₀ x₁ (simMap x M v)

/-- The game is the reduction on real Ring-LWE instances. -/
theorem game_eq (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ x : Attr → Bool) (M : Bool) :
    game χ ks A x₀ x₁ x M = (ringLWEReal χ).bind (reduction ks A x₀ x₁ x M) := by
  rw [game, realLaw_eq, h1Law, PMF.bind_map]
  rfl

/-- On uniform instances, the reduction does not depend on the challenge. -/
theorem reduction_uniform (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ x x' : Attr → Bool) (M M' : Bool) :
    ringLWEUniform.bind (reduction ks A x₀ x₁ x M) =
      ringLWEUniform.bind (reduction ks A x₀ x₁ x' M') := by
  have h := congrArg (fun μ => μ.bind (run ks A x₀ x₁)) (h3Law_eq (N := N) (hk := hk) x x' M M')
  simp only [h3Law, PMF.bind_map] at h
  exact h

/-- **Security of the ring variant under Ring-LWE** (BTVW17 Theorem 4.2). The games for `(x₀, M₀)`
and `(x₁, M₁)` are within `δ₀ + δ₁`, where `δ₀` and `δ₁` are the Ring-LWE advantages of the
reductions for the two challenges. -/
theorem attributeHiding (ks : KeySampler (Negacyclic (ZMod q) N) k) (A : Adversary N hk Attr)
    (x₀ x₁ : Attr → Bool) (M₀ M₁ : Bool) {δ₀ δ₁ : ℝ≥0∞}
    (hrlwe₀ : CloseTo ((ringLWEReal χ).bind (reduction ks A x₀ x₁ x₀ M₀))
      (ringLWEUniform.bind (reduction ks A x₀ x₁ x₀ M₀)) δ₀)
    (hrlwe₁ : CloseTo ((ringLWEReal χ).bind (reduction ks A x₀ x₁ x₁ M₁))
      (ringLWEUniform.bind (reduction ks A x₀ x₁ x₁ M₁)) δ₁) :
    CloseTo (game χ ks A x₀ x₁ x₀ M₀) (game χ ks A x₀ x₁ x₁ M₁) (δ₀ + δ₁) := by
  rw [game_eq, game_eq]
  rw [reduction_uniform ks A x₀ x₁ x₀ x₁ M₀ M₁] at hrlwe₀
  exact hrlwe₀.trans hrlwe₁.symm

end AdvancedEncryption.RingBTVW
