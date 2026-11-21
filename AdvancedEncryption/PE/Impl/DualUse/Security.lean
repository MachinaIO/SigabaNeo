import PE.Impl.DualUse.Hybrid5

/-!
# Attribute hiding of the dual-use scheme under Ring-LWE

The real game for the challenge `(x, M)` is the law of `(mpk, ct)` (`realGame`) followed by any
continuation `D`: the adversary with a key oracle that depends on `mpk` only (the ideal key law,
`DualUse.idealKeyLaw`, which the reductions sample with the trapdoor `W_f`,
`DualUse.keyLaw_real_eq_sim`). The chain of hybrids:

1. `B_j = B₀ W_j + ψ_j G̲` — leftover hash lemma (`hybrid1`);
2. encodings `c₀ W_j + e_j` — noise flooding (`hybrid4`);
3. `B₁ = [1 | a | G̲ − (t a + e)]` → `[1 | a | z]` — Ring-LWE with secret `t` (`reduction3`);
4. `(c₀, c₁, κ₀)` uniform — normal-form Ring-LWE (`reduction5`, `real5_eq`, `unif5_eq`);
5. `A Rᵢ`, `A W_j` uniform — leftover hash lemma (`hybrid6`), and the final view does not depend
   on the challenge (`finalView_indep`).

**Security** (`attributeHiding`): the games for `(x₀, M₀)` and `(x₁, M₁)` are within twice the
statistical terms of hybrids 1, 4 and 6 plus the Ring-LWE advantages of the four reductions.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib.Probability
open scoped ENNReal

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] {k : ℕ} {S : Setting R k}
  {Wd : Type} [Fintype Wd] [DecidableEq Wd] [Nonempty Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

variable (lawRest : PMF (Rest S Wd (TrapCol k)))
  (lawE : PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) R))

omit [DecidableEq R] [Nonempty Wd] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
/-- The view of hybrid 4 is a continuation of the trapdoor part `B₁`. -/
theorem viewW_bind_B₁ (lawB₁ : PMF (Matrix (Fin 1) (TrapCol k) R)) (lawP : PMF R)
    (x : S.Attr → Bool) (M : Bool) (cj) :
    viewW lawB₁ lawP lawRest lawE x M cj =
      lawB₁.bind fun B₁ => viewW (PMF.pure B₁) lawP lawRest lawE x M cj := by
  unfold viewW
  simp only [PMF.pure_bind]
  conv_lhs => enter [2, B₀]; rw [PMF.bind_comm]
  conv_lhs => rw [PMF.bind_comm]

variable (S) in
/-- `B₁ = [1 | a | G̲ − b]` from a Ring-LWE pair `(a, b)`. -/
def toB₁ (ab : Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R) :
    Matrix (Fin 1) (TrapCol k) R :=
  trapRowU ab.1 (S.Γ₁.G - ab.2)

omit [Fintype R] [DecidableEq R] [Fintype Wd] [DecidableEq Wd] [Nonempty Wd] [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
/-- The trapdoor part of the real setup is `toB₁ (a, t a + e)`. -/
theorem trapRow_eq_toB₁ (a e : Matrix (Fin 1) (Col k) R) (t : R) :
    trapRow S a e t = toB₁ S (a, scalar t * a + e) := by
  ext i c
  rcases c with c | c | c <;> simp [trapRow, toB₁, trapRowU, RingBTVW.scalar, Matrix.mul_apply]

/-- **Ring-LWE with secret `t`, real**: `(a, t a + e)`. -/
noncomputable def inst3Real (χ : PMF R) :
    PMF (Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R) := do
  let a ← PMF.uniformOfFintype (Matrix (Fin 1) (Col k) R)
  let t ← χ
  let e ← rowLaw χ (Col k)
  pure (a, scalar t * a + e)

/-- **Ring-LWE with secret `t`, uniform.** -/
noncomputable def inst3Unif : PMF (Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R) :=
  PMF.uniformOfFintype _

omit [DecidableEq R] [Fintype Wd] [DecidableEq Wd] [Nonempty Wd] [Fintype S.Attr]
  [DecidableEq S.Attr] [DecidableEq S.ctBits.Index] in
theorem inst3Unif_map : inst3Unif.map (toB₁ S) = lawB₁u (k := k) (R := R) := by
  unfold inst3Unif lawB₁u
  rw [PMF.map, uniform_prod_bind]
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  congr 1; funext a
  exact bind_uniform_equiv ((Equiv.subRight S.Γ₁.G).trans (Equiv.neg _))
    (fun z => PMF.pure (trapRowU a z)) |>.symm.trans (by
      congr 1; funext u; simp [toB₁]) |>.symm

/-- The real game: the law of `(mpk, ct)` for the challenge `(x, M)`, with the real setup
(`B₀`, `B_j`, `p` uniform, `B₁ = [1 | a | G̲ − (t a + e)]`) and the coins of `Enc`. -/
noncomputable def realGame (χ : PMF R) (x : S.Attr → Bool) (M : Bool) :
    PMF (MPK S Wd (TrapCol k) × Ciphertext S Wd (TrapCol k)) :=
  realView ((inst3Real χ).map (toB₁ S)) (PMF.uniformOfFintype R)
    (lawCoins (lawRestNF lawRmBin χ) lawE) x M

/-- **The reduction of hybrid 3**: the view of hybrid 4 for `B₁ = toB₁ (a, b)`, then `D`. -/
noncomputable def reduction3 (χ : PMF R) (x : S.Attr → Bool) (M : Bool)
    (D : MPK S Wd (TrapCol k) × Ciphertext S Wd (TrapCol k) → PMF Bool)
    (ab : Matrix (Fin 1) (Col k) R × Matrix (Fin 1) (Col k) R) : PMF Bool :=
  (viewW (PMF.pure (toB₁ S ab)) (PMF.uniformOfFintype R) (lawRestNF lawRmBin χ) lawE x M
    floodCj).bind D

variable (S Wd) in
/-- The statistical term of hybrid 1. -/
noncomputable def delta1 : ℝ≥0∞ :=
  ENNReal.ofReal (Fintype.card (JC S) *
    (Real.sqrt (Fintype.card (Fin 1 → R) * (2 ^ Fintype.card Wd : ℝ)⁻¹) / 2))

variable (S Wd) in
/-- The statistical term of hybrid 6. -/
noncomputable def delta6 : ℝ≥0∞ :=
  ENNReal.ofReal (Fintype.card (HC S) *
    (Real.sqrt (Fintype.card (Fin 2 → R) * (2 ^ Fintype.card Wd : ℝ)⁻¹) / 2))

/-- **One challenge**: the real game is close to the final view, up to the statistical terms and
the Ring-LWE advantages `δ₃`, `δ₅` of the reductions for this challenge. -/
theorem game_close (χ : PMF R) (D : MPK S Wd (TrapCol k) × Ciphertext S Wd (TrapCol k) → PMF Bool)
    (x : S.Attr → Bool) (M : Bool) {ε δ₃ δ₅ : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestNF (S := S) (Wd := Wd) lawRmBin χ).support,
      ∀ w : JC S → (Wd → Bool),
        CloseTo (lawE.map fun e j => e j + rest.2.1 * wMat w j) lawE ε)
    (h₃ : CloseTo ((inst3Real χ).bind (reduction3 lawE χ x M D))
      (inst3Unif.bind (reduction3 lawE χ x M D)) δ₃)
    (h₅ : CloseTo ((nfReal χ).bind fun i => (reduction5 (S := S) lawRmBin lawE x M i).bind D)
      (nfUnif.bind fun i => (reduction5 (S := S) lawRmBin lawE x M i).bind D) δ₅) :
    CloseTo ((realGame lawE χ x M).bind D) ((finalView (Wd := Wd) lawB₁u lawE x M).bind D)
      (delta1 S Wd + ε + δ₃ + δ₅ + delta6 S Wd) := by
  -- hybrid 1
  have e1 := ((hybrid1 (Wd := Wd) ((inst3Real χ).map (toB₁ S)) (PMF.uniformOfFintype R)
    (lawCoins (lawRestNF lawRmBin χ) lawE) x M).bind_left D).symm
  rw [← viewW_real_eq] at e1
  -- hybrid 4
  have e4 := ((hybrid4 ((inst3Real χ).map (toB₁ S)) (PMF.uniformOfFintype R)
    (lawRestNF lawRmBin χ) lawE x M hflood).bind_left D).symm
  -- hybrid 3
  have h3eq : (viewW ((inst3Real χ).map (toB₁ S)) (PMF.uniformOfFintype R)
      (lawRestNF lawRmBin χ) lawE x M floodCj).bind D =
      (inst3Real χ).bind (reduction3 lawE χ x M D) := by
    rw [viewW_bind_B₁, PMF.bind_map, PMF.bind_bind]
    rfl
  have h3eq' : inst3Unif.bind (reduction3 lawE χ x M D) =
      (viewW lawB₁u (PMF.uniformOfFintype R) (lawRestNF lawRmBin χ) lawE x M floodCj).bind D := by
    rw [viewW_bind_B₁ (lawB₁ := lawB₁u), ← inst3Unif_map (S := S), PMF.bind_map, PMF.bind_bind]
    rfl
  -- hybrid 5
  have h5eq : (viewW lawB₁u (PMF.uniformOfFintype R) (lawRestNF lawRmBin χ) lawE x M floodCj).bind D
      = (nfReal χ).bind fun i => (reduction5 (S := S) lawRmBin lawE x M i).bind D := by
    rw [real5_eq, PMF.bind_bind]
  have h5eq' : (nfUnif.bind fun i => (reduction5 (S := S) lawRmBin lawE x M i).bind D) =
      (h5View (Wd := Wd) lawB₁u lawE x M).bind D := by
    rw [← unif5_eq, PMF.bind_bind]
  -- hybrid 6
  have e6 := (hybrid6 (Wd := Wd) lawB₁u lawE x M).bind_left D
  rw [h3eq] at e4
  rw [h3eq', h5eq] at h₃
  rw [h5eq'] at h₅
  unfold realGame
  exact (((e1.trans e4).trans h₃).trans h₅).trans e6

/-- **Attribute hiding under Ring-LWE** (BTVW17 Theorem 4.2, dual-use ring variant): for any
continuation `D` (the adversary with a key oracle depending on `mpk` only), the games for
`(x₀, M₀)` and `(x₁, M₁)` are within twice the statistical terms of hybrids 1, 4, 6 plus the
Ring-LWE advantages of the reductions of hybrids 3 and 5 for both challenges. -/
theorem attributeHiding (χ : PMF R)
    (D : MPK S Wd (TrapCol k) × Ciphertext S Wd (TrapCol k) → PMF Bool)
    (x₀ x₁ : S.Attr → Bool) (M₀ M₁ : Bool) {ε δ₃₀ δ₃₁ δ₅₀ δ₅₁ : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestNF (S := S) (Wd := Wd) lawRmBin χ).support,
      ∀ w : JC S → (Wd → Bool),
        CloseTo (lawE.map fun e j => e j + rest.2.1 * wMat w j) lawE ε)
    (h₃₀ : CloseTo ((inst3Real χ).bind (reduction3 lawE χ x₀ M₀ D))
      (inst3Unif.bind (reduction3 lawE χ x₀ M₀ D)) δ₃₀)
    (h₃₁ : CloseTo ((inst3Real χ).bind (reduction3 lawE χ x₁ M₁ D))
      (inst3Unif.bind (reduction3 lawE χ x₁ M₁ D)) δ₃₁)
    (h₅₀ : CloseTo ((nfReal χ).bind fun i => (reduction5 (S := S) lawRmBin lawE x₀ M₀ i).bind D)
      (nfUnif.bind fun i => (reduction5 (S := S) lawRmBin lawE x₀ M₀ i).bind D) δ₅₀)
    (h₅₁ : CloseTo ((nfReal χ).bind fun i => (reduction5 (S := S) lawRmBin lawE x₁ M₁ i).bind D)
      (nfUnif.bind fun i => (reduction5 (S := S) lawRmBin lawE x₁ M₁ i).bind D) δ₅₁) :
    CloseTo ((realGame lawE χ x₀ M₀).bind D) ((realGame lawE χ x₁ M₁).bind D)
      ((delta1 S Wd + ε + δ₃₀ + δ₅₀ + delta6 S Wd) + (delta1 S Wd + ε + δ₃₁ + δ₅₁ + delta6 S Wd)) := by
  have g₀ := game_close lawE χ D x₀ M₀ hflood h₃₀ h₅₀
  have g₁ := game_close lawE χ D x₁ M₁ hflood h₃₁ h₅₁
  rw [finalView_indep (Wd := Wd) lawB₁u lawE x₀ x₁ M₀ M₁] at g₀
  exact g₀.trans g₁.symm

end AdvancedEncryption.DualUse
