module

public import SigabaNeo.Lib.Lattices.Research.Wall1.KleinProcedure
public import SigabaNeo.Lib.Lattices.Research.Wall1.CDTInversion
public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedPointGaussian

/-! # Fixed-point inversion tables for integer and coset Gaussians (Part 141, §3)

The quantizer floors the normalized approximate prefix at each interior cut. The
retained exact normalizer and the omitted probability refer to the same coset.
Taking q = 1 gives the ordinary tail-coordinate table.
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Function Real

noncomputable section

/-- Gaussian mass outside the truncation box, bounded using the scaled integer coordinate. -/
def cosetTailBound (s q R : ℝ) : ℝ :=
  2 * gs (s/q) (R/q) /
    ((1 - exp (-2 * π * (R/q) / (s/q)^2)) * gs (s/q) (1/2))

theorem cosetDraw_tail_le {s R : ℝ} (hs : 0 < s) (hR : 0 < R) {q : ℤ} (hq : 0 < q)
    (c : ℤ) :
    (∑' h : ℤ, if R < |(h : ℝ)| then cosetDraw s q c h else 0) ≤ cosetTailBound s q R := by
  let f (k : ℤ) := q*k+c
  have hf : Injective f := fun _ _ h ↦ mul_left_cancel₀ hq.ne' (add_right_cancel h)
  let g (h : ℤ) := if R < |(h : ℝ)| then cosetDraw s q c h else 0
  have hsup : support g ⊆ Set.range f := by
    intro h hh
    by_contra hn
    have hc : ¬h ≡ c [ZMOD q] := fun hc ↦ by
      obtain ⟨k, hk⟩ := hc.symm.dvd
      exact hn ⟨k, by dsimp [f]; omega⟩
    exact hh (by simp [g, cosetDraw, hc])
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let a : ℝ := -(c : ℝ) / q
  have hcoord (k : ℤ) : (k : ℝ) - a = (f k : ℝ) / q := by
    dsimp [a, f]; push_cast; field_simp; ring
  have hc (k : ℤ) : f k ≡ c [ZMOD q] := Int.modEq_iff_dvd.mpr ⟨-k, by dsimp [f]; ring⟩
  have he (k : ℤ) : g (f k) =
      (if R/q < |(k : ℝ)-a| then dg1 (s/q) a k else 0) := by
    have hnorm : -a = (c : ℝ)/q := by dsimp [a]; ring
    have habs : |(k : ℝ)-a| = |(f k : ℝ)| / q := by rw [hcoord, abs_div, abs_of_pos hqr]
    simp only [habs, div_lt_div_iff_of_pos_right hqr]
    simp only [g, cosetDraw, hc, ite_true,
      dg1, hnorm, thetaQ_eq hqr.ne', hcoord]
    have hw : gs s (f k) = gs (s/q) ((f k : ℝ)/q) := by
      unfold gs
      congr 1
      field_simp
    rw [hw]
  change (∑' h, g h) ≤ _
  rw [← hf.tsum_eq hsup, tsum_congr he]
  exact dg1_tail_le_all_scales (div_pos hs hqr) (div_pos hR hqr) a

namespace CDT

/-- Sum of the first j unnormalized weights. -/
def weightSum (w : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, w i

private theorem weightSum_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (weightSum w) :=
  monotone_nat_of_le_succ fun j ↦ by simp [weightSum, Finset.sum_range_succ, hw]

/-- Build all cuts from nonnegative weights, flooring each interior prefix and setting the
endpoint to the word range. With zero total weight the last bin receives every word. -/
def ofWeights (n P : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) : CDT n P where
  cut j := if j ≤ n then ⌊2^P * (weightSum w j / weightSum w (n+1))⌋₊ else 2^P
  mono := by
    intro i j hij
    have ht : 0 ≤ weightSum w (n+1) := Finset.sum_nonneg fun k _ ↦ hw k
    have hm := weightSum_mono hw
    dsimp only
    split_ifs with hi hj hj
    · exact Nat.floor_mono (by gcongr; exact hm hij)
    · have hrat : weightSum w i / weightSum w (n+1) ≤ 1 := by
        rcases ht.eq_or_lt with h | h
        · simp [← h]
        · exact (div_le_one h).mpr (hm (by omega))
      apply Nat.floor_le_of_le
      push_cast
      simpa using mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ (2:ℝ)^P)
    · omega
    · rfl
  first := by simp [weightSum]
  last := by simp

private theorem floor_error (P : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    |(⌊2^P*v⌋₊ : ℝ) / 2^P - v| ≤ 1 / 2^P := by
  have h : 0 < (2:ℝ)^P := by positivity
  have hle := Nat.floor_le (mul_nonneg h.le hv)
  rw [abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ h).mpr (by linarith))),
    neg_sub, le_div_iff₀ h, sub_mul, div_mul_cancel₀ _ h.ne']
  linarith [Nat.lt_floor_add_one ((2:ℝ)^P*v)]

private theorem weightSum_error {w v : ℕ → ℝ} {n j : ℕ} (hj : j ≤ n)
    {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ i < n, |w i - v i| ≤ ε) :
    |weightSum w j - weightSum v j| ≤ n * ε := by
  rw [weightSum, weightSum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range j, ε := Finset.sum_le_sum fun i hi ↦
      he i ((Finset.mem_range.mp hi).trans_le hj)
    _ ≤ n * ε := by simp; gcongr

/-- Prefix normalization stability. Use the approximate prefix fraction, which is in [0,1],
to control the error from the denominator. -/
private theorem ratio_error {a A b B U g : ℝ} (ha : 0 ≤ a) (haA : a ≤ A)
    (hA : 0 < A) (hg : 0 < g) (hgB : g ≤ B) (hU : 0 ≤ U)
    (hab : |a-b| ≤ U) (hAB : |A-B| ≤ U) : |a/A-b/B| ≤ 2*U/g := by
  have hB := hg.trans_le hgB
  have hfrac := div_nonneg ha hA.le
  have hone := (div_le_one hA).mpr haA
  have hid : (a/A-b/B)*B = (a-b) + (a/A)*(B-A) := by field_simp; ring
  have h := abs_add_le (a-b) (a/A*(B-A))
  rw [← hid, abs_mul, abs_of_pos hB, abs_mul, abs_of_nonneg hfrac, abs_sub_comm B A] at h
  have h' := mul_le_of_le_one_left (abs_nonneg (A-B)) hone
  exact ((le_div_iff₀ hB).mpr (by linarith)).trans
    (div_le_div_of_nonneg_left (by linarith) hg hgB)

/-- The recurrence value used by the integer and coset tables. -/
def gaussianWeight (F : ℕ) (E₁ E₂ : ℝ) (x : ℤ) : ℝ := (fpGaussian F E₁ E₂ x.natAbs).2

theorem gaussianWeight_nonneg (F : ℕ) {E₁ E₂ : ℝ} (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂)
    (x : ℤ) : 0 ≤ gaussianWeight F E₁ E₂ x := by
  have hmul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ fpMul F a b := by
    unfold fpMul
    apply div_nonneg _ (by positivity)
    exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ a*b*2^F by positivity)
  suffices ∀ j, 0 ≤ (fpGaussian F E₁ E₂ j).1 ∧ 0 ≤ (fpGaussian F E₁ E₂ j).2 from
    (this x.natAbs).2
  intro j
  induction j with
  | zero => exact ⟨h₁, zero_le_one⟩
  | succ j ih => exact ⟨hmul ih.1 h₂, hmul ih.2 ih.1⟩

/-- One absolute error bound for every retained unnormalized weight. -/
def gaussianWeightError (F R : ℕ) (δ : ℝ) : ℝ := ((R:ℝ)+2)^2 / 2 * (δ + 1 / 2^F)

/-- Per-draw SD bound for n+1 table entries. Here g bounds the retained exact weight below. -/
def gaussianDrawError (n P F R : ℕ) (δ g s q : ℝ) : ℝ :=
  n * (1 / 2^P + 2 * ((n+1:ℕ) * gaussianWeightError F R δ) / g) + cosetTailBound s q R

/-- The table uses the approximate weights of the listed physical integers, even for a coset. -/
def gaussianTable (n P F : ℕ) (x : ℕ → ℤ) {E₁ E₂ : ℝ} (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) :
    CDT n P := ofWeights n P (fun i ↦ gaussianWeight F E₁ E₂ (x i))
      (fun i ↦ gaussianWeight_nonneg F h₁ h₂ (x i))

/-- A finite list containing exactly the integers of c + qℤ in the truncation box, once each. -/
structure CosetBox (q c : ℤ) (R n : ℕ) (x : ℕ → ℤ) : Prop where
  inj : Set.InjOn x (Finset.range (n+1))
  mem_iff : ∀ h, h ∈ (Finset.range (n+1)).image x ↔ h.natAbs ≤ R ∧ h ≡ c [ZMOD q]

/-- End-to-end one-dimensional inversion bound, from input-constant errors to the law of
a uniform word mapped through the constructed table. -/
theorem gaussianTable_sdist_le {n P F R : ℕ} {s δ g E₁ E₂ : ℝ} {q c : ℤ} {x : ℕ → ℤ}
    (hs : 0 < s) (hq : 0 < q) (hR : 0 < R) (box : CosetBox q c R n x)
    (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1)
    (he₁ : |E₁-exp (-(π/s^2))| ≤ δ) (he₂ : |E₂-exp (-2*(π/s^2))| ≤ δ)
    (hsmall : ((n+1:ℕ):ℝ) * gaussianWeightError F R δ < g)
    (hg : g ≤ weightSum (fun i ↦ gs s (x i)) (n+1)) :
    sdist ((gaussianTable n P F x h₁.1 h₂.1).law x) (cosetDraw s q c) ≤
      gaussianDrawError n P F R δ g s q := by
  let w (i : ℕ) := gaussianWeight F E₁ E₂ (x i)
  let v (i : ℕ) := gs s (x i)
  let U := ((n+1:ℕ):ℝ) * gaussianWeightError F R δ
  let Z := thetaQ s q c
  have hZ : 0 < Z := thetaQ_pos hs (by exact_mod_cast hq.ne') _
  have hδ := (abs_nonneg _).trans he₁
  have hε : 0 ≤ gaussianWeightError F R δ := by unfold gaussianWeightError; positivity
  have hU : 0 ≤ U := mul_nonneg (Nat.cast_nonneg _) hε
  have hg0 : 0 < g := hU.trans_lt hsmall
  have hbox (i : ℕ) (hi : i < n+1) := (box.mem_iff (x i)).mp
    (Finset.mem_image_of_mem x (Finset.mem_range.mpr hi))
  have herr (j : ℕ) (hj : j ≤ n+1) : |weightSum w j - weightSum v j| ≤ U := by
    apply weightSum_error hj hε
    intro i hi
    have h := fpGaussian_weight_error F (show 0 ≤ π/s^2 by positivity) h₁ h₂ he₁ he₂ (hbox i hi).1
    have hx : (((x i).natAbs : ℝ))^2 = (x i : ℝ)^2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hx, show -(π/s^2)*(x i : ℝ)^2 = -π*(x i : ℝ)^2/s^2 by ring] at h
    exact h
  have hw0 (i : ℕ) : 0 ≤ w i := gaussianWeight_nonneg F h₁.1 h₂.1 _
  have hW : 0 < weightSum w (n+1) := by
    have he := (abs_le.mp (herr (n+1) le_rfl)).1
    change g ≤ weightSum v (n+1) at hg
    linarith
  have hprefix (j : ℕ) (hj : j ≤ n+1) :
      prefixMass (cosetDraw s q c) x j = weightSum v j / Z := by
    rw [prefixMass, weightSum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi ↦ by
      simp [cosetDraw, (hbox i ((Finset.mem_range.mp hi).trans_le hj)).2, v, Z]
  have hr (j : ℕ) (hj : j ≤ n) :
      |((gaussianTable n P F x h₁.1 h₂.1).cut j : ℝ) / 2^P -
        prefixMass (cosetDraw s q c) x j / prefixMass (cosetDraw s q c) x (n+1)| ≤
          1 / 2^P + 2*U/g := by
    have hj' := hj.trans (Nat.le_succ n)
    rw [hprefix j hj', hprefix (n+1) le_rfl, div_div_div_cancel_right₀ hZ.ne']
    have hsum : 0 ≤ weightSum w j := Finset.sum_nonneg fun i _ ↦ hw0 i
    exact (abs_sub_le _ (weightSum w j / weightSum w (n+1)) _).trans
      (add_le_add (by
        simpa [gaussianTable, ofWeights, hj, w] using
          floor_error P (div_nonneg hsum hW.le))
        (ratio_error hsum (weightSum_mono hw0 hj') hW hg0 hg hU (herr j hj') (herr _ le_rfl)))
  have ht := (gaussianTable n P F x h₁.1 h₂.1).sdist_conditional
    (cosetDraw_nonneg hs hq.ne' c) (cosetDraw_hasSum hs hq.ne' c) box.inj
    (by rw [hprefix _ le_rfl]; exact div_pos (hg0.trans_le hg) hZ)
    (fun i hi ↦ hr (i+1) hi)
  apply ht.trans
  unfold gaussianDrawError
  apply add_le_add_right
  let B (h : ℤ) := R < h.natAbs ∨ ¬h ≡ c [ZMOD q]
  have ho := one_sub_sum_le_mass (cosetDraw_nonneg hs hq.ne' c) (cosetDraw_hasSum hs hq.ne' c)
    box.inj B (fun h hn ↦ by
      by_contra hbad
      exact hn ((box.mem_iff h).mpr (by simpa [B, not_or] using hbad)))
  apply ho.trans
  refine (tsum_congr (g := fun h : ℤ ↦ if (R:ℝ) < |(h:ℝ)| then cosetDraw s q c h else 0)
    (fun h ↦ ?_)).le.trans (cosetDraw_tail_le hs (by exact_mod_cast hR) hq c)
  have hc : (R:ℝ) < |(h:ℝ)| ↔ R < h.natAbs := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast Iff.rfl
  by_cases hh : h ≡ c [ZMOD q] <;> simp [B, hc, hh, cosetDraw]

/-- The parameter choice of §4.1, with the §3.3 input-constant error budget. -/
theorem gaussianTable_sdist_le_960 {n : ℕ} {s g E₁ E₂ : ℝ} {q c : ℤ} {x : ℕ → ℤ}
    (hs : 0 < s) (hq : 0 < q) (box : CosetBox q c (2^22-1) n x)
    (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1)
    (he₁ : |E₁-exp (-(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088))
    (he₂ : |E₂-exp (-2*(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088))
    (hsmall : ((n+1:ℕ):ℝ) * gaussianWeightError 1024 (2^22-1)
      (1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)) < g)
    (hg : g ≤ weightSum (fun i ↦ gs s (x i)) (n+1)) :
    sdist ((gaussianTable n 960 1024 x h₁.1 h₂.1).law x) (cosetDraw s q c) ≤
      gaussianDrawError n 960 1024 (2^22-1) (1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)) g s q :=
  gaussianTable_sdist_le hs hq (by norm_num) box h₁ h₂ he₁ he₂ hsmall hg

end CDT
end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.cosetDraw_tail_le
#print axioms SigabaNeo.Wall1.CDT.gaussianTable_sdist_le
#print axioms SigabaNeo.Wall1.CDT.gaussianTable_sdist_le_960
