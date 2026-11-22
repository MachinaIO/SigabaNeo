module

public import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianCDT
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A uniform per-draw error at the Part 141 table precisions

The width conditions used below are 4q ≤ s and 20s ≤ R. They apply to the ordinary
integer table by taking q = 1. The input approximations carry the error from §3.3.
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Real

noncomputable section

/-- The unit-modulus table is precisely the integer draw used for a tail coordinate. -/
theorem cosetDraw_one_zero (s : ℝ) : cosetDraw s 1 0 = dg1 s 0 := by
  funext k
  simp [cosetDraw, dg1, theta1_zero_eq, Int.modEq_iff_dvd]

namespace CDT

/-- All retained integers for one table. -/
def cosetSupport (q c : ℤ) (R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R:ℤ)) R).filter (fun h ↦ h ≡ c [ZMOD q])

theorem mem_cosetSupport {q c h : ℤ} {R : ℕ} :
    h ∈ cosetSupport q c R ↔ h.natAbs ≤ R ∧ h ≡ c [ZMOD q] := by
  simp only [cosetSupport, Finset.mem_filter, Finset.mem_Icc]
  have he : h.natAbs ≤ R ↔ |h| ≤ (R:ℤ) := by
    rw [← Int.natCast_natAbs]; exact Nat.cast_le.symm
  rw [he, abs_le]

/-- Labels are in increasing order, with zero as an unused value beyond the last bin. -/
def sortedLabel (S : Finset ℤ) (i : ℕ) : ℤ :=
  if hi : i < S.card then (S.orderIsoOfFin rfl ⟨i, hi⟩ : S) else 0

theorem sortedLabel_box {q c : ℤ} {R n : ℕ} (hn : (cosetSupport q c R).card = n+1) :
    CosetBox q c R n (sortedLabel (cosetSupport q c R)) := by
  let S := cosetSupport q c R
  have hs : S.card = n+1 := hn
  have hlabel (i : Fin S.card) : sortedLabel S i = (S.orderIsoOfFin rfl i : ℤ) := by
    simp [sortedLabel, i.isLt]
  constructor
  · intro i hi j hj hij
    let a : Fin S.card := ⟨i, hs ▸ Finset.mem_range.mp hi⟩
    let b : Fin S.card := ⟨j, hs ▸ Finset.mem_range.mp hj⟩
    have he : S.orderIsoOfFin rfl a = S.orderIsoOfFin rfl b := Subtype.ext
      ((hlabel a).symm.trans (hij.trans (hlabel b)))
    exact congrArg Fin.val ((S.orderIsoOfFin rfl).injective he)
  · intro h
    rw [← mem_cosetSupport]
    change h ∈ (Finset.range (n+1)).image (sortedLabel S) ↔ h ∈ S
    constructor
    · rintro hh
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
      let a : Fin S.card := ⟨i, hs ▸ Finset.mem_range.mp hi⟩
      exact hlabel a ▸ (S.orderIsoOfFin rfl a).property
    · intro hh
      let a := (S.orderIsoOfFin rfl).symm ⟨h, hh⟩
      exact Finset.mem_image.mpr ⟨a.val, Finset.mem_range.mpr (hs ▸ a.isLt),
        (hlabel a).trans (congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _))⟩

private theorem count_box {q c : ℤ} {n R : ℕ} {x : ℕ → ℤ} (box : CosetBox q c R n x) :
    n+1 ≤ 2*R+1 := by
  have hin : (Finset.range (n+1)).image x ⊆ Finset.Icc (-(R:ℤ)) R := by
    intro h hh
    exact (Finset.mem_filter.mp (mem_cosetSupport.mpr ((box.mem_iff h).mp hh))).1
  have h := Finset.card_le_card hin
  rw [Finset.card_image_of_injOn box.inj, Finset.card_range, Int.card_Icc] at h
  omega

private theorem gs_half {s x : ℝ} (hs : 0 < s) (hx : |x| ≤ s/4) : 1/2 ≤ gs s x := by
  have hsq := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg x)
  have h : -(1/2:ℝ) ≤ -π*x^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith)
  exact (show (1/2:ℝ) ≤ -π*x^2/s^2 + 1 by linarith).trans (Real.add_one_le_exp _)

private theorem retained_ge_half {q c : ℤ} {n R : ℕ} {x : ℕ → ℤ} {s : ℝ}
    (hq : 0 < q) (hqs : 4*(q:ℝ) ≤ s) (hqR : q ≤ (R:ℤ)) (box : CosetBox q c R n x) :
    1/2 ≤ weightSum (fun i ↦ gs s (x i)) (n+1) := by
  let k := c % q
  have hk0 : 0 ≤ k := Int.emod_nonneg _ hq.ne'
  have hkq : k < q := Int.emod_lt_of_pos _ hq
  have hc : k ≡ c [ZMOD q] := by simp [k, Int.ModEq]
  have hk : k ∈ (Finset.range (n+1)).image x := (box.mem_iff k).mpr ⟨by omega, hc⟩
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
  have hkq' : (k:ℝ) < q := by exact_mod_cast hkq
  have hk0' : (0:ℝ) ≤ k := by exact_mod_cast hk0
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  apply (gs_half (s := s) (x := k) (by linarith) (by rw [abs_of_nonneg hk0']; linarith)).trans
  rw [← hik]
  exact Finset.single_le_sum (f := fun j ↦ gs s (x j)) (fun _ _ ↦ (gs_pos _ _).le) hi

set_option exponentiation.threshold 2048 in
private theorem tail_at_radius {s q : ℝ} (hq : 1 ≤ q) (hqs : 4*q ≤ s)
    (hR : 20*s ≤ 4194303) : cosetTailBound s q 4194303 ≤ 1/(2:ℝ)^1100 := by
  have hs : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  let v := s/q
  let z := (4194303:ℝ)/q
  have hv : 4 ≤ v := (le_div_iff₀ hq0).mpr hqs
  have hz : 20*v ≤ z := by dsimp [v,z]; rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hR hq0.le
  have hvmax : v ≤ 262144 := (div_le_iff₀ hq0).mpr (by linarith)
  have hv0 : 0 < v := by linarith
  have hz0 : 0 < z := by linarith
  have hexp : 1200 ≤ π*z^2/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv0)).mpr
    have h := mul_le_mul_of_nonneg_right pi_gt_three.le (sq_nonneg z)
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ 20*v) hz]
  have hdec : gs v z ≤ 1 / (2:ℝ)^1200 := by
    rw [gs, neg_mul, neg_div, exp_neg, one_div]
    apply inv_anti₀ (by positivity)
    calc (2:ℝ)^1200 ≤ (exp 1)^1200 := by gcongr; linarith [add_one_le_exp (1:ℝ)]
      _ = exp 1200 := by rw [← exp_nat_mul]; norm_num
      _ ≤ _ := exp_le_exp.mpr hexp
  let d := 2*π*z/v^2
  have hd : 1/262144 ≤ d := by
    apply (le_div_iff₀ (sq_pos_of_pos hv0)).mpr
    have h := mul_le_mul_of_nonneg_right pi_gt_three.le hz0.le
    nlinarith [mul_le_mul_of_nonneg_right hvmax hv0.le]
  have hd' : 1/524288 ≤ 1 - exp (-d) := by
    rw [exp_neg]
    have hlow : 1 + 1/262144 ≤ exp d := by linarith [add_one_le_exp d]
    have h := inv_anti₀ (by norm_num : (0:ℝ) < 1 + 1/262144) hlow
    norm_num at h
    linarith
  have hg := gs_half (s := v) (x := 1/2) hv0 (by rw [abs_of_nonneg (by norm_num)]; linarith)
  change 2*gs v z / ((1-exp (-2*π*z/v^2))*gs v (1/2)) ≤ _
  rw [show -2*π*z/v^2 = -d by dsimp [d]; ring]
  have hden := mul_le_mul hd' hg (by norm_num) (by linarith : 0 ≤ 1-exp (-d))
  have hden0 : 0 < (1-exp (-d))*gs v (1/2) := by linarith
  rw [div_le_iff₀ hden0]
  calc 2*gs v z ≤ 2*(1/(2:ℝ)^1200) := by gcongr
    _ ≤ (1/(2:ℝ)^1100)*(1/524288*(1/2)) := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

set_option exponentiation.threshold 2048 in
/-- Uniform numeric budget at the recorded table precisions and radius. It applies to
every residue, including the single residue at q=1. -/
theorem gaussianTable_sdist_le_pow_960 {n : ℕ} {s E₁ E₂ : ℝ} {q c : ℤ} {x : ℕ → ℤ}
    (hq : 0 < q) (hqs : 4*(q:ℝ) ≤ s) (hR : 20*s ≤ 4194303)
    (box : CosetBox q c (2^22-1) n x) (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1)
    (he₁ : |E₁-exp (-(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088))
    (he₂ : |E₂-exp (-2*(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)) :
    sdist ((gaussianTable n 960 1024 x h₁.1 h₂.1).law x) (cosetDraw s q c) ≤ 1/(2:ℝ)^930 := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hs : 0 < s := by linarith
  have hqR : q ≤ ((2^22-1:ℕ):ℤ) := by
    norm_num
    exact_mod_cast (show (q:ℝ) ≤ 4194303 by linarith)
  have hg := retained_ge_half hq hqs hqR box
  have hn := count_box box
  norm_num at hn
  have hN : ((n+1:ℕ):ℝ) ≤ 8388607 := by exact_mod_cast hn
  have hδ : (2:ℝ) ^ ((6.4:ℝ)-1088) ≤ 1/(2:ℝ)^1024 := by
    calc _ ≤ (2:ℝ)^(-(1024:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_neg (by norm_num), one_div]; norm_cast
  let ε := gaussianWeightError 1024 (2^22-1) (1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088))
  have hε : ε ≤ 1/(2:ℝ)^979 := by
    calc
      _ ≤ (((4194303:ℝ)+2)^2/2) * (1/2^1024 + 1/2^1024 + 1/2^1024) := by
        dsimp [ε, gaussianWeightError]; gcongr
      _ ≤ _ := by norm_num
  have hε0 : 0 ≤ ε := by dsimp [ε, gaussianWeightError]; positivity
  have hU := mul_le_mul hN hε hε0 (by norm_num)
  have hsmall : ((n+1:ℕ):ℝ)*ε < 1/2 := hU.trans_lt (by norm_num)
  apply (gaussianTable_sdist_le_960 hs hq box h₁ h₂ he₁ he₂ hsmall hg).trans
  unfold gaussianDrawError
  change (n:ℝ) * (1 / 2^960 + 2 * (((n+1:ℕ):ℝ)*ε) / (1/2)) +
    cosetTailBound s q 4194303 ≤ _
  have hn' : (n:ℝ) ≤ 8388607 := by exact_mod_cast (show n ≤ 8388607 by omega)
  calc
    _ ≤ 8388607 * (1/2^960 + 2*(8388607*(1/(2:ℝ)^979))/(1/2)) + 1/(2:ℝ)^1100 := by
      apply add_le_add _ (tail_at_radius hq1 hqs hR)
      gcongr
    _ ≤ _ := by norm_num


/-- Distribution produced by using the sorted, truncated coset as the table support. -/
def cosetTableLaw (q c : ℤ) (R P F : ℕ) {E₁ E₂ : ℝ} (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) : ℤ → ℝ :=
  let S := cosetSupport q c R
  (gaussianTable (S.card-1) P F (sortedLabel S) h₁ h₂).law (sortedLabel S)

/-- The normalized kernels of the concrete table sampler. -/
def tableDraws (q : ℤ) (R P F : ℕ) {E₁ E₂ : ℝ} (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) : KleinDraws where
  tail := cosetTableLaw 1 0 R P F h₁ h₂
  head c := cosetTableLaw q c R P F h₁ h₂
  tail_nonneg := push_nonneg _ (fun _ ↦ by positivity)
  head_nonneg _ := push_nonneg _ (fun _ ↦ by positivity)
  tail_hasSum := CDT.law_hasSum _ _
  head_hasSum _ := CDT.law_hasSum _ _

/-- Input constants and the specific accuracy contract of §3.3, at one width. -/
structure GaussianConstants (s : ℝ) where
  E₁ : ℝ
  E₂ : ℝ
  unit₁ : E₁ ∈ Set.Icc 0 1
  unit₂ : E₂ ∈ Set.Icc 0 1
  error₁ : |E₁-exp (-(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)
  error₂ : |E₂-exp (-2*(π/s^2))| ≤ 1/(2:ℝ)^1024 + 2 ^ ((6.4:ℝ)-1088)

theorem cosetTableLaw_sdist_le {s : ℝ} (e : GaussianConstants s) {q : ℤ} (hq : 0 < q)
    (hqs : 4*(q:ℝ) ≤ s) (hR : 20*s ≤ 4194303) (c : ℤ) :
    sdist (cosetTableLaw q c (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1) (cosetDraw s q c) ≤
      1/(2:ℝ)^930 := by
  let S := cosetSupport q c (2^22-1)
  have hqR : q ≤ (4194303:ℤ) := by exact_mod_cast (show (q:ℝ) ≤ 4194303 by linarith)
  have hmod := Int.emod_lt_of_pos c hq
  have hmod0 := Int.emod_nonneg c hq.ne'
  have hk : c % q ∈ S := mem_cosetSupport.mpr ⟨by norm_num; omega, by simp [Int.ModEq]⟩
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨_, hk⟩
  apply gaussianTable_sdist_le_pow_960 hq hqs hR _ e.unit₁ e.unit₂ e.error₁ e.error₂
  exact sortedLabel_box (show S.card = S.card-1+1 by omega)

/-- The widths used for the two recorded dimensions, at run j. -/
def recordedWidth (d j : ℕ) : ℝ :=
  3329 * sqrt (d * log (2*d+4) / π) * (2:ℝ)^((j:ℝ)/8)

theorem recordedWidth_bounds {d j : ℕ} (hd : d = 646 ∨ d = 647) (hj : j < 4) :
    4*3329 ≤ recordedWidth d j ∧ 20 * recordedWidth d j ≤ 4194303 := by
  have hlo : 646 ≤ (d:ℝ) := by rcases hd with rfl | rfl <;> norm_num
  have hhi : (d:ℝ) ≤ 647 := by rcases hd with rfl | rfl <;> norm_num
  have ht : 0 < 2*(d:ℝ)+4 := by positivity
  have hlog : 1 ≤ log (2*(d:ℝ)+4) :=
    (le_log_iff_exp_le ht).mpr (by linarith [exp_one_lt_d9])
  have hlog' : log (2*(d:ℝ)+4) ≤ 8 := by
    apply (log_le_iff_le_exp ht).mpr
    calc
      _ ≤ (2.5:ℝ)^8 := by norm_num; linarith
      _ ≤ (exp 1)^8 := by gcongr; linarith [exp_one_gt_d9]
      _ = _ := by rw [← exp_nat_mul]; norm_num
  let v := (d:ℝ) * log (2*d+4) / π
  have hd0 := Nat.cast_nonneg (α := ℝ) d
  have hbase : 16 ≤ v := by
    apply (le_div_iff₀ pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog hd0, pi_lt_four]
  have hlo' := (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 4) (by linarith : 0 ≤ v)).mpr
    (by linarith : (4:ℝ)^2 ≤ v)
  have hhi' : sqrt v ≤ 41.75 := by
    apply sqrt_le_iff.mpr ⟨by norm_num, (div_le_iff₀ pi_pos).mpr ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hlog' hd0, pi_gt_three]
  have hj' : (j:ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 by omega)
  have hlo'' : 1 ≤ (2:ℝ)^((j:ℝ)/8) := one_le_rpow (by norm_num) (by positivity)
  have hhi'' : (2:ℝ)^((j:ℝ)/8) ≤ 1.5 := by
    calc
      _ ≤ (2:ℝ)^(1/(2:ℝ)) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ _ := by rw [← sqrt_eq_rpow]; exact sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  change 4*3329 ≤ 3329*sqrt v*_ ∧ 20*(3329*sqrt v*_) ≤ 4194303
  constructor
  · nlinarith [mul_le_mul hlo' hlo'' (by norm_num) (sqrt_nonneg v)]
  · nlinarith [mul_le_mul hhi' hhi'' (by positivity : 0 ≤ (2:ℝ)^((j:ℝ)/8)) (by norm_num)]

/-- The concrete two-phase table sampler at any of the eight recorded widths. -/
theorem recorded_sdist_discGauss_le {r t j : ℕ} (hd : r+t = 646 ∨ r+t = 647) (hj : j < 4)
    (M : Matrix (Fin r) (Fin t) ℤ) (e : GaussianConstants (recordedWidth (r+t) j)) :
    let s := recordedWidth (r+t) j
    let A := tableDraws 3329 (2^22-1) 960 1024 e.unit₁.1 e.unit₂.1
    sdist (A.output M) (discGauss s 3329 M) ≤
      (r+t:ℝ) * (1/(2:ℝ)^930) + sdist (kleinLaw s 3329 M) (discGauss s 3329 M) := by
  obtain ⟨hlo, hhi⟩ := recordedWidth_bounds hd hj
  apply KleinDraws.sdist_discGauss_le_uniform _ _ (by linarith) (by norm_num)
  · rw [← cosetDraw_one_zero]
    exact cosetTableLaw_sdist_le e (by norm_num) (by norm_num; linarith) hhi 0
  · exact fun c ↦ cosetTableLaw_sdist_le e (by norm_num) (by simpa using hlo) hhi c

end CDT
end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.cosetDraw_one_zero
#print axioms SigabaNeo.Wall1.CDT.sortedLabel_box
#print axioms SigabaNeo.Wall1.CDT.gaussianTable_sdist_le_pow_960

#print axioms SigabaNeo.Wall1.CDT.cosetTableLaw_sdist_le
#print axioms SigabaNeo.Wall1.CDT.recordedWidth_bounds
#print axioms SigabaNeo.Wall1.CDT.recorded_sdist_discGauss_le
