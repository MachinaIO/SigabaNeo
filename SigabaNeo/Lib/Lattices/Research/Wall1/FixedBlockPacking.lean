module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Counting a separated shell by intersections of two balls -/

public section
namespace SigabaNeo.Wall1
open MeasureTheory Metric
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite collection of short vectors with strictly negative off-diagonal inner products
has bounded cardinality, by expanding the squared norm of its sum. -/
private theorem overlap_le (F : Finset E) {u C η : ℝ} (hη : 0 < η) (hC0 : 0 ≤ C)
    (hC : u ≤ (C-1)*η) (x : E) (hs : ∀ h ∈ F, ‖h-x‖^2 ≤ u)
    (hd : ∀ h ∈ F, ∀ g ∈ F, h ≠ g → 2*(u+η) ≤ ‖h-g‖^2) : (F.card : ℝ) ≤ C := by
  classical
  by_cases he : F.Nonempty
  · have hn : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr he
    have each h (hh : h ∈ F) : (∑ g ∈ F, ⟪h-x,g-x⟫) ≤ u - (F.card-1:ℝ)*η := by
      calc
        _ ≤ ∑ g ∈ F, (if g = h then u else -η) := by
          apply Finset.sum_le_sum
          intro g hg
          split_ifs with eq
          · subst g; simpa [real_inner_self_eq_norm_sq] using hs h hh
          · have dist := hd h hh g hg (Ne.symm eq)
            rw [show h-g = (h-x)-(g-x) by abel, norm_sub_sq_real] at dist
            linarith [hs h hh, hs g hg]
        _ = _ := by
          rw [← Finset.sum_erase_add _ _ hh]
          rw [Finset.sum_congr rfl (g := fun _ ↦ -η) (fun g hg ↦
            ite_eq_right (Finset.ne_of_mem_erase hg))]
          simp [Finset.card_erase_of_mem hh, Nat.cast_sub (Finset.one_le_card.mpr he)]
          ring
    have pos := sq_nonneg ‖∑ h ∈ F, (h-x)‖
    rw [← real_inner_self_eq_norm_sq, sum_inner] at pos
    simp_rw [inner_sum] at pos
    have cmp := Finset.sum_le_sum each
    simp only [Finset.sum_const, nsmul_eq_mul] at cmp
    have := nonneg_of_mul_nonneg_right (pos.trans cmp) hn
    exact (le_of_mul_le_mul_right (by linarith : (F.card : ℝ)*η ≤ C*η) hη)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, Nat.cast_zero]
    exact hC0

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A unit ball compressed in one direction has volume fraction ε. Translating this
ellipsoid inside the intersection of two balls gives a lower bound on the lens volume. -/
private theorem lens_lower {h : E} (hn : h ≠ 0) {r ρ R D c ε : ℝ}
    (hr : ‖h‖ ≤ r) (hρ : 0 < ρ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hc' : c ≤ 1) (he : 0 < ε) (he' : ε ≤ 1)
    (outer : ρ^2 + 2*ρ*ε*(c*r) + (c*r)^2 ≤ R^2)
    (inner : ρ^2 + 2*ρ*ε*((1-c)*r) + ((1-c)*r)^2 ≤ D^2) :
    ε * ρ ^ Module.finrank ℝ E * volume.real (closedBall (0:E) 1) ≤
      volume.real (closedBall 0 R ∩ closedBall h D) := by
  let u := ‖h‖⁻¹ • h
  have hp := norm_pos_iff.mpr hn
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hp.ne']
  have back : ‖h‖ • u = h := by simp [u, smul_smul, hp.ne']
  let f := (innerₗ E) u
  let T := LinearMap.transvection f ((ε-1) • u)
  have det : LinearMap.det T = ε := by
    rw [LinearMap.transvection.det]
    change 1 + ⟪u, (ε-1) • u⟫ = ε
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  have estimate (y : E) (hy : ‖y‖ ≤ ρ) (b A : ℝ) (hb : |b| ≤ A) :
      ‖T y + b • u‖^2 ≤ ρ^2 + 2*ρ*ε*A + A^2 := by
    let z := ⟪y,u⟫
    have hz : |z| ≤ ρ := (abs_real_inner_le_norm y u).trans (by simpa [hu] using hy)
    have form : T y = y + ((ε-1)*z) • u := by
      rw [LinearMap.transvection.apply, smul_smul, mul_comm]
      change y + ((ε-1)*⟪u,y⟫) • u = y + ((ε-1)*⟪y,u⟫) • u
      rw [real_inner_comm u y]
    have hty : ‖T y‖^2 ≤ ρ^2 := by
      rw [form, norm_add_sq_real, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs,
        real_inner_smul_right]
      have loss : (ε^2-1)*z^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he')]) (sq_nonneg _)
      change ‖y‖^2 + 2 * ((ε-1)*z*z) + ((ε-1)*z)^2 ≤ _
      nlinarith [sq_le_sq₀ (norm_nonneg y) hρ.le |>.2 hy]
    have axial : ⟪T y,u⟫ = ε*z := by
      rw [form, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      change z + _ = _; ring
    have mixed : b*(ε*z) ≤ A*(ε*ρ) := (le_abs_self (b*(ε*z))).trans (by
      rw [abs_mul, abs_mul, abs_of_pos he]
      exact mul_le_mul hb (mul_le_mul_of_nonneg_left hz he.le) (by positivity) ((abs_nonneg _).trans hb))
    rw [norm_add_sq_real, real_inner_smul_right, axial, norm_smul, hu, mul_one, Real.norm_eq_abs,
      sq_abs]
    nlinarith [sq_le_sq₀ (abs_nonneg b) ((abs_nonneg b).trans hb) |>.2 hb, sq_abs b]
  have sub : (fun v ↦ v + c • h) '' (T '' closedBall (0:E) ρ) ⊆
      closedBall 0 R ∩ closedBall h D := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hy
    have shift : c • h = (c*‖h‖) • u := by rw [← smul_smul, back]
    have shift' : T y + c • h - h = T y + ((c-1)*‖h‖) • u := by
      rw [← smul_smul, back, sub_smul, one_smul]; abel
    constructor
    · rw [mem_closedBall, dist_zero_right, shift]
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      exact (estimate y hy _ _ (by rw [abs_of_nonneg (by positivity)]; gcongr)).trans outer
    · rw [mem_closedBall, dist_eq_norm, shift']
      apply (sq_le_sq₀ (norm_nonneg _) hD).mp
      apply (estimate y hy _ _ ?_).trans inner
      rw [abs_mul, abs_of_nonpos (by linarith : c-1 ≤ 0), abs_of_nonneg (norm_nonneg h),
        neg_sub]
      gcongr
  have cmp := measureReal_mono (μ := volume) sub
    ((lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_closedBall_lt_top).ne)
  rw [measureReal_def, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap, det, abs_of_pos he, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal he.le, ← measureReal_def, Measure.addHaar_real_closedBall' _ _ hρ.le]
    at cmp
  linarith

/-- A dimension-dependent shell bound. The volume of each lens is bounded below by
compressing a ball along its axis. Its overlap is controlled by pairwise separation. -/
theorem shell_card_le (F : Finset E) {r ρ R D c ε η C : ℝ}
    (hn : ∀ h ∈ F, h ≠ 0 ∧ ‖h‖ ≤ r)
    (hd : ∀ h ∈ F, ∀ g ∈ F, h ≠ g → 2*(D^2+η) ≤ ‖h-g‖^2)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hc' : c ≤ 1) (he : 0 < ε) (he' : ε ≤ 1)
    (hη : 0 < η) (hC0 : 0 ≤ C) (hC : D^2 ≤ (C-1)*η)
    (outer : ρ^2 + 2*ρ*ε*(c*r) + (c*r)^2 ≤ R^2)
    (inner : ρ^2 + 2*ρ*ε*((1-c)*r) + ((1-c)*r)^2 ≤ D^2) :
    (F.card : ℝ) ≤ C / ε * (R / ρ)^Module.finrank ℝ E := by
  classical
  let A (h : E) := closedBall (0:E) R ∩ closedBall h D
  have meas h : MeasurableSet (A h) := measurableSet_closedBall.inter measurableSet_closedBall
  have fin h : volume (A h) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_closedBall_lt_top).ne
  let I (h : E) := (A h).indicator (fun _ ↦ (1:ℝ))
  have int h : Integrable (I h) volume := (integrable_indicator_iff (meas h)).2
    (integrableOn_const (fin h))
  have pt x : (∑ h ∈ F, I h x) ≤ (closedBall (0:E) R).indicator (fun _ ↦ C) x := by
    by_cases hx : x ∈ closedBall (0:E) R
    · rw [Set.indicator_of_mem hx]
      let K := F.filter fun h ↦ x ∈ A h
      have eq : (∑ h ∈ F, I h x) = (K.card : ℝ) := by
        simp [I, K, Set.indicator_apply]
      rw [eq]
      apply overlap_le K hη hC0 hC x
      · intro h hh
        have mem := (Finset.mem_filter.mp hh).2.2
        have hh' : ‖h-x‖ ≤ D := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using mem
        exact (sq_le_sq₀ (norm_nonneg _) hD).2 hh'
      · exact fun h hh g hg ↦ hd h (Finset.mem_filter.mp hh).1 g (Finset.mem_filter.mp hg).1
    · have hz h : x ∉ A h := fun hm ↦ hx hm.1
      simp [I, hz, hx]
  have integrated := integral_mono (integrable_finsetSum F (fun h _ ↦ int h))
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) pt
  rw [integral_finsetSum F (fun h _ ↦ int h), integral_indicator_const C measurableSet_closedBall,
    smul_eq_mul, Measure.addHaar_real_closedBall' volume _ hR] at integrated
  have vols h : ∫ x, I h x = volume.real (A h) := integral_indicator_one (meas h)
  simp_rw [vols] at integrated
  have low := Finset.sum_le_sum (s := F) fun h hh ↦
    lens_lower (hn h hh).1 (hn h hh).2 hρ hR hD hc hc' he he' outer inner
  simp only [Finset.sum_const, nsmul_eq_mul] at low
  have hv : 0 < volume.real (closedBall (0:E) 1) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume _ zero_lt_one).ne' measure_closedBall_lt_top.ne
  have cmp := low.trans integrated
  rw [div_pow]
  have cancel : ((F.card:ℝ) * (ε * ρ^Module.finrank ℝ E)) * volume.real (closedBall (0:E) 1) ≤
      (C * R^Module.finrank ℝ E) * volume.real (closedBall (0:E) 1) := by linarith only [cmp]
  have ans := (le_div_iff₀ (mul_pos he (pow_pos hρ _))).2 ((mul_le_mul_iff_left₀ hv).mp cancel)
  convert ans using 1
  ring

end SigabaNeo.Wall1
#print axioms SigabaNeo.Wall1.shell_card_le
