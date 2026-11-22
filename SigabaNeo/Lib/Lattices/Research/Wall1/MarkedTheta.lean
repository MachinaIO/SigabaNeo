import SigabaNeo.Lib.Lattices.Research.Wall1.MarkedLineage
import SigabaNeo.Lib.Lattices.Research.Wall1.GaussianSmoothing1D

/-! # Gaussian mass of the character annihilator along a marked history -/

noncomputable section
namespace SigabaNeo.Wall1

open Submodule WithLp
open scoped ENNReal RealInnerProductSpace
variable {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]

private def weight (s t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-s * t))

private theorem weight_add (s a b : ℝ) : weight s (a + b) = weight s a * weight s b := by
  simp [weight, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Gaussian mass in the scale convention exp(-s times squared norm). -/
def annihilatorTheta (S : MarkedFrame ι q) (s : ℝ) : ℝ≥0∞ :=
  ∑' x : S.label.ker, weight s (‖x.val.val‖ ^ 2)

def integerTheta (s : ℝ) : ℝ≥0∞ := ∑' j : ℤ, weight s ((j : ℝ) ^ 2)

theorem integerTheta_finite {s : ℝ} (hs : 0 < s) : integerTheta s < ⊤ := by
  unfold integerTheta weight
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ (Real.exp_pos _).le) (summable_int_gauss hs)]
  exact ENNReal.ofReal_lt_top

variable (S : MarkedFrame ι q) (u : S.space) (v : WindowSpace S.space)

private def parent (x : (S.append u v).label.ker) : S.label.ker :=
  ⟨dualParent S.lattice u v x.val, (retained_label_transport S.lattice u v S.mark q S.multiple
    x.val).symm.trans x.property⟩

omit [Fintype ι] [NeZero q] in
private theorem ext_coordinates {x y : (S.append u v).label.ker}
    (hf : parent S u v x = parent S u v y) (hs : x.val.val.val.snd = y.val.val.val.snd) :
    x = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply (WithLp.equiv 2 (S.space × ℝ)).injective
  exact Prod.ext (congrArg (fun z : S.label.ker ↦ z.val.val) hf) hs

omit [Fintype ι] [NeZero q] in
/-- When the winner has nonzero height every parent has at most one lift. -/
theorem annihilatorTheta_vertical (hv : v.snd ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    annihilatorTheta (S.append u v) s ≤ annihilatorTheta S s := by
  have hin : Function.Injective (parent S u v) := by
    intro x y h
    apply ext_coordinates S u v h
    have ho (z : (S.append u v).label.ker) :
        ⟪(parent S u v z).val.val, v.fst⟫ + v.snd * z.val.val.val.snd = 0 :=
      mem_orthogonal_singleton_iff_inner_left.mp z.val.val.property
    apply mul_left_cancel₀ hv
    have hx := ho x
    rw [h] at hx
    linarith only [hx, ho y]
  apply le_trans _ (tsum_comp_le_tsum_of_injective hin (fun z ↦ weight s (‖z.val.val‖ ^ 2)))
  apply tsum_le_tsum
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hs)
  exact pow_le_pow_left₀ (norm_nonneg _) (WithLp.norm_fst_le S.space x.val.val.val) 2

/-- An annihilator lift of a marked displacement has integral vertical coordinate.
Consequently at most one copy of the integer Gaussian factor is needed. -/
theorem annihilatorTheta_horizontal (a : ι → ℤ) (hu : u - ∑ i, a i • S.mark i ∈ S.lattice)
    (s : ℝ) : annihilatorTheta (S.append u v) s ≤ annihilatorTheta S s * integerTheta s := by
  have hz (x : (S.append u v).label.ker) : ∃ j : ℤ, (j : ℝ) = x.val.val.val.snd := by
    have h := retained_label_kick S.lattice u v S.mark q S.multiple a hu x.val
    have h0 : S.label (parent S u v x).val = 0 := (parent S u v x).property
    change (x.val.val.val.snd : UnitAddCircle) =
      -ZMod.toAddCircle (∑ i, a i • S.label (parent S u v x).val i) at h
    simp only [h0, Pi.zero_apply, smul_zero, Finset.sum_const_zero, map_zero, neg_zero] at h
    simpa using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  choose j hj using hz
  let f (x : (S.append u v).label.ker) := (parent S u v x, j x)
  have hin : Function.Injective f := by
    intro x y h
    obtain ⟨hf, hJ⟩ := Prod.mk.inj h
    exact ext_coordinates S u v hf (by rw [← hj, ← hj, hJ])
  let g (p : S.label.ker × ℤ) := weight s (‖p.1.val.val‖ ^ 2) * weight s ((p.2 : ℝ) ^ 2)
  calc
    _ = ∑' x, g (f x) := by
      apply tsum_congr
      intro x
      change weight s (‖x.val.val.val‖ ^ 2) = _ * _
      rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, weight_add, ← hj]
      rfl
    _ ≤ ∑' p, g p := tsum_comp_le_tsum_of_injective hin g
    _ = _ := by
      rw [tsum_prod']
      simp only [g, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, annihilatorTheta, integerTheta]

namespace MarkedHistory

variable {S R : MarkedFrame ι q}

def horizontalCount : {S : MarkedFrame ι q} → MarkedHistory R S → ℕ
  | _, .restart => 0
  | _, .append past _ _ _ v => past.horizontalCount + if v.snd = 0 then 1 else 0

theorem annihilatorTheta_le (path : MarkedHistory R S) {s : ℝ} (hs : 0 < s) :
    annihilatorTheta S s ≤ annihilatorTheta R s * integerTheta s ^ path.horizontalCount := by
  induction path with
  | restart => simp [horizontalCount]
  | @append P past a u hu v ih =>
    by_cases hv : v.snd = 0
    · simp only [horizontalCount, hv, ite_true, pow_succ, ← mul_assoc]
      exact (annihilatorTheta_horizontal P u v a hu s).trans (mul_le_mul_left ih _)
    · simpa [horizontalCount, hv] using (annihilatorTheta_vertical P u v hv hs.le).trans ih

end MarkedHistory

private theorem cube_theta (n : ℕ) (s : ℝ) :
    (∑' z : Fin n → ℤ, weight s (∑ i, (z i : ℝ) ^ 2)) = integerTheta s ^ n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    let e := Fin.consEquiv (n := n) (fun _ ↦ ℤ)
    rw [← e.tsum_eq, tsum_prod']
    simp only [e, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      weight_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    rw [ih, pow_succ']
    rfl

/-- For a cubic restart the dimension is a parameter. It suffices that all vectors of the
restart annihilator have integer coordinates in the given orthonormal basis. -/
theorem MarkedHistory.annihilatorTheta_cubic {R S : MarkedFrame ι q}
    (path : MarkedHistory R S) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ R.space)
    (hR : ∀ x : R.label.ker, x.val.val ∈ cubicModule b) {s : ℝ} (hs : 0 < s) :
    annihilatorTheta S s ≤ integerTheta s ^ (n + path.horizontalCount) := by
  have hb (x : R.label.ker) (i : Fin n) : ∃ j : ℤ, (j : ℝ) = b.repr x.val.val i := by
    have h := (b.toBasis.mem_span_iff_repr_mem ℤ x.val.val).1 (hR x) i
    simpa [OrthonormalBasis.coe_toBasis_repr_apply] using h
  choose f hf using hb
  have hin : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply b.repr.injective
    ext i
    rw [← hf, ← hf, h]
  have he (x : R.label.ker) : ‖x.val.val‖ ^ 2 = ∑ i, (f x i : ℝ) ^ 2 := by
    simp only [hf, ← b.repr.norm_map x.val.val, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have hbase : annihilatorTheta R s ≤ integerTheta s ^ n := by
    rw [← cube_theta]
    calc
      _ = ∑' x : R.label.ker, weight s (∑ i, (f x i : ℝ) ^ 2) := tsum_congr fun x ↦ congrArg _ (he x)
      _ ≤ _ := tsum_comp_le_tsum_of_injective hin (fun z ↦ weight s (∑ i, (z i : ℝ) ^ 2))
  rw [pow_add]
  exact (path.annihilatorTheta_le hs).trans (mul_le_mul_left hbase _)

/-- With the marked preimage equal to the cubic lattice at restart, its dual supplies
the integer-coordinate hypothesis of the path bound. -/
theorem MarkedHistory.annihilatorTheta_of_cubic_restart {R S : MarkedFrame ι q}
    (path : MarkedHistory R S) {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ R.space)
    (hR : markedPreimage R.lattice R.mark = cubicModule b) {s : ℝ} (hs : 0 < s) :
    annihilatorTheta S s ≤ integerTheta s ^ (n + path.horizontalCount) := by
  apply path.annihilatorTheta_cubic b _ hs
  intro x
  have hmem := (markLabel_ker R.lattice R.mark q R.multiple (NeZero.ne q)).le x.property
  change x.val.val ∈ metricDual (markedPreimage R.lattice R.mark) at hmem
  rwa [hR, metricDual_cubicModule] at hmem

/-- Ordinary convergent real theta series for a cubic restart. -/
theorem MarkedHistory.real_theta_bound {R S : MarkedFrame ι q} (path : MarkedHistory R S)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ R.space) (hR : markedPreimage R.lattice R.mark =
      cubicModule b) {s : ℝ} (hs : 0 < s) :
    Summable (fun x : S.label.ker ↦ Real.exp (-s * ‖x.val.val‖ ^ 2)) ∧
    (∑' x : S.label.ker, Real.exp (-s * ‖x.val.val‖ ^ 2)) ≤
      (∑' j : ℤ, Real.exp (-s * (j : ℝ) ^ 2)) ^ (n + path.horizontalCount) := by
  have h := path.annihilatorTheta_of_cubic_restart b hR hs
  have hf := ENNReal.pow_ne_top (n := n + path.horizontalCount) (integerTheta_finite hs).ne
  have hsumm := ENNReal.summable_toReal (ne_top_of_le_ne_top hf h)
  have hreal := ENNReal.toReal_mono hf h
  refine ⟨?_, ?_⟩
  · simpa [weight, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hsumm
  · simpa only [annihilatorTheta, integerTheta, weight, ENNReal.toReal_pow,
      ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.integerTheta_finite
#print axioms SigabaNeo.Wall1.annihilatorTheta_vertical
#print axioms SigabaNeo.Wall1.annihilatorTheta_horizontal
#print axioms SigabaNeo.Wall1.MarkedHistory.annihilatorTheta_le
#print axioms SigabaNeo.Wall1.MarkedHistory.annihilatorTheta_cubic
#print axioms SigabaNeo.Wall1.MarkedHistory.annihilatorTheta_of_cubic_restart
#print axioms SigabaNeo.Wall1.MarkedHistory.real_theta_bound
