import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockFourier
import SigabaNeo.Lib.Lattices.Research.Wall1.KleinFactorization
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The Gaussian mass of the integral section of a projected block -/

noncomputable section
namespace SigabaNeo.Wall1
open scoped RealInnerProductSpace
open Submodule

variable {N : ℕ} (S : Submodule ℝ (PlantSpace N))

/-- A rank-sized set of ambient coordinates separates points of the retained space. -/
theorem exists_separating_coordinates :
    ∃ e : Fin (Module.finrank ℝ S) ↪ Fin N,
      Function.Injective (fun x : S ↦ fun i ↦ x.val (e i)) := by
  classical
  let b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  let p := S.orthogonalProjectionOnto.toLinearMap
  let v := p ∘ b
  have span : Submodule.span ℝ (Set.range v) = ⊤ := by
    rw [show Set.range v = p '' Set.range b from Set.range_comp p b,
      ← Submodule.map_span, b.span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr fun x ↦ ⟨x, S.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  obtain ⟨κ, idx, hi, hsp, hli⟩ := exists_linearIndependent' ℝ v
  let : Fintype κ := Fintype.ofInjective idx hi
  let c := Module.Basis.mk hli ((hsp.trans span).ge)
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis c).symm
  refine ⟨e.symm.toEmbedding.trans ⟨idx, hi⟩, ?_⟩
  intro x y h
  apply InnerProductSpace.ext_inner_right_basis c
  intro i
  have he := congrFun h (e i)
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
    Function.Embedding.coeFn_mk] at he
  simp only [c, Module.Basis.coe_mk, Function.comp_apply, v]
  change ⟪x, S.orthogonalProjectionOnto _⟫ = ⟪y, S.orthogonalProjectionOnto _⟫
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left, S.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.inner_basisFun_real] using he

abbrev stdSection := integerSection (EuclideanSpace.basisFun (Fin N) ℝ) S

theorem section_coords (x : stdSection S) (i : Fin N) :
    ∃ z : ℤ, (z : ℝ) = x.val.val i := by
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have h := (b.toBasis.mem_span_iff_repr_mem ℤ x.val.val).mp x.property i
  rcases h with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa only [b, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_inner, eq_intCast] using hz

/-- All integral modes, including the zero mode, are dominated by a cubic theta series
in the retained rank. The coordinate minor may depend on the subspace. -/
private theorem integerSection_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun x : stdSection S ↦ Real.exp (-a * ‖x.val‖^2)) ∧
    (∑' x : stdSection S, Real.exp (-a * ‖x.val‖^2)) ≤
      (1 + 2 * Real.exp (-a) / (1 - Real.exp (-3*a))) ^ Module.finrank ℝ S := by
  classical
  obtain ⟨e, hin⟩ := exists_separating_coordinates S
  choose z hz using section_coords S
  let f (x : stdSection S) (i : Fin (Module.finrank ℝ S)) := z x (e i)
  have inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply hin
    funext i
    change x.val.val (e i) = y.val.val (e i)
    rw [← hz x, ← hz y]
    exact congrArg Int.cast (congrFun h i)
  let g (m : ℤ) := Real.exp (-a * (m : ℝ)^2)
  have sg : Summable g := summable_int_gauss ha
  have prodSum := hasSum_pi_prod (f := fun (_ : Fin (Module.finrank ℝ S)) ↦ g)
    (fun _ m ↦ (Real.exp_pos _).le) (fun _ ↦ sg.hasSum)
  have dom (x : stdSection S) : Real.exp (-a * ‖x.val‖^2) ≤ ∏ i, g (f x i) := by
    simp only [g, ← Real.exp_sum, ← Finset.mul_sum, f, hz]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (by linarith)
    change _ ≤ ‖x.val.val‖^2
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [← Finset.sum_map (f := fun i ↦ (x.val.val i)^2) Finset.univ e]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
  have summ := Summable.of_nonneg_of_le (fun x ↦ (Real.exp_pos _).le) dom
    (prodSum.summable.comp_injective inj)
  refine ⟨summ, ?_⟩
  have cmp := summ.tsum_le_tsum_of_inj f inj (fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦
    (Real.exp_pos _).le) dom prodSum.summable
  rw [prodSum.tsum_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at cmp
  apply cmp.trans
  apply pow_le_pow_left₀ (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)
  have pos (n : ℕ) : g ((n : ℤ)+1) = Real.exp (-a * ((n : ℝ)+1)^2) := by simp [g]
  have neg (n : ℕ) : g (-((n : ℤ)+1)) = Real.exp (-a * ((n : ℝ)+1)^2) := by simp [g]; left; ring
  rw [tsum_of_add_one_of_neg_add_one (f := g) (by simpa only [pos] using summable_tail ha)
    (by simpa only [neg] using summable_tail ha)]
  simp only [pos, neg, show g 0 = 1 by simp [g]]
  change tailSum a + 1 + tailSum a ≤ _
  rw [mul_div_assoc]
  linarith [tailSum_le ha]

theorem integerSection_gaussian_le {a : ℝ} (ha : 0 < a) :
    (∑' x : stdSection S, Real.exp (-a * ‖x.val‖^2)) ≤
      (1 + 2 * Real.exp (-a) / (1 - Real.exp (-3*a))) ^ Module.finrank ℝ S :=
  (integerSection_gaussian S ha).2

theorem integerSection_excess_eq {a : ℝ} (ha : 0 < a) :
    (∑' x : stdSection S, Real.exp (-a * ‖x.val‖^2)) - 1 =
      ∑' x : {x : stdSection S // x ≠ 0}, Real.exp (-a * ‖x.val.val‖^2) := by
  classical
  have h := (integerSection_gaussian S ha).1.sum_add_tsum_subtype_compl {0}
  let e : {x : stdSection S // x ∉ ({0} : Finset (stdSection S))} ≃
      {x : stdSection S // x ≠ 0} := Equiv.subtypeEquivRight fun _ ↦ by simp
  rw [← e.tsum_eq]
  simpa [e, add_comm, sub_eq_iff_eq_add] using h.symm

/-- The Fourier decay parameter π²/t at the recorded test scale. -/
def aliasDecay505 : ℝ := Real.pi ^ 2 / (505 / 1921)

private theorem alias_exp_small : Real.exp (-aliasDecay505) ≤ 4.954829e-17 := by
  have ha : 37.54358415 ≤ aliasDecay505 := by
    unfold aliasDecay505
    nlinarith [Real.pi_gt_d20, sq_nonneg (Real.pi - 3.14159265)]
  have small : (1.79789853 : ℝ) ≤ Real.exp (37.54358415 / 64) := by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 37.54358415/64) 12)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.79789853) small 64
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  apply (Real.exp_le_exp.mpr (neg_le_neg ha)).trans
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  norm_num
  linarith

/-- Excess of the integral section over its zero mode. -/
theorem integerSection_excess_505 (hd : Module.finrank ℝ S = 505) :
    (∑' x : stdSection S, Real.exp (-aliasDecay505 * ‖x.val‖^2)) - 1 < 5.00438e-14 := by
  have ha : 0 < aliasDecay505 := by unfold aliasDecay505; positivity
  have z := alias_exp_small
  have z3 : Real.exp (-3 * aliasDecay505) ≤ Real.exp (-aliasDecay505) :=
    Real.exp_le_exp.mpr (by linarith)
  have den : 0 < 1 - Real.exp (-3 * aliasDecay505) := by linarith
  have fac : 2 * Real.exp (-aliasDecay505) / (1 - Real.exp (-3 * aliasDecay505)) ≤
      9.909659e-17 := (div_le_iff₀ den).2 (by linarith)
  have bound := integerSection_gaussian_le S ha
  rw [hd] at bound
  have step : 1 + 2 * Real.exp (-aliasDecay505) / (1 - Real.exp (-3 * aliasDecay505)) ≤
      Real.exp 9.909659e-17 := by linarith [Real.add_one_le_exp (9.909659e-17 : ℝ)]
  have pw := pow_le_pow_left₀ (by positivity) step 505
  rw [← Real.exp_nat_mul] at pw
  have expBound := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0:ℝ) ≤ 505*9.909659e-17) (by norm_num)
  have total := bound.trans pw
  norm_num only [Nat.cast_ofNat] at total
  norm_num at expBound
  exact sub_lt_iff_lt_add.mpr ((total.trans expBound).trans_lt (by norm_num))

/-- At any determinant, multiply the excess by the sum of the Gaussian prefactors.
The numerical specialization uses the explicit audited upper bound on that sum. -/
theorem integerSection_charge_505 (hd : Module.finrank ℝ S = 505) {mass : ℝ}
    (hm : 0 ≤ mass) (hmodel : mass ≤ 4.46272e-125) :
    mass * ((∑' x : stdSection S, Real.exp (-aliasDecay505 * ‖x.val‖^2)) - 1) <
      2.23332e-138 := by
  have h := mul_le_mul_of_nonneg_left (integerSection_excess_505 S hd).le hm
  linarith

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.exists_separating_coordinates
#print axioms SigabaNeo.Wall1.integerSection_gaussian_le
#print axioms SigabaNeo.Wall1.integerSection_excess_505
#print axioms SigabaNeo.Wall1.integerSection_charge_505
