module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockPacking
public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import all SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockCount
import CslibFrontier.Foundations.Probability.Gaussian.MassBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Height one at horizontal rank 505

The finite packing test covers the whole interval from the minimum through 80.
Doubling the Gaussian width bounds the remainder of the *full* primal theta sum.
-/

public section
noncomputable section
namespace SigabaNeo.Wall1.FinalBlock
open ZLattice ProbabilityTheory

/-- The capped height-one event can only involve nonzero vectors in the centered
ball of radius 2√a. Each vector in that finite section costs its CBD half-space tail. -/
theorem cappedOneMass_le_sum {N d : ℕ} (B : FinalBlock N d) (a : ℝ) :
    cbdMass (fun w ↦ ‖projectedCBD B.Q w‖^2 ≤ a ∧
      ∃ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0:B.V) ∧
        ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2) ≤
      ∑ h ∈ (B.ballSection 0 (2*√a)).erase 0, Real.exp (-‖h‖^2/12) := by
  classical
  let F := (B.ballSection 0 (2*√a)).erase 0
  let hit (w : Plant N) (h : B.V) := ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2
  let cost (w : Plant N) (h : B.V) := if hit w h then CBDTail.jointWeight w else 0
  have pos w h : 0 ≤ cost w h := by dsimp [cost]; split <;> simp [weightNonneg]
  have one h : ∑ w, cost w h ≤ Real.exp (-‖h‖^2/12) := by
    simpa [cost, hit, Finset.sum_filter] using heightOneVector B.Q B.symmetric h.val (B.fixed h)
  apply le_trans _ (Finset.sum_le_sum (s := F) (fun h _ ↦ one h))
  unfold cbdMass
  rw [Finset.sum_filter, Finset.sum_comm (s := F)]
  apply Finset.sum_le_sum
  intro w _
  split_ifs with hw
  · obtain ⟨cap, h, hh, hn, col⟩ := hw
    have hy := Real.le_sqrt_of_sq_le cap
    have hhit := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp col
    have dist := norm_sub_le (projectedCBD B.Q w + h.val) (projectedCBD B.Q w)
    rw [add_sub_cancel_left] at dist
    have mem : h ∈ F := Finset.mem_erase.mpr ⟨hn, by
      simpa [ballSection] using And.intro hh (show ‖h.val‖ ≤ 2*√a by linarith)⟩
    simpa only [cost, show hit w h from col, ↓reduceIte] using
      (Finset.single_le_sum (fun z _ ↦ pos w z) mem)
  · exact Finset.sum_nonneg (fun h _ ↦ pos w h)

/-- Two-shell version with exact finite section sizes. The outer shell omits the
inner vectors. The minimum floor is needed only for the inner shell's weight. -/
theorem cappedOneMass_le_shells {N d : ℕ} (B : FinalBlock N d) (a : ℝ) {L r : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (floor : B.MinFloor L) :
    let F := (B.ballSection 0 (2*√a)).erase 0
    cbdMass (fun w ↦ ‖projectedCBD B.Q w‖^2 ≤ a ∧
      ∃ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0:B.V) ∧
        ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2) ≤
      ((F.filter (fun h ↦ ‖h‖ ≤ r)).card : ℝ) * Real.exp (-L^2/12) +
      ((F.filter (fun h ↦ r < ‖h‖)).card : ℝ) * Real.exp (-r^2/12) := by
  classical
  dsimp only
  apply (B.cappedOneMass_le_sum a).trans
  let F := (B.ballSection 0 (2*√a)).erase 0
  have weight h (hh : h ∈ F) : Real.exp (-‖h‖^2/12) ≤
      (if ‖h‖ ≤ r then Real.exp (-L^2/12) else Real.exp (-r^2/12)) := by
    obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hh
    have ⟨mem, _⟩ : h ∈ Submodule.span ℤ (Set.range B.basis) ∧ ‖h‖ ≤ 2*√a := by
      simpa [ballSection] using hm
    split_ifs with hl
    · apply Real.exp_le_exp.mpr
      linarith [(sq_le_sq₀ hL (norm_nonneg h)).2 (floor h mem hn)]
    · apply Real.exp_le_exp.mpr
      linarith [(sq_le_sq₀ hr (norm_nonneg h)).2 (le_of_not_ge hl)]
  apply (Finset.sum_le_sum weight).trans_eq
  rw [Finset.sum_ite (p := fun h : B.V ↦ ‖h‖ ≤ r)
    (fun _ ↦ Real.exp (-L^2/12)) (fun _ ↦ Real.exp (-r^2/12))]
  simp [not_le, F]
  apply congrArg Finset.card
  ext x
  simp
  constructor
  · rintro ⟨hh, hrx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr hh, hrx⟩
  · intro hx
    obtain ⟨hm, hrx⟩ := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_erase.mp hm, hrx⟩

private def lo (i : Fin 13) : ℚ := max 54.82 (54 + 2*(i.val:ℚ))
private def hi (i : Fin 13) : ℚ := 56 + 2*(i.val:ℚ)
private def c : Fin 13 → ℚ :=
  ![0.5224,0.5548,0.584,0.6104,0.6344,0.6562,0.6761,0.6943,0.7111,0.7265,0.7407,0.7538,0.766]
private def rho : Fin 13 → ℚ :=
  ![27.87,28.73,29.47,30.14,30.72,31.25,31.72,32.15,32.53,32.89,33.21,33.5,33.77]
private def rad : Fin 13 → ℚ :=
  ![40.45,43.18,45.83,48.42,50.96,53.45,55.9,58.32,60.71,63.07,65.41,67.72,70.02]

private theorem rows : ∀ i, 0 < rho i ∧ 0 ≤ rad i ∧ 0 ≤ c i ∧ c i ≤ 1 ∧
    (rho i)^2 + 2*rho i*0.001*(c i*hi i) + (c i*hi i)^2 ≤ (rad i)^2 ∧
    (rho i)^2 + 2*rho i*0.001*((1-c i)*hi i) + ((1-c i)*hi i)^2 ≤ 38.7^2 ∧
    (let v := (lo i)^2 / (12*505)
     rad i / rho i ≤ 0.9 * (1+v+v^2/2+v^3/6)) := by decide +kernel

private theorem covers {x : ℝ} (hl : 54.82 ≤ x) (hh : x ≤ 80) :
    ∃ i : Fin 13, ((lo i : ℚ) : ℝ) ≤ x ∧ x ≤ ((hi i : ℚ) : ℝ) := by
  let n := ⌊(x-54)/2⌋₊
  have hn : (n:ℝ) ≤ (x-54)/2 := Nat.floor_le (by linarith)
  have hn' : (x-54)/2 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases top : 12 ≤ n
  · refine ⟨12, ?_, ?_⟩ <;> norm_num [lo, hi] <;>
      linarith [show (12:ℝ) ≤ n by exact_mod_cast top]
  · refine ⟨⟨n, by omega⟩, ?_, ?_⟩ <;> simp [lo, hi] <;> (first | constructor <;> linarith | linarith)

variable {N : ℕ} (B : FinalBlock N 505)
private abbrev H := Submodule.span ℤ (Set.range B.basis)
private def wt (h : B.V) := Real.exp (-‖h‖^2/12)

set_option exponentiation.threshold 1024 in
private theorem shell_sum (floor : B.MinFloor 54.82) (i : Fin 13) (F : Finset B.V)
    (hF : ∀ h ∈ F, h ∈ H B ∧ h ≠ 0 ∧ (lo i : ℝ) ≤ ‖h‖ ∧ ‖h‖ ≤ (hi i : ℝ)) :
    ∑ h ∈ F, wt B h ≤ 400000 * (0.9:ℝ)^505 := by
  obtain ⟨hr, hR, hc, hc', ho, hd, hq⟩ := rows i
  replace ho := (Rat.cast_le (K := ℝ)).2 ho
  replace hd := (Rat.cast_le (K := ℝ)).2 hd
  replace hq := (Rat.cast_le (K := ℝ)).2 hq
  norm_num [Rat.cast_ofScientific] at ho hd hq
  have fp := shell_card_le F (r := (hi i : ℝ)) (ρ := (rho i : ℝ)) (R := (rad i : ℝ))
    (D := 38.7) (c := (c i : ℝ)) (ε := 0.001) (η := 4) (C := 400)
    (fun h hh ↦ ⟨(hF h hh).2.1, (hF h hh).2.2.2⟩) (fun h hh g hg hn ↦ by
      have m := floor (h-g) ((H B).sub_mem (hF h hh).1 (hF g hg).1) (sub_ne_zero.mpr hn)
      nlinarith [sq_nonneg (‖h-g‖-54.82)])
    (by exact_mod_cast hr) (by exact_mod_cast hR) (by norm_num) (by exact_mod_cast hc)
    (by exact_mod_cast hc') (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num; exact ho) (by norm_num; exact hd)
  rw [Module.finrank_eq_card_basis B.basis, Fintype.card_fin] at fp
  let v : ℝ := (lo i : ℝ)^2/(12*505)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ep := Real.sum_le_exp_of_nonneg hv 4
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at ep
  have p : (rad i : ℝ)/(rho i : ℝ) ≤ 0.9 * Real.exp v := by
    have q : (rad i : ℝ)/(rho i : ℝ) ≤ 0.9 * (1+v+v^2/2+v^3/6) := by
      dsimp [v]; norm_num; exact hq
    linarith
  have lo0 : 0 ≤ (lo i : ℝ) := by
    unfold lo; rw [Rat.cast_max]; exact le_max_of_le_left (by norm_num)
  have weights h (hh : h ∈ F) : wt B h ≤ Real.exp (-(505*v)) := by
    apply Real.exp_le_exp.mpr
    change -‖h‖^2/12 ≤ -(505*v)
    dsimp only [v]
    linarith [(sq_le_sq₀ lo0 (norm_nonneg h)).2 (hF h hh).2.2.1]
  have pw := pow_le_pow_left₀ (div_nonneg (by exact_mod_cast hR) (by exact_mod_cast hr.le)) p 505
  rw [mul_pow, ← Real.exp_nat_mul] at pw
  have total := Finset.sum_le_sum weights
  simp only [Finset.sum_const, nsmul_eq_mul] at total
  apply total.trans
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  norm_num only [Nat.cast_ofNat] at pw
  have q := fp.trans (mul_le_mul_of_nonneg_left pw (by norm_num : 0 ≤ (400:ℝ)/0.001))
  convert q using 1
  norm_num only [show (0.9:ℝ) = 9/10 by norm_num, show (400:ℝ)/0.001 = 400000 by norm_num]
  ring

private theorem finite_inner (floor : B.MinFloor 54.82) (F : Finset B.V)
    (hF : ∀ h ∈ F, h ∈ H B ∧ h ≠ 0 ∧ ‖h‖ ≤ 80) :
    ∑ h ∈ F, wt B h ≤ 13 * (400000 * (0.9:ℝ)^505) := by
  classical
  let K (i : Fin 13) := F.filter fun h ↦ (lo i : ℝ) ≤ ‖h‖ ∧ ‖h‖ ≤ (hi i : ℝ)
  have shell i := shell_sum B floor i (K i) (by
    intro h hh
    obtain ⟨m, low, high⟩ := Finset.mem_filter.mp hh
    exact ⟨(hF h m).1, (hF h m).2.1, low, high⟩)
  calc
    _ ≤ ∑ i, ∑ h ∈ K i, wt B h := by
      simp only [K, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨i, mem⟩ := covers (floor h (hF h hh).1 (hF h hh).2.1) (hF h hh).2.2
      simpa only [ite_eq_left mem] using (Finset.single_le_sum (f := fun i : Fin 13 ↦
        if (lo i : ℝ) ≤ ‖h‖ ∧ ‖h‖ ≤ (hi i : ℝ) then wt B h else 0)
        (fun _ _ ↦ by split <;> simp [wt, (Real.exp_pos _).le]) (Finset.mem_univ i))
    _ ≤ _ := by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ shell i)

set_option exponentiation.threshold 1024 in
/-- The full height-one theta excess, including its infinite tail. -/
theorem oneTheta_505_le (floor : B.MinFloor 54.82) : B.oneTheta ≤ 6.44e-14 := by
  classical
  let s := √(12*Real.pi)
  have hs : 0 < s := by dsimp [s]; positivity
  have s2 : s^2 = 12*Real.pi := Real.sq_sqrt (by positivity)
  let M := gaussianMass (H B) s 0
  have massEq : B.oneTheta = M - 1 := by
    unfold oneTheta M gaussianMass
    congr 1
    let b := B.basis.restrictScalars ℤ
    rw [← b.equivFun.toEquiv.symm.tsum_eq]
    apply tsum_congr
    intro z
    change Real.exp _ = gaussianWeight s ((b.equivFun.symm z).val - 0)
    rw [Module.Basis.equivFun_symm_apply, sub_zero, gaussianWeight, s2]
    congr 1
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower, b,
      Module.Basis.restrictScalars_apply, ← Int.cast_smul_eq_zsmul ℝ, vector]
    field_simp [Real.pi_ne_zero]
  have wide := (div_le_iff₀ (gaussianMass_pos (H B) s hs 0)).mp
    (gaussianMass_zero_div_le (H B) s hs (2*s) (by linarith))
  rw [show 2*s/s = 2 by field_simp, Module.finrank_eq_card_basis B.basis,
    Fintype.card_fin] at wide
  have wt1 (z : H B) : gaussianWeight s (z.val-0) = wt B z.val := by
    rw [sub_zero, gaussianWeight, s2, wt]
    congr 1; field_simp [Real.pi_ne_zero]
  have wt2 (z : H B) : gaussianWeight (2*s) (z.val-0) = Real.exp (-‖z.val‖^2/48) := by
    rw [sub_zero, gaussianWeight, mul_pow, s2]
    congr 1; field_simp [Real.pi_ne_zero]; ring
  let tail := Real.exp (-400) * gaussianMass (H B) (2*s) 0
  have cap : M ≤ 1 + 13*(400000*(0.9:ℝ)^505) + tail := by
    apply (summable_gaussianWeight (H B) s hs 0).tsum_le_of_sum_le
    intro F
    let small (z : H B) := z ≠ 0 ∧ ‖z.val‖ ≤ 80
    let K := F.filter small
    let e : H B ↪ B.V := ⟨Subtype.val, Subtype.val_injective⟩
    have inner := finite_inner B floor (K.map e) (by
      intro h hh
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hh
      have mem := (Finset.mem_filter.mp hz).2
      exact ⟨z.property, fun h ↦ mem.1 (Subtype.ext h), mem.2⟩)
    rw [Finset.sum_map] at inner
    have pt z : gaussianWeight s (z.val-0) ≤ (if z = (0:H B) then 1 else 0) +
        (if small z then wt B z.val else 0) +
          Real.exp (-400) * gaussianWeight (2*s) (z.val-0) := by
      have pos := mul_nonneg (Real.exp_pos (-400)).le (gaussianWeight_pos (2*s) (z.val-0)).le
      by_cases hz : z = 0
      · subst z; simp [small, gaussianWeight, (Real.exp_pos _).le]
      by_cases hm : small z
      · rw [wt1]; simpa only [hz, hm, ↓reduceIte, zero_add, le_add_iff_nonneg_right] using pos
      · simp only [hz, hm, ↓reduceIte, zero_add, wt1, wt2, wt, ← Real.exp_add, Real.exp_le_exp]
        have outside : 80 < ‖z.val‖ := lt_of_not_ge fun h ↦ hm ⟨hz,h⟩
        nlinarith [sq_nonneg (‖z.val‖-80)]
    have h := Finset.sum_le_sum (s := F) fun z _ ↦ pt z
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum] at h
    have single : (∑ z ∈ F.filter (· = (0:H B)), (1:ℝ)) ≤ 1 := by
      simp [Finset.filter_eq']; split <;> simp
    have hpart := (summable_gaussianWeight (H B) (2*s) (by positivity) 0).sum_le_tsum F
      (fun _ _ ↦ (gaussianWeight_pos _ _).le)
    exact h.trans (add_le_add (add_le_add single inner)
      (mul_le_mul_of_nonneg_left hpart (Real.exp_pos _).le))
  have smallTail : Real.exp (-400) * (2:ℝ)^505 ≤ 1e-18 := by
    rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718) (by linarith [Real.exp_one_gt_d9] :
      (2.718:ℝ) ≤ Real.exp 1) 400
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have M0 : 0 ≤ M := (gaussianMass_pos (H B) s hs 0).le
  have tailBound : tail ≤ 1e-18 * M := by
    calc
      _ ≤ Real.exp (-400) * ((2:ℝ)^505 * M) := mul_le_mul_of_nonneg_left wide (Real.exp_pos _).le
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right smallTail M0
  rw [massEq]
  have smallInner : 13*(400000*(0.9:ℝ)^505) ≤ 1e-15 := by norm_num
  linarith

theorem oneCharge_505_le (floor : B.MinFloor 54.82) (a : ℝ) :
    B.oneCharge a 54.82 ≤ 6.44e-14 := by
  unfold oneCharge
  split_ifs
  · norm_num
  · exact (min_le_right _ _).trans (B.oneTheta_505_le floor)

theorem cappedOneMass_505_le (floor : B.MinFloor 54.82) (a : ℝ) :
    cbdMass (fun w ↦ ‖projectedCBD B.Q w‖^2 ≤ a ∧
      ∃ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0:B.V) ∧
        ‖projectedCBD B.Q w + h.val‖^2 ≤ ‖projectedCBD B.Q w‖^2) ≤ 6.44e-14 :=
  (B.mass_oneEvent_le (a := a) floor).trans (B.oneCharge_505_le floor a)

end SigabaNeo.Wall1.FinalBlock
#print axioms SigabaNeo.Wall1.FinalBlock.cappedOneMass_le_shells
#print axioms SigabaNeo.Wall1.FinalBlock.oneTheta_505_le
#print axioms SigabaNeo.Wall1.FinalBlock.oneCharge_505_le
#print axioms SigabaNeo.Wall1.FinalBlock.cappedOneMass_505_le
