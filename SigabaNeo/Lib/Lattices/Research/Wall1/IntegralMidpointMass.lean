module

public import SigabaNeo.Lib.Lattices.Research.Wall1.IntegralMidpointCount
public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Cost
import SigabaNeo.Lib.Lattices.Research.Wall1.KleinFactorization
import Mathlib.Tactic

/-! A minimum-energy anchor within each parity class gives a termwise injection.
Its half-difference has squared norm at most the excess above the global minimum.
A product of two-sided geometric series bounds the resulting mass. -/

@[expose] public section
noncomputable section
namespace SigabaNeo.Wall1.CVP638

open SigabaNeo.SampleDeletion

private theorem geometric_int {u : ℝ} (hu : 0 ≤ u) (hu' : u < 1) :
    HasSum (fun a : ℤ ↦ u^a.natAbs) (1 + 2*u/(1-u)) := by
  have h := hasSum_geometric_of_lt_one hu hu'
  have hn : HasSum (fun a : ℕ ↦ u^(Int.negSucc a).natAbs) ((1-u)⁻¹*u) := by
    simpa only [Int.natAbs_negSucc, pow_succ] using h.mul_right u
  have hp : HasSum (fun a : ℕ ↦ u^(a:ℤ).natAbs) (1-u)⁻¹ := h
  convert hp.of_nat_of_neg_add_one (f := fun z : ℤ ↦ u^z.natAbs) hn using 1
  field_simp [(sub_pos.mpr hu').ne']
  ring

/-- Covers the empty class as well as classes containing multiple minimizers or none. -/
theorem parity_mass_le {d : ℕ} (S : Set (Fin d → ℤ)) (D : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hu' : u < 1) (midpoints : ∀ x ∈ S, ∀ y ∈ S, ∃ h : Fin d → ℤ,
      (∀ i, y i = x i + 2*h i) ∧ D ≤ normSq (fun i ↦ x i + h i)) :
    (∑' y : S, u ^ normSq y.val) ≤ u^D * Real.exp (d * (2*u/(1-u))) := by
  classical
  let G (z : Fin d → ℤ) := ∏ i, u^(z i).natAbs
  have hG := SigabaNeo.Wall1.hasSum_pi_prod (f := fun (_ : Fin d) (a : ℤ) ↦ u^a.natAbs)
    (fun _ _ ↦ pow_nonneg hu _) (fun _ ↦ geometric_int hu hu')
  have hp : HasSum (fun z ↦ u^D * G z) (u^D*(1+2*u/(1-u))^d) := by
    simpa [G] using hG.mul_left (u^D)
  apply le_trans (b := u^D*(1+2*u/(1-u))^d)
  · apply le_trans _ hp.tsum_eq.le
    by_cases hS : Nonempty S
    · obtain ⟨w⟩ := hS
      have hex : ∃ n, ∃ y : S, normSq y.val = n := ⟨_,w,rfl⟩
      obtain ⟨x,hx⟩ := Nat.find_spec hex
      choose diff he hm using fun y : S ↦ midpoints x.val x.property y.val y.property
      have inj : Function.Injective diff := by
        intro y z hy
        exact Subtype.ext (funext fun i ↦ by rw [he y i, he z i, hy])
      have bound (y : S) : u^normSq y.val ≤ u^D * G (diff y) := by
        have minimal := Nat.find_min' hex (show ∃ v : S, normSq v.val = normSq y.val from ⟨y,rfl⟩)
        have h := integral_midpoint_energy x.val (diff y)
        rw [← funext (he y)] at h
        have lower := hm y
        have h1 : (∑ i, (diff y i).natAbs) ≤ normSq (diff y) :=
          Finset.sum_le_sum fun i _ ↦ by
            exact Nat.le_self_pow (by decide : 2 ≠ 0) _
        unfold G
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        apply pow_le_pow_of_le_one hu hu'.le
        omega
      have hs := hp.summable.comp_injective inj
      have hs' := Summable.of_nonneg_of_le (fun y : S ↦ pow_nonneg hu (normSq y.val)) bound hs
      exact hs'.tsum_le_tsum_of_inj diff inj (fun z _ ↦ mul_nonneg (pow_nonneg hu _)
        (Finset.prod_nonneg fun _ _ ↦ pow_nonneg hu _)) bound hp.summable
    · have : IsEmpty S := not_nonempty_iff.mp hS
      rw [show (fun y : S ↦ u^normSq y.val) = (fun _ ↦ 0) from funext fun y ↦ isEmptyElim y, tsum_zero]
      exact tsum_nonneg fun z ↦ mul_nonneg (pow_nonneg hu _)
        (Finset.prod_nonneg fun _ _ ↦ pow_nonneg hu _)
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu D)
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity [sub_pos.mpr hu'])
      ((add_comm ..).trans_le (Real.add_one_le_exp _)) d

/-- The fixed inverse temperature and the midpoint estimate imply the factor 16/15. -/
theorem terminal_parity_mass (S : Set (Fin 638 → ℤ)) (D : ℕ)
    (midpoints : ∀ x ∈ S, ∀ y ∈ S, ∃ h : Fin 638 → ℤ,
      (∀ i, y i = x i + 2*h i) ∧ D ≤ normSq (fun i ↦ x i + h i)) :
    let u := Real.exp (-(Real.pi / variance levels))
    (∑' y : S, u^normSq y.val) ≤ u^D*(16/15) := by
  intro u
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ := (lt_div_iff₀ hlog).mp inverse_temperature
  have hu : u ≤ 1/65536 := by
    have h : u ≤ Real.exp (-(16 * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    convert h using 1
    rw [Real.exp_neg]
    have hpow := Real.exp_nat_mul (Real.log 2) 16
    norm_num [Real.exp_log] at hpow
    rw [hpow]
    norm_num
  have hpos : 0 ≤ u := (Real.exp_pos _).le
  have hu' : u < 1 := by linarith
  apply (parity_mass_le S D hpos hu' midpoints).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hpos _)
  apply (Real.exp_le_exp.mpr _).trans terminal_factor.le
  rw [mul_div_assoc', div_le_iff₀ (sub_pos.mpr hu')]
  norm_num
  linarith

end SigabaNeo.Wall1.CVP638

#print axioms SigabaNeo.Wall1.CVP638.parity_mass_le
#print axioms SigabaNeo.Wall1.CVP638.terminal_parity_mass
