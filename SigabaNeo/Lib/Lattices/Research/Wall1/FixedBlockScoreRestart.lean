module

public import SigabaNeo.Lib.Lattices.Research.Wall1.FixedBlockScore
public import SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
import all SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
import all SigabaNeo.Lib.Lattices.Research.Wall1.DecoupledDecoder
import all SigabaNeo.Lib.Lattices.Research.Wall1.RestartLift
import all SigabaNeo.Lib.Lattices.Research.Wall1.RestartReduction
import all SigabaNeo.Lib.Lattices.Research.Wall1.PlantBlindRestart
import Mathlib.Tactic

/-! # Restart certificate with the exact Part 181 score and actual prefix lengths -/

public section
namespace SigabaNeo.Wall1

open SampleDeletion CBDTail MultiBlock PlantBlindRestart RestartReduction RestartLift
open DecoupledDecoder AttackLattice Classical

/-- The score and the Babai charge of the same returned prefix must both pass. -/
def FinalBlock.scoreAccept {N d : ℕ} (B : FinalBlock N d) (J : ℕ) (p : ℕ → ℝ)
    (a s ℓ : ℝ) : Prop :=
  B.score a ≤ s ∧
    (∑ m ∈ Finset.range J, 2 * Real.exp (-(p m)^2 / 12)) ≤ ℓ

namespace AttackLattice

variable {Y ι : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] {k : ℕ}
  {r N d : Fin k → ℕ} {n q : ℕ}

/-- Acceptance depends only on the block rows, including any independent reducer coins. -/
def scoreAcc [NeZero q] {row : Y → Fin n → ZMod q}
    {σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)} {J : Fin k → ℕ}
    (hJ : ∀ i, J i + d i = N i) (red : Reducer row σ J d)
    (a : ∀ i, (Fin (r i) → Y) → ℝ) (s ℓ : ℝ) (i : Fin k) (z : Fin (r i) → Y) : Prop :=
  (finals hJ red i z).scoreAccept (J i) (fun m ↦ ‖(prefixes red i z).bs m‖)
    (a i z) s ℓ

/-- For disjoint blocks, rejection of every block or a wrong secret on the first
accepted block has probability at most the product of rejection probabilities plus
the terminal and prefix allowances. Both allowances use the same returned basis. -/
theorem restartScore_lwe [NeZero q] {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (row : Y → Fin n → ZMod q) (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)) (J : Fin k → ℕ)
    (hJ : ∀ i, J i + d i = N i) (red : Reducer row σ J d)
    (a : ∀ i, (Fin (r i) → Y) → ℝ)
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun x : (Σ i, Fin (r i)) ↦ b x.1 x.2))
    {c s ℓ : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ)
    (hcap : ∀ i z, scoreAcc hJ red a s ℓ i z → (finals hJ red i z).capTail (a i z) ≤ c) :
    let acc := scoreAcc hJ red a s ℓ
    (failProb w (plantWeight n cbdQ) acc (attackFail row σ b red) b : ℝ) ≤
      (∏ i, (rejectProb w acc i : ℝ)) + (c + s) + ℓ := by
  intro acc
  let ρ := plantWeight (ι := ι) n cbdQ
  have hρ : ∑ p, ρ p = 1 := plantWeight_sum n cbdQ_sum
  have hρ0 p : 0 ≤ ρ p := mul_nonneg (Finset.prod_nonneg fun _ _ ↦ cbdQ_nonneg _)
    (Finset.prod_nonneg fun _ _ ↦ cbdQ_nonneg _)
  let R := finals hJ red
  let pre := prefixes red
  let π := lwePlant σ b
  let lf := liftFail pre J π
  have imp i p z (hf : attackFail row σ b red i p z) : decodeFail R π lf i p z := by
    apply outputFail_imp (fun _ ↦ chooseSVP_spec) (fun _ ↦ chooseLift_spec)
      (fun i z ↦ nullLattice₀ (blockDesign row z) (σ i)) R pre J π
      (compatible_ofBasis (hJ i) (red i z))
    intro eq
    exact (attackFail_iff row σ b red i p z).1 hf (by rw [eq, readSecret_plantVec])
  have mono := failProb_mono (F := attackFail row σ b red) (F' := decodeFail R π lf)
    hw0 hρ0 acc b (fun i p z _ ↦ imp i p z)
  have per i z (hz : acc i z) : (plantProb ρ (fun p ↦ decodeFail R π lf i p z) : ℝ) ≤ (c + s) + ℓ := by
    have hπ := lwePlant_marginal σ b i (fun i₁ i₂ eq ↦ by
      have := hb (a₁ := ⟨i, i₁⟩) (a₂ := ⟨i, i₂⟩) eq
      simpa using this)
    have hU := plantProb_not_unique hρ R π i hπ z
    have hT := ((R i z).failure_le_capTail_add_score (a i z)).trans
      (add_le_add (hcap i z hz) hz.1)
    let gp (j : Fin k) (m : ℕ) := if j = i then ‖(pre i z).bs m‖ else 0
    have hpre : prefixFloor pre J gp i z := by intro m _; simp [gp]
    have hLift := plantProb_liftFail_le pre J π gp (by intros; dsimp [gp]; split <;> positivity)
      i hπ hpre
    simp only [gp, ite_eq_left _] at hLift
    have hB : (plantProb ρ (fun p ↦ lf i p z) : ℝ) ≤ ℓ := hLift.trans hz.2
    have hUnion : plantProb ρ (fun p ↦ decodeFail R π lf i p z) ≤
        plantProb ρ (fun p ↦ ¬Unique R π i p z) + plantProb ρ (fun p ↦ lf i p z) := by
      unfold plantProb decodeFail
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ ↦ ?_
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (hρ0 p)
      by_cases h1 : Unique R π i p z <;> by_cases h2 : lf i p z <;> simp [h1, h2]
    have hUnionR := (Rat.cast_le (K := ℝ)).2 hUnion
    rw [Rat.cast_add, hU] at hUnionR
    linarith
  have avg := failProb_le_real hw hw0 hρ acc _ b hb per
  have hp : (0 : ℝ) ≤ ∏ i, (rejectProb w acc i : ℝ) :=
    Finset.prod_nonneg fun i _ ↦ by exact_mod_cast rejectProb_nonneg hw0 acc i
  apply le_trans (show (failProb w ρ acc (attackFail row σ b red) b : ℝ) ≤ _ from
    (Rat.cast_le (K := ℝ)).2 mono)
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hc hs) hℓ) hp]

end AttackLattice
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.AttackLattice.restartScore_lwe
