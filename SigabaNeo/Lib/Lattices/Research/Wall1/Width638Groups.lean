module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlock
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Geometry
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

/-! Part 236. Disjoint local CVP queries and the first passing candidate on fresh rows. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.Width638
open SigabaNeo.SampleDeletion MultiBlock QaryMembership Matrix Finset
open scoped Classical
variable {r n q m : ℕ} [Fact q.Prime]

@[expose] def plant (e : Fin r → Digit 3) (s : Fin n → Digit 3) : Grid r n :=
  Sum.elim (centered ∘ e) (centered ∘ s)

/-- Insert a CVP answer into the repository's candidate-list interface. Height one
merely selects the supported-secret branch of that interface. The underlying query is CVP. -/
def asBlockOracle (O : ∀ k, CVPOracle k n q) : Attack.Oracle n q :=
  fun k A y ↦ Sum.elim (fun i ↦ O k |>.closest A y (.inl i))
    (Sum.elim (fun j ↦ O k |>.closest A y (.inr j)) (fun _ ↦ 1))

def localBad (s : Fin n → Digit 3) (z : Fin r → Row n q 3) :=
  Bad (plant (fun i ↦ (z i).1) s) (fun i ↦ (z i).2)

def miss (r q : ℕ) [Fact q.Prime] (s : Fin n → Digit 3) : ℚ :=
  expect (rowWeight n q 3) (fun z : Fin r → Row n q 3 ↦ if localBad s z then 1 else 0)

theorem observed (b : Fin r → Fin m) (s : Fin n → Digit 3) (e : Fin m → Digit 3)
    (A : Design m n q) :
    output (fun i ↦ A (b i)) (plant (e ∘ b) s) = Attack.lweSample A s e ∘ b := by
  funext i
  apply add_comm

theorem candidate_of_good (O : ∀ k, CVPOracle k n q) (hq : 6 < q)
    (b : Fin r → Fin m) (s : Fin n → Digit 3) (e : Fin m → Digit 3) (A : Design m n q)
    (hg : ¬ Bad (plant (e ∘ b) s) (fun i ↦ A (b i))) :
    Attack.candidate 3 (asBlockOracle O) A (Attack.lweSample A s e) b = some (centered ∘ s) := by
  have hc := closest_of_good (O r) _ _ hg
  rw [observed] at hc
  simp only [Attack.candidate, asBlockOracle, Sum.elim_inr, true_or, ↓reduceIte, one_mul]
  change Attack.decode 3 q (fun j ↦ (O r).closest _ (Attack.lweSample A s e ∘ b) (.inr j)) = _
  rw [hc]
  have hv (j : Fin n) := Attack.valMinAbs_small (η := 3) hq _ (Attack.support_bound (s j))
  simp [Attack.decode, plant, hv, Attack.support_bound, Function.comp_def]

/-- The discarded sample coordinate is recovered by centered residual lifting. -/
theorem lift_discarded (A : Design m n q) (s : Fin n → Digit 3) (e : Fin m → Digit 3)
    (hq : 6 < q) (i : Fin m) :
    (Attack.lweSample A s e i - A i ⬝ᵥ (fun j ↦ (centered (s j) : ZMod q))).valMinAbs =
      centered (e i) := by
  simp [Attack.lweSample, Attack.valMinAbs_small (η := 3) hq _ (Attack.support_bound (e i))]

/-- Write the joint LWE law as a product over the secret and the paired error/design rows. -/
theorem lwe_expect (P : (Fin n → Digit 3) → (Fin m → Digit 3) → Design m n q → Prop) :
    Attack.lweProb m n q 3 P = expect (cbdWeight 3) (fun s ↦ expect (rowWeight n q 3)
      (fun z : Fin m → Row n q 3 ↦ if P s (fun i ↦ (z i).1) (fun i ↦ (z i).2) then 1 else 0)) := by
  unfold Attack.lweProb
  have h (s : Fin n → Digit 3) := MultiBlock.expect_rows (r := m)
    (fun e A ↦ if P s e A then (1:ℚ) else 0)
  have eqF : (fun s ↦ MultiBlock.expect (rowWeight n q 3) (fun z : Fin m → Row n q 3 ↦
      if P s (fun i ↦ (z i).1) (fun i ↦ (z i).2) then 1 else 0)) = _ := funext h
  rw [eqF, MultiBlock.expect]
  rw [sum_div]
  apply sum_congr rfl
  intro s _
  simp only [cbdWeight, prod_div_distrib, prod_const, card_univ, Fintype.card_fin, sum_div,
    mul_sum, mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro A _
  split_ifs <;> simp [pow_add, div_eq_mul_inv]; ring

/-- Exact factorization of the all-bad event conditional on the one shared secret. -/
theorem all_bad_probability {k : ℕ} (b : Fin k → Fin r → Fin m)
    (hb : Function.Injective (fun p : (Σ _ : Fin k, Fin r) ↦ b p.1 p.2)) :
    Attack.lweProb m n q 3 (fun s e A ↦ ∀ i, Bad (plant (e ∘ b i) s) (fun j ↦ A (b i j))) =
      expect (cbdWeight 3) (fun s : Fin n → Digit 3 ↦ (miss r q s)^k) := by
  rw [lwe_expect]
  congr 1
  funext s
  have hp := block_product b hb _ (rowWeight_sum n q 3)
    (fun _ z ↦ if localBad s z then (1:ℚ) else 0)
  simp only [prod_const, card_univ, Fintype.card_fin] at hp
  refine Eq.trans ?_ hp
  congr 1
  funext z
  rw [prod_boole]
  apply MultiBlock.ite_inst
  simp [localBad, Function.comp_def]

/-- Any exact oracle and any disjoint split. Reuse the existing first-passing selection,
support filter and reserved-row law for its four (possibly dependent) false-accept events. -/
theorem success_lower {k v : ℕ} (b : Fin k → Fin r → Fin m) (c : Fin v → Fin m)
    (hb : Function.Injective (Sum.elim (fun p : (Σ _ : Fin k, Fin r) ↦ b p.1 p.2) c))
    (O : ∀ d, CVPOracle d n q) (hq : 6 < q) :
    1 - expect (cbdWeight 3) (fun s : Fin n → Digit 3 ↦ (miss r q s)^k) -
      k*(7/q : ℚ)^v ≤ Attack.lweProb m n q 3 (fun s e A ↦
        Attack.attack 3 (asBlockOracle O) (fun _ ↦ r) b c A (Attack.lweSample A s e) =
          some (centered ∘ s)) := by
  classical
  let T := asBlockOracle O
  let allBad := fun s e (A : Design m n q) ↦ ∀ i, Bad (plant (e ∘ b i) s) (fun j ↦ A (b i j))
  have fail := Attack.lweProb_union m n q 3
    (fun s e A ↦ Attack.attack 3 T (fun _ ↦ r) b c A (Attack.lweSample A s e) ≠ some (centered ∘ s))
    allBad (fun i ↦ Attack.falseAccept 3 T (b i) c) (by
      intro s e A hf
      by_cases ha : allBad s e A
      · exact Or.inl ha
      right
      unfold allBad at ha
      push Not at ha
      obtain ⟨i,hi⟩ := ha
      have hc := candidate_of_good O hq (b i) s e A hi
      have hp := Attack.passes_secret (le_refl 3) A s e c
      have hh : Attack.attack 3 T (fun _ ↦ r) b c A (Attack.lweSample A s e) ≠ none := by
        rw [Attack.attack, Ne, List.findSome?_eq_none_iff]
        intro hn
        have h := hn i (List.mem_finRange i)
        change Attack.candidate 3 T _ _ _ = _ at hc
        rw [hc] at h
        simp [hp, Function.comp_def] at h
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hh
      have hd' := hd
      unfold Attack.attack at hd'
      obtain ⟨i', -, hi'⟩ := List.exists_of_findSome?_eq_some hd'
      rw [Option.filter_eq_some_iff] at hi'
      exact ⟨i',d,hi'.1, fun he ↦ hf (hd.trans (congrArg some he)), of_decide_eq_true hi'.2⟩)
  have hV (i : Fin k) := Attack.falseAccept_le hq (le_refl 3) T (b i) c
    (fun a j he ↦ Sum.inl_ne_inr (hb (a₁ := .inl ⟨i,a⟩) (a₂ := .inr j) he))
    (hb.comp Sum.inr_injective)
  have sumV := sum_le_sum (s := univ) (fun i _ ↦ hV i)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at sumV
  rw [Attack.lweProb_not, show Attack.lweProb m n q 3 allBad = _ from
    all_bad_probability b (hb.comp Sum.inl_injective)] at fail
  change _ ≤ Attack.lweProb m n q 3 (fun s e A ↦
    Attack.attack 3 T (fun _ ↦ r) b c A (Attack.lweSample A s e) = some (centered ∘ s))
  linarith

end SigabaNeo.Wall1.Width638
#print axioms SigabaNeo.Wall1.Width638.success_lower
#print axioms SigabaNeo.Wall1.Width638.lift_discarded
