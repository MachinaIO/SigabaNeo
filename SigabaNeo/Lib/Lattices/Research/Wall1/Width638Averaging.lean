module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Groups
public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Arithmetic
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Groups
import all SigabaNeo.Lib.Lattices.Research.Wall1.QaryMembership
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlock
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

public section
noncomputable section
namespace SigabaNeo.Wall1.Width638
open SigabaNeo.SampleDeletion MultiBlock QaryMembership Finset
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩
set_option maxRecDepth 8000
set_option exponentiation.threshold 1024
attribute [local irreducible] ballCount shell H D credit gap gain denominator

private def designMiss {r n : ℕ} (q : ℕ) [Fact q.Prime] (p : Grid r n) : ℚ :=
  ((designs (q := q) (Bad p)).card : ℚ) / Fintype.card (Design r n q)

private theorem miss_split {r n q : ℕ} [Fact q.Prime] (s : Fin n → Digit 3) :
    miss r q s = MultiBlock.expect (cbdWeight 3) (fun e : Fin r → Digit 3 ↦
      designMiss q (plant e s)) := by
  have eqn := MultiBlock.expect_rows (r := r) (q := q) (n := n)
    (fun e A ↦ if Bad (plant e s) A then (1:ℚ) else 0)
  change MultiBlock.expect _ _ = _
  refine eqn.trans ?_
  rw [MultiBlock.expect, sum_div]
  apply sum_congr rfl
  intro e _
  simp only [← mul_sum, sum_boole, designMiss, designs, cbdWeight, prod_div_distrib,
    prod_const, card_univ, Fintype.card_fin, Attack.card_matrix]
  ring

def energyOf {n : ℕ} (s : Fin n → Digit 3) := normSq (centered ∘ s)

private def bonus (t j : ℕ) : ℚ := if j < 955-t then (gap (t+j) : ℚ)/H else 0

private theorem design_bound (s : Fin 511 → Digit 3) (e : Fin 127 → Digit 3) :
    designMiss 3329 (plant e s) + bonus (energyOf s) (energyOf e) ≤ 1 := by
  let p := plant e s
  let T := Fintype.card (Design 127 511 3329)
  let B := (designs (q := 3329) (Bad p)).card
  have cap : B ≤ T := card_le_univ _
  have posT : (0:ℚ) < T := by exact_mod_cast Fintype.card_pos
  have posH : (0:ℚ) < H := by unfold H; positivity
  have en : normSq p = energyOf s + energyOf e := by
    simp [normSq, p, plant, energyOf, Fintype.sum_sum_type, add_comm, Function.comp_def]
  change (B:ℚ)/T + _ ≤ _
  unfold bonus
  split_ifs with ht
  · have he : normSq p ≤ 954 := by omega
    have hu : B * H ≤ (ballCount 638 (normSq p)-1)*T := by
      unfold H
      exact translated_ball (q := 3329) p (by omega)
    set b := ballCount 638 (normSq p) - 1
    rw [← en, gap]
    change (B:ℚ)/T + ((H-b:ℕ):ℚ)/H ≤ 1
    by_cases hb : H ≤ b
    · rw [Nat.sub_eq_zero_of_le hb, Nat.cast_zero, zero_div, add_zero, div_le_one posT]
      exact_mod_cast cap
    · have hc := (Nat.cast_le (α := ℚ)).mpr hu
      push_cast at hc
      rw [Nat.cast_sub (by omega)]
      field_simp
      linarith
  · rw [add_zero, div_le_one posT]
    exact_mod_cast cap

private theorem range_cut {N M : ℕ} (h : M ≤ N) (f : ℕ → ℚ) :
    (∑ i ∈ range N, if i < M then f i else 0) = ∑ i ∈ range M, f i := by
  rw [← sum_filter]
  congr 1
  ext i
  simp
  omega

private theorem expect_bonus (t : ℕ) :
    MultiBlock.expect (cbdWeight 3) (fun e : Fin 127 → Digit 3 ↦ bonus t (energyOf e)) =
      (credit t : ℚ)/D := by
  rw [show (fun e : Fin 127 → Digit 3 ↦ bonus t (energyOf e)) =
    (fun e ↦ bonus t (normSq (fun j ↦ centered (e j)))) from rfl, expect_energy]
  simp only [bonus, mul_ite, mul_zero]
  rw [range_cut (by omega : 955-t ≤ 127*3^2+1), credit, Nat.cast_sum]
  unfold D
  push_cast
  simp only [← mul_div_assoc, ← sum_div]
  ring

private theorem total_weight (d : ℕ) :
    ∑ e : Fin d → Digit 3, ∏ i, cbdWeight 3 (e i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin d) a ↦ cbdWeight 3 a), cbdWeight_sum]
  simp

/-- Conditional on the entire secret. The bound uses its energy only after integrating
the independent group errors and the uniform group design. -/
theorem conditional_bound (s : Fin 511 → Digit 3) :
    miss 127 3329 s + (credit (energyOf s) : ℚ)/D ≤ 1 := by
  rw [miss_split, ← expect_bonus, MultiBlock.expect, MultiBlock.expect, ← sum_add_distrib,
    ← total_weight 127]
  apply sum_le_sum
  intro e _
  rw [← mul_add]
  exact mul_le_of_le_one_right (prod_nonneg fun j _ ↦ cbdWeight_nonneg _ _) (design_bound s e)

private theorem miss_nonneg (s : Fin 511 → Digit 3) : 0 ≤ miss 127 3329 s := by
  rw [miss_split, MultiBlock.expect]
  exact sum_nonneg fun e _ ↦ mul_nonneg (prod_nonneg fun j _ ↦ cbdWeight_nonneg _ _)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Probability credit for at least one good block, with four disjoint groups. -/
theorem average_bound :
    (gain : ℚ)/denominator ≤ 1 - MultiBlock.expect (cbdWeight 3)
      (fun s : Fin 511 → Digit 3 ↦ (miss 127 3329 s)^4) := by
  let part (t : ℕ) : ℚ := ((D^4 - (D-credit t)^4 : ℕ) : ℚ)/(D : ℚ)^4
  have posD : 0 < (D : ℚ) := by unfold D H; positivity
  have single (s : Fin 511 → Digit 3) : part (energyOf s) ≤ 1 - (miss 127 3329 s)^4 := by
    have h := conditional_bound s
    have hn := miss_nonneg s
    have hc : (credit (energyOf s) : ℚ) ≤ D := (div_le_one posD).mp (by linarith)
    have hc' : credit (energyOf s) ≤ D := by exact_mod_cast hc
    have hh : miss 127 3329 s ≤ (D - (credit (energyOf s) : ℚ))/D := by
      rw [sub_div, div_self posD.ne']; linarith
    have h4 := pow_le_pow_left₀ hn hh 4
    unfold part
    rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.sub_le ..) 4), Nat.cast_pow, Nat.cast_pow,
      Nat.cast_sub hc', sub_div, div_self (pow_ne_zero _ posD.ne'), ← div_pow]
    linarith
  have partMean : MultiBlock.expect (cbdWeight 3) (fun s : Fin 511 → Digit 3 ↦ part (energyOf s)) =
      (gain : ℚ)/denominator := by
    change MultiBlock.expect _ (fun s : Fin 511 → Digit 3 ↦ part (normSq (fun j ↦ centered (s j)))) = _
    rw [expect_energy]
    have trunc (t : ℕ) : (shell 3 511 t : ℚ) * part t =
        if t < 955 then (shell 3 511 t : ℚ) * part t else 0 := by
      split_ifs with ht
      · rfl
      · simp [part, credit, Nat.sub_eq_zero_of_le (by omega : 955 ≤ t)]
    rw [sum_congr rfl (fun t (_ : t ∈ range (511*3^2+1)) ↦ trunc t)]
    rw [range_cut (by decide : 955 ≤ 511*3^2+1), gain_eq, Nat.cast_sum, denominator]
    simp only [part, Nat.cast_mul, Nat.cast_pow, ← mul_div_assoc, ← sum_div]
    push_cast
    ring
  rw [← partMean, MultiBlock.expect, MultiBlock.expect, ← total_weight 511, ← sum_sub_distrib]
  refine sum_le_sum fun s _ ↦ ?_
  simpa [mul_sub] using mul_le_mul_of_nonneg_left (single s)
    (prod_nonneg (s := univ) fun j _ ↦ cbdWeight_nonneg 3 (s j))

end SigabaNeo.Wall1.Width638
#print axioms SigabaNeo.Wall1.Width638.conditional_bound
#print axioms SigabaNeo.Wall1.Width638.average_bound
