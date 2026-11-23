module

public import SigabaNeo.Lib.Lattices.Research.Wall1.Width638Certificate
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Certificate
import all SigabaNeo.Lib.Lattices.Research.Wall1.Width638Graph
import all SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
import Mathlib.Tactic

/-! Randomized closest-point solvers. For each seed, patch the solver's wrong answers with
a fixed exact oracle. The patched map is an exact oracle, so `recovery_std` applies seedwise.
The raw and patched runs agree unless one of the four queries is answered wrongly. -/

public section
noncomputable section
namespace SigabaNeo.Wall1.Width638
open MultiBlock QaryMembership SigabaNeo.SampleDeletion Matrix Finset
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

abbrev Solver := Design 127 511 3329 → (Fin 127 → ℤ) → Grid 127 511

/-- `firstValidated` with an arbitrary map in place of an exact oracle. -/
def firstValidatedBy (f : Solver) (b : Fin 4 → Fin 127 → Fin 512) (c : Fin 4 → Fin 512)
    (A : Sample) (y : Observation) : Option Secret :=
  (List.finRange 4).findSome? fun i ↦
    let g := f (fun j ↦ A (b i j)) (fun j ↦ ((y (b i j)).val : ℤ))
    (Attack.decode 3 3329 (fun j ↦ g (.inr j))).filter (fun d ↦ decide
      (∀ j, (((y (c j)).val : ℤ) - lift A y d (c j)).natAbs ≤ 3))

theorem firstValidated_eq (O : Oracle) (b c A y) :
    firstValidated O b c A y = firstValidatedBy O.closest b c A y := by
  unfold firstValidated firstValidatedBy
  rfl

/-- The solver's answer is a closest graph point. -/
def Correct (f : Solver) (A : Design 127 511 3329) (t : Fin 127 → ℤ) : Prop :=
  f A t ∈ graph A ∧ ∀ w ∈ graph A, normSq (f A t - target t) ≤ normSq (w - target t)

/-- Keep correct answers and replace wrong ones by a fixed exact oracle. -/
def patch (O₀ : Oracle) (f : Solver) : Oracle where
  closest A t := if Correct f A t then f A t else O₀.closest A t
  mem A t := by
    by_cases h : Correct f A t
    · simpa [h] using h.1
    · simpa [h] using O₀.mem A t
  minimal A t w hw := by
    by_cases h : Correct f A t
    · simpa [h] using h.2 w hw
    · simpa [h] using O₀.minimal A t w hw

/-- The four queries made on a public sample. -/
def query (b : Fin 4 → Fin 127 → Fin 512) (A : Sample) (y : Observation) (i : Fin 4) :
    Design 127 511 3329 × (Fin 127 → ℤ) :=
  ((fun j ↦ A (b i j)), (fun j ↦ ((y (b i j)).val : ℤ)))

theorem agree (O₀ : Oracle) (f : Solver) (b c) (A : Sample) (y : Observation)
    (h : ∀ i, Correct f (query b A y i).1 (query b A y i).2) :
    firstValidatedBy f b c A y = firstValidated (patch O₀ f) b c A y := by
  rw [firstValidated_eq]
  unfold firstValidatedBy
  apply congrArg (fun g : Fin 4 → Option Secret ↦ (List.finRange 4).findSome? g)
  funext i
  have hi : Correct f (fun j ↦ A (b i j)) (fun j ↦ ((y (b i j)).val : ℤ)) := h i
  have hc : (patch O₀ f).closest (fun j ↦ A (b i j)) (fun j ↦ ((y (b i j)).val : ℤ)) =
      f (fun j ↦ A (b i j)) (fun j ↦ ((y (b i j)).val : ℤ)) := if_pos hi
  simp only [hc]

/-- Seed averages of event probabilities are bounded by a pointwise seed bound. -/
theorem seed_average_le {m n q η : ℕ} [Fact q.Prime] {Ω : Type} [Fintype Ω]
    (w : Ω → ℚ) (hw : ∀ ω, 0 ≤ w ω)
    (P : Ω → (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop)
    (δ : ℚ) (h : ∀ s e A, ∑ ω, w ω * (if P ω s e A then 1 else 0) ≤ δ) :
    ∑ ω, w ω * Attack.lweProb m n q η (P ω) ≤ δ := by
  have tot : Attack.lweProb m n q η (fun _ _ _ ↦ True) = 1 := by
    have h0 : Attack.lweProb m n q η (fun _ _ _ ↦ False) = 0 := by
      simp [Attack.lweProb]
    have := Attack.lweProb_not m n q η (fun _ _ _ ↦ False)
    simpa [h0] using this
  generalize hN : (((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m)) = N
  let wt (s : Fin n → Digit η) (e : Fin m → Digit η) : ℚ :=
    (∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)
  have hm (s e) : 0 ≤ wt s e := by positivity
  have expand (Q : (Fin n → Digit η) → (Fin m → Digit η) → Matrix (Fin m) (Fin n) (ZMod q) → Prop) :
      Attack.lweProb m n q η Q =
        (∑ s, ∑ e, ∑ A, wt s e * (if Q s e A then 1 else 0)) / N := by
    rw [← hN]
    unfold Attack.lweProb
    congr 1
    refine sum_congr rfl fun s _ ↦ sum_congr rfl fun e _ ↦ sum_congr rfl fun A _ ↦ ?_
    split_ifs <;> simp [wt]
  have hNn : 0 ≤ N := by rw [← hN]; positivity
  have lhs : ∑ ω, w ω * Attack.lweProb m n q η (P ω) =
      (∑ s, ∑ e, ∑ A, wt s e * ∑ ω, w ω * (if P ω s e A then 1 else 0)) / N := by
    simp_rw [expand, mul_div_assoc', ← sum_div]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [sum_comm]
    exact sum_congr rfl fun A _ ↦ sum_congr rfl fun ω _ ↦ by ring
  have rhs : δ * Attack.lweProb m n q η (fun _ _ _ ↦ True) =
      (∑ s, ∑ e, ∑ A : Matrix (Fin m) (Fin n) (ZMod q), wt s e * δ) / N := by
    rw [expand, mul_div_assoc']
    congr 1
    simp only [if_true, mul_one, mul_sum]
    exact sum_congr rfl fun s _ ↦ sum_congr rfl fun e _ ↦ sum_congr rfl fun A _ ↦ mul_comm _ _
  rw [lhs]
  calc (∑ s, ∑ e, ∑ A, wt s e * ∑ ω, w ω * (if P ω s e A then 1 else 0)) / N
      ≤ (∑ s, ∑ e, ∑ A : Matrix (Fin m) (Fin n) (ZMod q), wt s e * δ) / N := by
        apply div_le_div_of_nonneg_right _ hNn
        exact sum_le_sum fun s _ ↦ sum_le_sum fun e _ ↦ sum_le_sum fun A _ ↦
          mul_le_mul_of_nonneg_left (h s e A) (hm s e)
    _ = δ := by rw [← rhs, tot, mul_one]

/-- Randomized solvers with per-query error at most `δ` (uniformly over inputs) keep
the width-638 recovery bound up to `4δ`. The seed law `w` is independent of the sample. -/
theorem recovery_randomized {Ω : Type} [Fintype Ω] (w : Ω → ℚ) (hw : ∀ ω, 0 ≤ w ω)
    (hsum : ∑ ω, w ω = 1) (S : Ω → Solver) (δ : ℚ)
    (herr : ∀ A t, ∑ ω, w ω * (if Correct (S ω) A t then 0 else 1) ≤ δ) :
    (643162094166 / 10^12 : ℚ) - 4*δ < ∑ ω, w ω * Attack.lweProb 512 511 3329 3 (fun s e A ↦
      firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
        some (centered ∘ s)) := by
  obtain ⟨O₀⟩ := graphOracle_nonempty (r := 127) (n := 511) (q := 3329)
  let Bad (ω : Ω) (i : Fin 4) (s : Fin 511 → Digit 3) (e : Fin 512 → Digit 3) (A : Sample) :=
    ¬ Correct (S ω) (query blockRow A (Attack.lweSample A s e) i).1
      (query blockRow A (Attack.lweSample A s e) i).2
  have seedwise (ω : Ω) :
      Attack.lweProb 512 511 3329 3 (fun s e A ↦
          firstValidated (patch O₀ (S ω)) blockRow reservedRow A (Attack.lweSample A s e) =
            some (centered ∘ s)) ≤
        Attack.lweProb 512 511 3329 3 (fun s e A ↦
          firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
            some (centered ∘ s)) + ∑ i, Attack.lweProb 512 511 3329 3 (Bad ω i) := by
    apply Attack.lweProb_union
    intro s e A hp
    by_cases hall : ∀ i, ¬ Bad ω i s e A
    · left
      rw [agree O₀ (S ω) blockRow reservedRow A _ (fun i ↦ by simpa [Bad] using hall i)]
      exact hp
    · right
      push_neg at hall
      exact hall
  have errs (i : Fin 4) : ∑ ω, w ω * Attack.lweProb 512 511 3329 3 (Bad ω i) ≤ δ :=
    seed_average_le w hw (fun ω ↦ Bad ω i) δ fun s e A ↦ by
      have := herr (query blockRow A (Attack.lweSample A s e) i).1
        (query blockRow A (Attack.lweSample A s e) i).2
      simpa [Bad, ite_not] using this
  have base (ω : Ω) := recovery_std (patch O₀ (S ω))
  have lower : ∑ ω, w ω * (643162094166 / 10^12 : ℚ) <
      ∑ ω, w ω * (Attack.lweProb 512 511 3329 3 (fun s e A ↦
          firstValidatedBy (S ω) blockRow reservedRow A (Attack.lweSample A s e) =
            some (centered ∘ s)) + ∑ i, Attack.lweProb 512 511 3329 3 (Bad ω i)) := by
    have hpos : ∃ ω, 0 < w ω := by
      by_contra hc
      push_neg at hc
      have : ∑ ω, w ω ≤ 0 := sum_nonpos fun ω _ ↦ hc ω
      linarith
    obtain ⟨ω₀, hω₀⟩ := hpos
    apply sum_lt_sum
    · intro ω _
      exact mul_le_mul_of_nonneg_left ((base ω).le.trans (seedwise ω)) (hw ω)
    · exact ⟨ω₀, mem_univ _, mul_lt_mul_of_pos_left ((base ω₀).trans_le (seedwise ω₀)) hω₀⟩
  rw [← sum_mul, hsum, one_mul] at lower
  simp only [mul_add, sum_add_distrib, mul_sum] at lower
  rw [sum_comm] at lower
  have hE : ∑ i : Fin 4, ∑ ω, w ω * Attack.lweProb 512 511 3329 3 (Bad ω i) ≤ 4*δ := by
    have := sum_le_sum (s := (univ : Finset (Fin 4))) fun i _ ↦ errs i
    simpa using this
  linarith

end SigabaNeo.Wall1.Width638

#print axioms SigabaNeo.Wall1.Width638.seed_average_le
#print axioms SigabaNeo.Wall1.Width638.recovery_randomized
