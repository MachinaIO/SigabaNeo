module

public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionCBD
public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockProduct
import all SigabaNeo.Lib.Lattices.Planted.Probability
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionCBD
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Multi-block conditional independence for primal sample deletion (PROOF_GAP Parts 131/132)

Part 39 (`SampleDeletion.failure`) is the exact probability that the projected plant is not the
unique shortest pair, over iid CBD(η) `(e', s)` and a uniform design `A' ∈ (ZMod q)^{r×n}`.

* `condFailure r n q η s` is the same probability conditional on the secret `s`.
* `failure_eq_expect`: `failure = E_s[condFailure s]`.
* `condFailure_le`: the conditional form of `cbd_bound`, with a bound depending only on `‖s‖²`.
* `multiblock_exact`: for predetermined disjoint row blocks of a plain LWE sample, the probability
  that every block fails is exactly `E_s[∏ᵢ condFailure (r i) s]`.
* `multiblock_le`: hence it is at most `E_s[∏ᵢ condBound (r i) ‖s‖²]`.
* `expect_energy`: an `E_s` of a function of `‖s‖²` is a finite sum against `shell`. -/

public section
namespace SigabaNeo.Wall1.MultiBlock
open SigabaNeo.Planted SigabaNeo.SampleDeletion

/-! ## Laws -/

/-- One CBD(η) coordinate, normalized. -/
@[expose] def cbdWeight (η : ℕ) (a : Digit η) : ℚ := (mass a : ℚ) / (4^η : ℕ)

/-- One LWE row: a CBD(η) error digit and a uniform row of the design. -/
abbrev Row (n q η : ℕ) := Digit η × (Fin n → ZMod q)

@[expose] def rowWeight (n q η : ℕ) (y : Row n q η) : ℚ := cbdWeight η y.1 / (q : ℚ)^n

private theorem mass_sum (η : ℕ) : ∑ a : Digit η, mass a = 4^η := by
  rw [show (∑ a : Digit η, mass a) = _ from Fin.sum_univ_eq_sum_range _ _,
    Nat.sum_range_choose, pow_mul]
  rfl

theorem cbdWeight_sum (η : ℕ) : ∑ a, cbdWeight η a = 1 := by
  simp only [cbdWeight, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (by positivity)]
  exact_mod_cast mass_sum η

theorem rowWeight_sum (n q η : ℕ) [Fact q.Prime] : ∑ y, rowWeight n q η y = 1 := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  simp only [rowWeight, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
  have h (x : Digit η) : ((q^n : ℕ) : ℚ) * (cbdWeight η x / (q : ℚ)^n) = cbdWeight η x := by
    push_cast; field_simp
  simp only [h, cbdWeight_sum]

theorem cbdWeight_nonneg (η : ℕ) (a : Digit η) : 0 ≤ cbdWeight η a := by
  unfold cbdWeight; positivity

/-! ## Conditional failure -/

private theorem ite_inst {p q : Prop} (i : Decidable p) (j : Decidable q) (h : p ↔ q)
    (a b : ℚ) : @ite _ p i a b = @ite _ q j a b := by
  obtain rfl := propext h
  congr

/-- The block with rows `z` (error digit and design row each) fails for the secret `s`: the
projected plant is not the unique shortest pair (ties count as failure). -/
@[expose] def blockBad {r n q η : ℕ} [Fact q.Prime] (s : Fin n → Digit η)
    (z : Fin r → Row n q η) : Prop :=
  (fun i ↦ (z i).2) ∈ badMatrices q (fun i ↦ centered (z i).1) (fun j ↦ centered (s j))
    (Real.sqrt (normSq (plantedPoint (fun i ↦ centered (z i).1) (fun j ↦ centered (s j)))))

noncomputable instance {r n q η : ℕ} [Fact q.Prime] (s : Fin n → Digit η) :
    DecidablePred (blockBad (r := r) (q := q) s) := fun _ ↦ Classical.dec _

/-- Part 39's failure probability conditional on the secret `s`: the average over the `r` iid rows
(CBD error, uniform design row) only. -/
noncomputable def condFailure (r n q η : ℕ) [Fact q.Prime] (s : Fin n → Digit η) : ℚ :=
  expect (rowWeight n q η) (fun z : Fin r → Row n q η ↦ if blockBad s z then 1 else 0)

theorem condFailure_nonneg (r n q η : ℕ) [Fact q.Prime] (s : Fin n → Digit η) :
    0 ≤ condFailure r n q η s := by
  unfold condFailure expect
  refine Finset.sum_nonneg fun z _ ↦ mul_nonneg
    (Finset.prod_nonneg fun i _ ↦ div_nonneg (cbdWeight_nonneg _ _) (by positivity)) ?_
  dsimp only
  split_ifs <;> norm_num

private theorem integrate_eq {η : ℕ} (d : ℕ) (f : (Fin d → Digit η) → ℕ) :
    integrate d f = ∑ x, (∏ i, mass (x i)) * f x := by
  induction d with
  | zero => simp [integrate]; exact congrArg f (Subsingleton.elim _ _)
  | succ d ih =>
    rw [integrate, ← (Fin.consEquiv fun _ => Digit η).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_assoc]

private theorem badCount_append {r n q η : ℕ} [Fact q.Prime] (e : Fin r → Digit η)
    (s : Fin n → Digit η) :
    badCount r n q η (Fin.append e s) =
      (badMatrices q (fun i ↦ centered (e i)) (fun j ↦ centered (s j))
        (Real.sqrt (normSq (plantedPoint (fun i ↦ centered (e i))
          (fun j ↦ centered (s j)))))).card := by
  have h1 : retained (Fin.append e s) = fun i ↦ centered (e i) :=
    funext fun i ↦ by simp [retained]
  have h2 : secret (Fin.append e s) = fun j ↦ centered (s j) :=
    funext fun j ↦ by simp [secret]
  rw [badCount, h1, h2]

/-- Expectation of a function of the rows, in terms of the error digits and the design. -/
private theorem expect_rows {r n q η : ℕ} [Fact q.Prime]
    (F : (Fin r → Digit η) → Matrix (Fin r) (Fin n) (ZMod q) → ℚ) :
    expect (rowWeight n q η) (fun z : Fin r → Row n q η ↦ F (fun i ↦ (z i).1) (Matrix.of fun i ↦ (z i).2)) =
      (∑ e : Fin r → Digit η, ∑ A : Matrix (Fin r) (Fin n) (ZMod q),
        (∏ i, (mass (e i) : ℚ)) * F e A) / (((4^η : ℕ) : ℚ)^r * (q : ℚ)^(n*r)) := by
  unfold expect
  rw [← (Equiv.arrowProdEquivProdArrow (Fin r) (fun _ ↦ Digit η)
    (fun _ ↦ Fin n → ZMod q)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply, rowWeight, cbdWeight,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm n r]
  field_simp
  rfl

theorem condFailure_eq_integrate (r n q η : ℕ) [Fact q.Prime] (s : Fin n → Digit η) :
    condFailure r n q η s =
      (integrate r (fun e ↦ badCount r n q η (Fin.append e s)) : ℚ) /
        (((4^η : ℕ) : ℚ)^r * (q : ℚ)^(n*r)) := by
  unfold condFailure
  classical
  let F : (Fin r → Digit η) → Matrix (Fin r) (Fin n) (ZMod q) → ℚ := fun e A ↦
    if A ∈ badMatrices q (fun i ↦ centered (e i)) (fun j ↦ centered (s j))
      (Real.sqrt (normSq (plantedPoint (fun i ↦ centered (e i)) (fun j ↦ centered (s j)))))
    then 1 else 0
  have h1 : (fun z : Fin r → Row n q η ↦ if blockBad s z then (1 : ℚ) else 0) =
      fun z ↦ F (fun i ↦ (z i).1) (Matrix.of fun i ↦ (z i).2) :=
    funext fun z ↦ ite_inst _ _ Iff.rfl _ _
  rw [h1, expect_rows]
  congr 1
  rw [integrate_eq]
  push_cast
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [← Finset.mul_sum, badCount_append]
  congr 1
  simp only [F, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Part 39's failure probability is the secret-average of the conditional failure. -/
theorem failure_eq_expect (r n q η : ℕ) [Fact q.Prime] :
    SampleDeletion.failure r n q η = expect (cbdWeight η) (condFailure r n q η) := by
  unfold SampleDeletion.failure expect
  simp_rw [condFailure_eq_integrate, integrate_eq]
  rw [← (Fin.appendEquiv r n).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [show (Fin.appendEquiv r n) (e, s) = Fin.append e s from rfl]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    cbdWeight, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_add]
  field_simp
  push_cast
  ring

/-! ## Conditional form of `cbd_bound` -/

/-- Conditional analogue of `gain`: secret energy `E`, retained rows `r`, energy cutoff `J`. -/
@[expose] def condGain (η r n q J E : ℕ) : ℕ := ∑ j ∈ Finset.range (J - E),
  shell η r j * (2*q^r - (ballCount (r+n+1) (j+E+1) - 1))

/-- The bound on the conditional failure for a secret of squared norm `E`. -/
@[expose] def condBound (r n q η J E : ℕ) : ℚ :=
  ((2*q^r*(4^η)^r - condGain η r n q J E : ℕ) : ℚ) / (2*q^r*(4^η)^r : ℕ)

theorem condBound_nonneg (r n q η J E : ℕ) : 0 ≤ condBound r n q η J E := by
  unfold condBound; positivity

private theorem energy_eq_normSq {n η : ℕ} (s : Fin n → Digit η) :
    ∑ j, energy (s j) = normSq (fun j ↦ centered (s j)) := rfl

/-- Conditional `cbd_bound`: given the secret `s`, the failure probability over the `r` rows is at
most `condBound`, which depends on `s` only through `‖s‖² = Σ centered(s j)²`. -/
theorem condFailure_le (r n q η J : ℕ) [Fact q.Prime] (hq : J*(1+η^2) < q^2)
    (s : Fin n → Digit η) :
    condFailure r n q η s ≤ condBound r n q η J (normSq (fun j ↦ centered (s j))) := by
  classical
  rw [condFailure_eq_integrate, condBound, ← energy_eq_normSq]
  let E := ∑ j, energy (s j)
  let d := r+n
  let H := 2*q^r
  let L := q^(n*r)
  let T := (4^η)^r
  let g (k : ℕ) := H - (ballCount (d+1) (k+1)-1)
  let bonus (x : Fin r → Digit η) := ∑ j ∈ Finset.range (J - E),
    (if (∑ i, energy (x i)) = j then 1 else 0) * g (j+E)
  have bg : integrate r bonus = condGain η r n q J E := by
    unfold bonus condGain
    rw [integrate_sum]
    simp_rw [integrate_mul, shell_law]
    rfl
  have pointwise (x : Fin r → Digit η) :
      badCount r n q η (Fin.append x s) * H + bonus x * L ≤ H*L := by
    let k := ∑ i, energy (Fin.append x s i)
    have hk : k = (∑ i, energy (x i)) + E := by
      simp [k, E, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have cap : badCount r n q η (Fin.append x s) ≤ L := by
      unfold badCount
      refine (Finset.card_le_univ _).trans ?_
      change Fintype.card (Fin r → Fin n → ZMod q) ≤ _
      simp [L, ← pow_mul]
    have base := Nat.mul_le_mul_right H cap
    by_cases hj : (∑ i, energy (x i)) < J - E
    · have hkJ : k < J := by omega
      have hq' : (k+1)*(1+η^2) < q^2 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hkJ) hq
      have h := design_bound (q := q) (retained (Fin.append x s)) (secret (Fin.append x s)) η
        (k+1) (fun _ ↦ support_bound _) (fun _ ↦ support_bound _) hq'
      have hh : badCount r n q η (Fin.append x s) * H ≤ (ballCount (d+1) (k+1)-1)*L := by
        simpa [badCount, plant_energy, H, k, L, d, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using h
      have hb : bonus x = g k := by
        simp only [bonus]
        rw [Finset.sum_eq_single (∑ i, energy (x i))]
        · simp [hk]
        · intro j _ hne; simp [Ne.symm hne]
        · intro hn; exact absurd (Finset.mem_range.mpr hj) hn
      rw [hb]
      unfold g
      by_cases hc : ballCount (d+1) (k+1)-1 ≤ H
      · have he := congrArg (· * L) (Nat.sub_add_cancel hc)
        simp only [Nat.add_mul] at he
        omega
      · simp [Nat.sub_eq_zero_of_le (by omega : H ≤ ballCount (d+1) (k+1)-1)]
        simpa [Nat.mul_comm] using base
    · have hb : bonus x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : (∑ i, energy (x i)) ≠ i := by have := Finset.mem_range.mp hi; omega
        simp [hne]
      simpa [hb, Nat.mul_comm] using base
  have total := integrate_mono r _ _ pointwise
  rw [integrate_add, integrate_mul, integrate_mul, bg, integrate_const] at total
  have hL : 0 < L := pow_pos (Fact.out : Nat.Prime q).pos _
  have hH : 0 < H := Nat.mul_pos (by decide) (pow_pos (Fact.out : Nat.Prime q).pos _)
  have hT : 0 < T := pow_pos (pow_pos (by decide) _) _
  change integrate r _ * H + condGain η r n q J E * L ≤ T * (H*L) at total
  have hg : condGain η r n q J E ≤ H*T := by
    apply Nat.le_of_mul_le_mul_right _ hL
    nlinarith only [total, Nat.zero_le (integrate r (fun x ↦ badCount r n q η (Fin.append x s)) * H)]
  have bound : integrate r (fun x ↦ badCount r n q η (Fin.append x s)) * H ≤
      (H*T-condGain η r n q J E)*L := by
    rw [Nat.sub_mul]
    rw [show T*(H*L) = H*T*L by ring] at total
    omega
  change (integrate r _ : ℚ) / ((4^η : ℕ) ^ r * (q : ℚ)^(n*r)) ≤
    ((H*T-condGain η r n q J E : ℕ) : ℚ) / ((H*T : ℕ) : ℚ)
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos hT hL)
    (by exact_mod_cast Nat.mul_pos hH hT)).mpr
  have hb := Nat.mul_le_mul_right T bound
  exact_mod_cast (show integrate r _ * (H*T) ≤ (H*T-condGain η r n q J E)*(T*L) by
    simpa only [Nat.mul_assoc, Nat.mul_comm L T] using hb)

/-! ## Multiple disjoint row blocks -/

/-- Block `i` of a full sample `(e, A)` with `m` rows, restricted to the rows `b i`, fails. -/
@[expose] def sampleBlockBad {m n q η : ℕ} [Fact q.Prime] {r : ℕ} (b : Fin r → Fin m)
    (s : Fin n → Digit η) (e : Fin m → Digit η) (A : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  (fun a ↦ A (b a)) ∈ badMatrices q (fun a ↦ centered (e (b a))) (fun j ↦ centered (s j))
    (Real.sqrt (normSq (plantedPoint (fun a ↦ centered (e (b a))) (fun j ↦ centered (s j)))))

noncomputable instance {m n q η r : ℕ} [Fact q.Prime] (b : Fin r → Fin m) (s : Fin n → Digit η)
    (e : Fin m → Digit η) : DecidablePred (sampleBlockBad (q := q) b s e) :=
  fun _ ↦ Classical.dec _

/-- Plain LWE with `m` rows: iid CBD(η) secret `s` and errors `e`, uniform `A`, all independent.
For `k` predetermined row blocks `b i : Fin (r i) → Fin m`, pairwise disjoint and without
repetition, the exact probability that every block fails equals `E_s[∏ᵢ condFailure (r i) s]`. -/
theorem multiblock_exact (m n q η : ℕ) [Fact q.Prime] {K : Type*} [Fintype K] [DecidableEq K]
    (r : K → ℕ) (b : ∀ i, Fin (r i) → Fin m)
    (hb : Function.Injective (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2)) :
    ((∑ s : Fin n → Digit η, ∑ e : Fin m → Digit η, ∑ A : Matrix (Fin m) (Fin n) (ZMod q),
        if ∀ i, sampleBlockBad (b i) s e A then
          ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)) else 0) /
      (((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m)) : ℚ) =
      expect (cbdWeight η) (fun s ↦ ∏ i, condFailure (r i) n q η s) := by
  unfold condFailure
  simp_rw [← block_product b hb (rowWeight n q η) (rowWeight_sum n q η)]
  have key (s : Fin n → Digit η) :
      expect (rowWeight n q η) (fun x : Fin m → Row n q η ↦
        ∏ i, if blockBad s (fun a ↦ x (b i a)) then (1 : ℚ) else 0) =
      (∑ e : Fin m → Digit η, ∑ A : Matrix (Fin m) (Fin n) (ZMod q),
        (∏ j, (mass (e j) : ℚ)) * if ∀ i, sampleBlockBad (b i) s e A then (1 : ℚ) else 0) /
        (((4^η : ℕ) : ℚ)^m * (q : ℚ)^(n*m)) := by
    refine Eq.trans ?_ (expect_rows (r := m) (n := n) (q := q) (η := η)
      (fun e A ↦ if ∀ i, sampleBlockBad (b i) s e A then (1 : ℚ) else 0))
    congr 1
    funext x
    exact Finset.prod_boole.trans
      (ite_inst _ _ ⟨fun h i ↦ h i (Finset.mem_univ _), fun h i _ ↦ h i⟩ _ _)
  simp_rw [key]
  unfold expect
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [cbdWeight, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  split_ifs
  · rw [pow_add]
    field_simp
  · simp

/-- Hence the probability that every block fails is at most `E_s[∏ᵢ condBound (r i) ‖s‖²]`. -/
theorem multiblock_le (m n q η J : ℕ) [Fact q.Prime] (hq : J*(1+η^2) < q^2)
    {K : Type*} [Fintype K] [DecidableEq K]
    (r : K → ℕ) (b : ∀ i, Fin (r i) → Fin m)
    (hb : Function.Injective (fun p : (Σ i, Fin (r i)) ↦ b p.1 p.2)) :
    ((∑ s : Fin n → Digit η, ∑ e : Fin m → Digit η, ∑ A : Matrix (Fin m) (Fin n) (ZMod q),
        if ∀ i, sampleBlockBad (b i) s e A then
          ((∏ j, (mass (s j) : ℚ)) * ∏ j, (mass (e j) : ℚ)) else 0) /
      (((4^η : ℕ) : ℚ)^(m+n) * (q : ℚ)^(n*m)) : ℚ) ≤
      expect (cbdWeight η)
        (fun s : Fin n → Digit η ↦ ∏ i, condBound (r i) n q η J (normSq (fun j ↦ centered (s j)))) := by
  rw [multiblock_exact m n q η r b hb]
  unfold expect
  refine Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun j _ ↦ cbdWeight_nonneg _ _)
  exact Finset.prod_le_prod₀ (fun i _ ↦ condFailure_nonneg _ _ _ _ _)
    (fun i _ ↦ condFailure_le _ _ _ _ _ hq s)

/-- The secret average of a function of `‖s‖²` against the CBD energy distribution `shell`. -/
theorem expect_energy (n η : ℕ) (g : ℕ → ℚ) :
    expect (cbdWeight η) (fun s : Fin n → Digit η ↦ g (normSq (fun j ↦ centered (s j)))) =
      (∑ E ∈ Finset.range (n*η^2+1), (shell η n E : ℚ) * g E) / ((4^η : ℕ) : ℚ)^n := by
  classical
  have hlaw (E : ℕ) : (shell η n E : ℚ) =
      ∑ s : Fin n → Digit η, (∏ j, (mass (s j) : ℚ)) *
        if normSq (fun j ↦ centered (s j)) = E then 1 else 0 := by
    rw [← shell_law (η := η) n E, integrate_eq]
    push_cast
    rfl
  have hle (s : Fin n → Digit η) : normSq (fun j ↦ centered (s j)) < n*η^2+1 := by
    rw [← energy_eq_normSq, Nat.lt_succ_iff]
    calc ∑ j, energy (s j) ≤ ∑ _j : Fin n, η^2 :=
          Finset.sum_le_sum fun j _ ↦ Nat.pow_le_pow_left (support_bound _) 2
      _ = n*η^2 := by simp
  simp_rw [hlaw, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  unfold expect
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_eq_single (normSq (fun j ↦ centered (s j)))]
  · simp [cbdWeight, Finset.prod_div_distrib]
    ring
  · intro E _ hE; simp [Ne.symm hE]
  · intro h; exact absurd (Finset.mem_range.mpr (hle s)) h

end SigabaNeo.Wall1.MultiBlock

#print axioms SigabaNeo.Wall1.MultiBlock.failure_eq_expect
#print axioms SigabaNeo.Wall1.MultiBlock.condFailure_le
#print axioms SigabaNeo.Wall1.MultiBlock.multiblock_exact
#print axioms SigabaNeo.Wall1.MultiBlock.multiblock_le
#print axioms SigabaNeo.Wall1.MultiBlock.expect_energy
