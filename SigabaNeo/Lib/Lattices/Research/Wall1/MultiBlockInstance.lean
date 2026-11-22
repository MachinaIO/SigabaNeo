module

public import SigabaNeo.Lib.Lattices.Research.Wall1.MultiBlockAttack
public import SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionPacked
import all SigabaNeo.Lib.Lattices.Attacks.Primal.SampleDeletionPacked
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-! # The recorded two-block instance (PROOF_GAP Wall 1, Part 131)

Plain LWE (m, n, q) = (511, 512, 3329), CBD(3): two predetermined disjoint blocks of 133 rows
each (two exact SVP calls in dimension 133 + 512 + 1 = 646) and 245 reserved verification rows.
`two_block_success`: for every exact SVP oracle and every such row split, the end-to-end attack
of `MultiBlockAttack` outputs the secret with probability `> 99409/100000`.

The kernel evaluates `attack_success_condBound` at `J = 1081`, the largest cutoff for which the
truncated subtraction `2q^r − (ballCount 646 (k+1) − 1)` never truncates for `k < J` (checked:
`ballCount 646 1081 ≤ 2q^133 + 1`). All `condGain E` for `E < J` are digits of one packed
product: the reversed CBD(3)^133 energy polynomial times the packed truncation-free ball gaps. -/

public section
namespace SigabaNeo.Wall1.MultiBlock.Instance
open Polynomial SigabaNeo.SampleDeletion SigabaNeo.Wall1.MultiBlock
  SigabaNeo.Wall1.MultiBlock.Attack

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 10000000

instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-! ## Packed data -/

@[expose] def H := 2*3329^133
/-- The denominator of `condBound 133 512 3329 3 J E`. -/
@[expose] def Dn := 2*3329^133*(4^3)^133
/-- The reversed CBD(3) energy word `Σₐ mass a · b^(9 − energy a)`. -/
@[expose] def revWord (b : ℕ) :=
  sumTo (fun a ↦ (Nat.choose 6 a) * b ^ (9 - (Int.ofNat a - 3).natAbs^2)) 7
@[expose] def packedRev := Nat.powMod (revWord base) 133 (base^2279)
/-- Digit `k < 1081` is `2q^133 + 1 − ballCount 646 (k+1)`. -/
@[expose] def gWord := (H+1) * ((base^1081 - 1)/(base - 1)) - packedBall 646 / base % base^1081
/-- Digit `1197 + E` is `condGain 3 133 512 3329 1081 E` for `E < 1081`. -/
@[expose] def pWord := packedRev * gWord

/-- Digitwise fold of two packed words over `2^a` digits. -/
@[expose] def foldD (f : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, c, w => f (c % base) (w % base)
  | a+1, c, w =>
    let split := base^(2^a)
    foldD f a (c % split) (w % split) + foldD f a (c / split) (w / split)

/-- `Σ_{E<1081} shell 3 512 E · (Dn − condGain E)²`. -/
@[expose] def S1 :=
  foldD (fun a g ↦ a * (Dn - g)^2) 11 (packedCBD 512 % base^1081) (pWord / base^1197)
/-- `Σ_{E<1081} shell 3 512 E`. -/
@[expose] def S0 := foldD (fun a _ ↦ a) 11 (packedCBD 512 % base^1081) 0

/-! ## Kernel checks -/

theorem ball_check : packedBall 646 / base^1081 % base ≤ H + 1 := by decide +kernel

theorem final_check : 99409 * (Dn^2 * 64^512) * 3329^245 + 200000 * 7^245 * (Dn^2 * 64^512) +
    100000 * S1 * 3329^245 < 100000 * S0 * Dn^2 * 3329^245 := by decide +kernel

-- Keep the elaborator from unfolding the recursive counts in defeq checks (e.g. the `rfl`
-- attempted after each `rw`); the kernel checks above do not depend on this. The kernel itself
-- evaluates closed `Nat` arithmetic whenever two such terms differ syntactically, so the proofs
-- below are arranged so that closed terms only ever meet syntactically equal copies (e.g.
-- `gword_abstract` is instantiated with `ballCount 646`, not with a lambda).
attribute [local irreducible] ballCount shell condGain packedBall packedCBD base H Dn gWord pWord
  packedRev S0 S1

private theorem base_pos : 0 < base := by unfold base; positivity

set_option maxHeartbeats 400000

/-! ## Digits -/

private theorem foldD_sum (f : ℕ → ℕ → ℕ) (a c w : ℕ) :
    foldD f a c w = ∑ k ∈ Finset.range (2^a), f (digit c k) (digit w k) := by
  induction a generalizing c w with
  | zero => simp [foldD, digit]
  | succ a ih =>
    rw [foldD, pow_succ, Nat.mul_two, Finset.sum_range_add, ih, ih]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [digit_low _ _ _ (Finset.mem_range.mp hk)]
    · simp only [digit_high]

private theorem mod_digits (w : ℕ) : ∀ J, w % base^J = ∑ k ∈ Finset.range J, digit w k * base^k
  | 0 => by simp [Nat.mod_one]
  | J+1 => by
    rw [Finset.sum_range_succ, ← mod_digits w J, Nat.mod_pow_succ, digit, Nat.mul_comm]

private theorem digit_trunc (w J k : ℕ) (hk : J ≤ k) : digit (w % base^J) k = 0 := by
  have hlt : w % base^J < base^k :=
    (Nat.mod_lt _ (pow_pos base_pos _)).trans_le (Nat.pow_le_pow_right base_pos hk)
  simp [digit, Nat.div_eq_of_lt hlt]

/-! ## Ball counts -/

private theorem ballCount_pos : ∀ d j, 1 ≤ ballCount d j
  | 0, _ => by simp [ballCount]
  | d+1, j => by
    rw [ballCount]
    have h0 : (0 : ℤ) ∈ Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ) := by simp
    have := Finset.single_le_sum (f := fun a : ℤ ↦ ballCount d (j - a.natAbs^2))
      (fun _ _ ↦ Nat.zero_le _) h0
    exact (ballCount_pos d j).trans (by simpa using this)

private theorem ballCount_mono : ∀ d {j j' : ℕ}, j ≤ j' → ballCount d j ≤ ballCount d j'
  | 0, _, _, _ => by simp [ballCount]
  | d+1, j, j', h => by
    rw [ballCount, ballCount]
    refine (Finset.sum_le_sum fun a _ ↦ ballCount_mono d (Nat.sub_le_sub_right h _)).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      have := Nat.sqrt_le_sqrt h
      omega
    · intros; exact Nat.zero_le _

private theorem gword_abstract (b Hc J : ℕ) (B : ℕ → ℕ) (hB1 : ∀ k, 1 ≤ B k)
    (hBle : ∀ k ∈ Finset.range J, B (k+1) ≤ Hc + 1) :
    (Hc+1) * ∑ k ∈ Finset.range J, b^k - ∑ k ∈ Finset.range J, B (k+1) * b^k =
      ∑ k ∈ Finset.range J, (Hc - (B (k+1) - 1)) * b^k := by
  rw [Finset.mul_sum, ← Finset.sum_tsub_distrib _ (fun k hk ↦ Nat.mul_le_mul_right _ (hBle k hk))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Nat.sub_mul]
  have := hB1 (k+1)
  congr 1
  omega

private theorem gWord_eq :
    gWord = ∑ k ∈ Finset.range 1081, (H - (ballCount 646 (k+1) - 1)) * base^k := by
  have hcheck : ballCount 646 1081 ≤ H + 1 := by
    have h := ball_digit (d := 646) (k := 1081) (by norm_num) (by norm_num)
    rw [← h]
    exact ball_check
  have hb : packedBall 646 / base % base^1081 =
      ∑ k ∈ Finset.range 1081, ballCount 646 (k+1) * base^k := by
    rw [mod_digits]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [show packedBall 646 / base = packedBall 646 / base^1 by rw [pow_one], digit_high]
    unfold digit
    rw [ball_digit (d := 646) (k := 1+k) (by norm_num) (by omega), Nat.add_comm 1 k]
  have hones : (base^1081 - 1)/(base - 1) = ∑ k ∈ Finset.range 1081, base^k :=
    (Nat.geomSum_eq (by unfold base; norm_num) _).symm
  have e1 : gWord = (H+1) * ∑ k ∈ Finset.range 1081, base^k -
      ∑ k ∈ Finset.range 1081, ballCount 646 (k+1) * base^k := by
    rw [gWord, hb, hones]
  exact e1.trans (gword_abstract base H 1081 (ballCount 646) (ballCount_pos 646) fun k hk ↦
      (ballCount_mono 646 (by have := Finset.mem_range.mp hk; omega)).trans hcheck)

/-! ## The reversed energy polynomial -/

private noncomputable def rc : ℕ[X] := ∑ a : Digit 3, C (mass a) * X^(9 - energy a)

private theorem energy_le (a : Digit 3) : energy a ≤ 9 := by
  have h : (centered a).natAbs ≤ 3 := by
    have := a.isLt
    unfold centered
    omega
  exact (Nat.pow_le_pow_left h 2).trans (by norm_num)

private theorem cbd_natDegree : (cbd 3).natDegree ≤ 9 :=
  natDegree_sum_le_of_forall_le _ _ fun a _ ↦
    (natDegree_C_mul_X_pow_le _ _).trans (energy_le a)

private theorem reflect_cbd : reflect 9 (cbd 3) = rc := by
  unfold cbd rc
  induction (Finset.univ : Finset (Digit 3)) using Finset.induction_on with
  | empty => simp [reflect_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, reflect_add, ih, reflect_C_mul_X_pow,
      revAt_le (energy_le a)]

private theorem reflect_cbd_pow' (d : ℕ) : reflect (9*d) (cbd 3 ^ d) = rc ^ d := by
  induction d with
  | zero => simp [reflect_one]
  | succ d ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ,
      reflect_mul (F := 9*d) (G := 9) _ _ ((natDegree_pow_le_of_le d cbd_natDegree).trans
        (Nat.mul_comm d 9).le) cbd_natDegree, ih, reflect_cbd]

private theorem reflect_cbd_pow : reflect 1197 (cbd 3 ^ 133) = rc ^ 133 :=
  reflect_cbd_pow' 133

private theorem rc_pow_coeff (i : ℕ) :
    (rc^133).coeff i = shell 3 133 (revAt 1197 i) := by
  rw [← reflect_cbd_pow, coeff_reflect, cbd_coeff]

private theorem shell_zero (i : ℕ) (hi : 1197 < i) : shell 3 133 i = 0 := by
  rw [← cbd_coeff]
  exact coeff_eq_zero_of_natDegree_lt
    ((natDegree_pow_le_of_le 133 cbd_natDegree).trans_lt (by omega))

private theorem eval_rc (b : ℕ) : rc.eval b = revWord b := by
  simp only [rc, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, revWord, sumTo_eq]
  exact Fin.sum_univ_eq_sum_range
    (fun a ↦ Nat.choose 6 a * b^(9 - (Int.ofNat a - 3).natAbs^2)) 7

/-! ## The packed product -/

private noncomputable def Gp : ℕ[X] := ∑ k ∈ Finset.range 1081, C (H - (ballCount 646 (k+1) - 1)) * X^k

private theorem eval_Gp_base : Gp.eval base = gWord := by
  simp [Gp, eval_finsetSum, gWord_eq]

private theorem eval_Gp_one : Gp.eval 1 ≤ 1081 * H := by
  simp only [Gp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  calc _ ≤ ∑ _k ∈ Finset.range 1081, H := Finset.sum_le_sum fun k _ ↦ Nat.sub_le _ _
    _ = _ := by simp

private theorem prod_coeff (E : ℕ) (hE : E < 1081) :
    (rc^133 * Gp).coeff (1197 + E) = condGain 3 133 512 3329 1081 E := by
  rw [Gp, Finset.mul_sum, finsetSum_coeff]
  have hterm (k : ℕ) : (rc^133 * (C (H - (ballCount 646 (k+1) - 1)) * X^k)).coeff (1197 + E) =
      (H - (ballCount 646 (k+1) - 1)) * if k ≤ 1197 + E then (rc^133).coeff (1197 + E - k) else 0 := by
    rw [← mul_assoc, mul_comm (rc^133) (C _), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  simp_rw [hterm]
  rw [← Finset.sum_range_add_sum_Ico _ hE.le]
  rw [Finset.sum_eq_zero (s := Finset.range E) fun k hk ↦ by
    have := Finset.mem_range.mp hk
    rw [if_pos (by omega), rc_pow_coeff, revAt_eq_self_of_lt (by omega),
      shell_zero _ (by omega), mul_zero]]
  rw [zero_add, Finset.sum_Ico_eq_sum_range, condGain]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have := Finset.mem_range.mp hj
  rw [if_pos (by omega), rc_pow_coeff, revAt_le (by omega),
    show 1197 - (1197 + E - (E + j)) = j by omega, Nat.mul_comm,
    show E + j + 1 = j + E + 1 by omega]
  unfold H
  rfl

private theorem pWord_digit (E : ℕ) (hE : E < 1081) :
    digit (pWord / base^1197) E = condGain 3 133 512 3329 1081 E := by
  rw [digit_high]
  unfold digit
  rw [← prod_coeff E hE]
  apply packed_coeff _ _ _ 2279 (by omega)
  · rw [eval_mul, eval_pow, eval_rc, show revWord 1 = 64 by decide]
    calc 64^133 * Gp.eval 1 ≤ 64^133 * (1081 * H) := Nat.mul_le_mul_left _ eval_Gp_one
      _ < base := by unfold H base; norm_num
  · rw [eval_mul, eval_pow, eval_rc, eval_Gp_base]
    unfold pWord packedRev
    rw [Nat.powMod_def]
    exact (Nat.mod_modEq _ _).mul_right _

private theorem cbd_trunc_digit (E : ℕ) :
    digit (packedCBD 512 % base^1081) E = if E < 1081 then shell 3 512 E else 0 := by
  split_ifs with h
  · rw [digit_low _ _ _ h]
    exact cbd_digit (by norm_num) (by omega)
  · exact digit_trunc _ _ _ (by omega)

private theorem S1_eq : S1 = ∑ E ∈ Finset.range 1081,
    shell 3 512 E * (Dn - condGain 3 133 512 3329 1081 E)^2 := by
  rw [S1, foldD_sum, ← Finset.sum_range_add_sum_Ico _ (by norm_num : 1081 ≤ 2^11)]
  rw [Finset.sum_eq_zero (s := Finset.Ico 1081 (2^11)) fun k hk ↦ by
    rw [cbd_trunc_digit, if_neg (by simp at hk; omega), zero_mul], add_zero]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  have := Finset.mem_range.mp hE
  rw [cbd_trunc_digit, if_pos this, pWord_digit E this]

private theorem S0_eq : S0 = ∑ E ∈ Finset.range 1081, shell 3 512 E := by
  rw [S0, foldD_sum, ← Finset.sum_range_add_sum_Ico _ (by norm_num : 1081 ≤ 2^11)]
  rw [Finset.sum_eq_zero (s := Finset.Ico 1081 (2^11)) fun k hk ↦ by
    rw [cbd_trunc_digit, if_neg (by simp at hk; omega)], add_zero]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  rw [cbd_trunc_digit, if_pos (Finset.mem_range.mp hE)]

/-! ## Assembly -/

private theorem shell_total :
    ∑ E ∈ Finset.range (512*3^2+1), (shell 3 512 E : ℚ) = ((4^3 : ℕ) : ℚ)^512 := by
  have h := expect_energy 512 3 (fun _ ↦ 1)
  have h1 : expect (cbdWeight 3) (fun _ : Fin 512 → Digit 3 ↦ (1 : ℚ)) = 1 := by
    unfold expect
    simp only [mul_one]
    rw [← Fintype.prod_sum (fun (_ : Fin 512) (a : Digit 3) ↦ cbdWeight 3 a), cbdWeight_sum]
    simp
  rw [h1, eq_div_iff (by positivity)] at h
  simpa using h.symm

private theorem condBound_eq (E : ℕ) :
    condBound 133 512 3329 3 1081 E =
      ((Dn - condGain 3 133 512 3329 1081 E : ℕ) : ℚ) / (Dn : ℚ) := by
  unfold condBound Dn
  rfl

/-- `Σ_E shell E · condBound(E)²` in terms of the kernel-checked sums. -/
private theorem sigma_eq :
    ∑ E ∈ Finset.range (512*3^2+1), (shell 3 512 E : ℚ) *
        ∏ _i : Fin 2, condBound 133 512 3329 3 1081 E =
      (S1 : ℚ) / (Dn : ℚ)^2 + (((4^3 : ℕ) : ℚ)^512 - S0) := by
  have hD : (0 : ℚ) < Dn := by unfold Dn; positivity
  have hsplit := Finset.sum_range_add_sum_Ico (fun E ↦ (shell 3 512 E : ℚ) *
    ∏ _i : Fin 2, condBound 133 512 3329 3 1081 E) (by norm_num : 1081 ≤ 512*3^2+1)
  have htail : ∑ E ∈ Finset.Ico 1081 (512*3^2+1), (shell 3 512 E : ℚ) *
      ∏ _i : Fin 2, condBound 133 512 3329 3 1081 E =
      ∑ E ∈ Finset.Ico 1081 (512*3^2+1), (shell 3 512 E : ℚ) := by
    refine Finset.sum_congr rfl fun E hE ↦ ?_
    have hE' := (Finset.mem_Ico.mp hE).1
    have hg : condGain 3 133 512 3329 1081 E = 0 := by
      simp [condGain, Nat.sub_eq_zero_of_le hE']
    rw [condBound_eq, hg, Nat.sub_zero, div_self hD.ne']
    simp
  have htot := Finset.sum_range_add_sum_Ico (fun E ↦ (shell 3 512 E : ℚ))
    (by norm_num : 1081 ≤ 512*3^2+1)
  rw [shell_total] at htot
  have hhead : ∑ E ∈ Finset.range 1081, (shell 3 512 E : ℚ) *
      ∏ _i : Fin 2, condBound 133 512 3329 3 1081 E = (S1 : ℚ) / (Dn : ℚ)^2 := by
    rw [S1_eq]
    push_cast [Finset.sum_div]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [Fin.prod_univ_two, condBound_eq]
    field_simp
  have hS0 : (S0 : ℚ) = ∑ E ∈ Finset.range 1081, (shell 3 512 E : ℚ) := by
    rw [S0_eq, Nat.cast_sum]
  rw [← hsplit, htail, hhead, hS0, eq_sub_of_add_eq' htot]

private theorem final_ineq (S0 S1 D N Q W : ℚ) (hD : 0 < D) (hN : 0 < N) (hQ : 0 < Q)
    (h : 99409 * (D^2 * N) * Q + 200000 * W * (D^2 * N) + 100000 * S1 * Q <
      100000 * S0 * D^2 * Q) :
    99409 / 100000 < 1 - (S1 / D^2 + (N - S0)) / N - 2 * (W / Q) := by
  have e : 1 - (S1 / D^2 + (N - S0)) / N - 2 * (W / Q) =
      (100000 * S0 * D^2 * Q - 100000 * S1 * Q - 200000 * W * (D^2 * N)) /
        (100000 * (D^2 * N) * Q) := by
    field_simp
    ring
  rw [e, lt_div_iff₀ (by positivity)]
  linarith

/-- **The recorded instance (PROOF_GAP Part 131).** Plain LWE with `m = 511` rows, `n = 512`,
`q = 3329`, CBD(3); two predetermined disjoint blocks of 133 rows and 245 reserved rows (any
such split). For every exact SVP oracle (two calls in dimension 646), the end-to-end attack
outputs the true secret with probability greater than `99409/100000 = 99.409%`. -/
theorem two_block_success (b : Fin 2 → Fin 133 → Fin 511) (c : Fin 245 → Fin 511)
    (hb : Function.Injective (Sum.elim (fun p : (Σ _i : Fin 2, Fin 133) ↦ b p.1 p.2) c))
    (O : Oracle 512 3329) (hO : IsSVPOracle O) :
    (99409 / 100000 : ℚ) <
      lweProb 511 512 3329 3 (fun s e A ↦
        attack 3 O (fun _ ↦ 133) b c A (lweSample A s e) = some (fun j ↦ centered (s j))) := by
  refine lt_of_lt_of_le ?_ (attack_success_condBound (by norm_num) le_rfl 1081 (by norm_num)
    (fun _ ↦ 133) b c hb O hO)
  rw [sigma_eq, Nat.cast_ofNat, div_pow]
  have hN : (0 : ℚ) < ((4^3 : ℕ) : ℚ)^512 := by positivity
  have hD : (0 : ℚ) < Dn := by unfold Dn; positivity
  refine final_ineq S0 S1 Dn _ ((3329 : ℚ)^245) ((7 : ℚ)^245) hD hN (by positivity) ?_
  have h := final_check
  have h' : ((99409 * (Dn^2 * 64^512) * 3329^245 + 200000 * 7^245 * (Dn^2 * 64^512) +
      100000 * S1 * 3329^245 : ℕ) : ℚ) < ((100000 * S0 * Dn^2 * 3329^245 : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  norm_num at h' ⊢
  linarith

/-- A concrete row split: blocks `[0, 133)` and `[133, 266)`, reserved rows `[266, 511)`. -/
@[expose] def stdBlock (i : Fin 2) (a : Fin 133) : Fin 511 := ⟨i.val * 133 + a.val, by omega⟩
@[expose] def stdReserved (j : Fin 245) : Fin 511 := ⟨266 + j.val, by omega⟩

theorem std_injective :
    Function.Injective (Sum.elim (fun p : (Σ _i : Fin 2, Fin 133) ↦ stdBlock p.1 p.2)
      stdReserved) := by
  rintro (⟨i, a⟩ | j) (⟨i', a'⟩ | j') h <;>
    simp only [Sum.elim_inl, Sum.elim_inr, stdBlock, stdReserved, Fin.ext_iff] at h
  · have hi := i.isLt; have hi' := i'.isLt; have ha := a.isLt; have ha' := a'.isLt
    have : i = i' := by ext; omega
    subst this
    have : a = a' := by ext; omega
    subst this
    rfl
  · have := i.isLt; have := a.isLt; omega
  · have := i'.isLt; have := a'.isLt; omega
  · congr 1; ext; omega

/-- The instance for the concrete split, for every exact SVP oracle. -/
theorem two_block_success_std (O : Oracle 512 3329) (hO : IsSVPOracle O) :
    (99409 / 100000 : ℚ) <
      lweProb 511 512 3329 3 (fun s e A ↦
        attack 3 O (fun _ ↦ 133) stdBlock stdReserved A (lweSample A s e) =
          some (fun j ↦ centered (s j))) :=
  two_block_success stdBlock stdReserved std_injective O hO

end SigabaNeo.Wall1.MultiBlock.Instance

#print axioms SigabaNeo.Wall1.MultiBlock.Instance.ball_check
#print axioms SigabaNeo.Wall1.MultiBlock.Instance.final_check
#print axioms SigabaNeo.Wall1.MultiBlock.Instance.two_block_success
#print axioms SigabaNeo.Wall1.MultiBlock.Instance.two_block_success_std
