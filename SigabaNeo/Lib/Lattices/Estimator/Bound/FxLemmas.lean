import SigabaNeo.Lib.Lattices.Estimator.Fx
import Mathlib.Tactic

/-!
# Order facts about the fixed-point functions

Monotonicity and bounds of `log2Nat`, `log2`, `log2Add` and `exp2`, used to bound attack costs
from below without evaluating them.
-/

namespace SigabaNeo.Lattices.Estimator.Fx

/-- One step of `log2Nat`'s repeated squaring. -/
def l2step (acc : ℕ × ℕ) : ℕ × ℕ :=
  if 2 ^ (K + 1) ≤ (acc.1 * acc.1) >>> K then ((acc.1 * acc.1) >>> K >>> 1, 2 * acc.2 + 1)
  else ((acc.1 * acc.1) >>> K, 2 * acc.2)

theorem ONE_pos : (0 : ℤ) < ONE := by decide

theorem ONE_eq : ONE = ((2 ^ P : ℕ) : ℤ) := by simp [ONE]

theorem log2Nat_eq (v : ℕ) : log2Nat v =
    (Nat.log2 v : ℤ) * ONE + ((List.range P).foldl (fun acc _ => l2step acc)
      ((v <<< K) >>> Nat.log2 v, 0)).2 := rfl

theorem fold_l2step_snd_lt (l : List ℕ) (x : ℕ × ℕ) :
    ((l.foldl (fun acc _ => l2step acc) x).2 + 1) ≤ (x.2 + 1) * 2 ^ l.length := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    refine (ih _).trans ?_
    have : (l2step x).2 + 1 ≤ (x.2 + 1) * 2 := by
      unfold l2step; split <;> simp <;> omega
    calc ((l2step x).2 + 1) * 2 ^ l.length ≤ (x.2 + 1) * 2 * 2 ^ l.length :=
          Nat.mul_le_mul_right _ this
      _ = (x.2 + 1) * 2 ^ (l.length + 1) := by rw [pow_succ]; ring

theorem frac_lt (v : ℕ) : ((List.range P).foldl (fun acc _ => l2step acc)
    ((v <<< K) >>> Nat.log2 v, 0)).2 < 2 ^ P := by
  have := fold_l2step_snd_lt (List.range P) ((v <<< K) >>> Nat.log2 v, 0)
  simp only [List.length_range, zero_add, one_mul] at this
  omega

theorem log2Nat_nonneg (v : ℕ) : 0 ≤ log2Nat v := by
  rw [log2Nat_eq]; have := ONE_pos; positivity

theorem log2Nat_ge (v : ℕ) : (Nat.log2 v : ℤ) * ONE ≤ log2Nat v := by
  rw [log2Nat_eq]; have := Int.natCast_nonneg ((List.range P).foldl (fun acc _ => l2step acc)
      ((v <<< K) >>> Nat.log2 v, 0)).2
  omega

theorem log2Nat_lt (v : ℕ) : log2Nat v < ((Nat.log2 v : ℤ) + 1) * ONE := by
  rw [log2Nat_eq]
  have h := frac_lt v
  have : (((List.range P).foldl (fun acc _ => l2step acc)
      ((v <<< K) >>> Nat.log2 v, 0)).2 : ℤ) < ONE := by
    rw [ONE_eq]; exact_mod_cast h
  linarith

/-- The order preserved by `l2step`: lexicographic on (fraction bits, mantissa). -/
def LexLe (x y : ℕ × ℕ) : Prop := x.2 < y.2 ∨ (x.2 = y.2 ∧ x.1 ≤ y.1)

theorem l2step_lexLe {x y : ℕ × ℕ} (h : LexLe x y) : LexLe (l2step x) (l2step y) := by
  unfold LexLe l2step at *
  rcases h with h | ⟨h1, h2⟩
  · left; split <;> split <;> simp <;> omega
  · have hm : (x.1 * x.1) >>> K ≤ (y.1 * y.1) >>> K := by
      simp only [Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right (Nat.mul_le_mul h2 h2)
    split <;> split
    · right; refine ⟨by simp [h1], ?_⟩
      simp only [Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right (by simpa [Nat.shiftRight_eq_div_pow] using hm)
    · omega
    · left; simp; omega
    · right; exact ⟨by simp [h1], hm⟩

theorem fold_lexLe (l : List ℕ) {x y : ℕ × ℕ} (h : LexLe x y) :
    LexLe (l.foldl (fun acc _ => l2step acc) x) (l.foldl (fun acc _ => l2step acc) y) := by
  induction l generalizing x y with
  | nil => exact h
  | cons a l ih => exact ih (l2step_lexLe h)

/-- The fraction bits, as a function of the mantissa. -/
def frac (m : ℕ) : ℕ := ((List.range P).foldl (fun acc _ => l2step acc) (m, 0)).2

theorem log2Nat_eq' (v : ℕ) : log2Nat v = (Nat.log2 v : ℤ) * ONE + frac ((v <<< K) >>> Nat.log2 v) :=
  rfl

theorem frac_mono {a b : ℕ} (h : a ≤ b) : frac a ≤ frac b := by
  have := fold_lexLe (List.range P) (x := (a, 0)) (y := (b, 0)) (Or.inr ⟨rfl, h⟩)
  unfold LexLe at this; unfold frac; omega

theorem fold_l2step_fix (l : List ℕ) {x : ℕ × ℕ} (hx : l2step x = x) :
    l.foldl (fun acc _ => l2step acc) x = x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, hx, ih]

theorem frac_zero : frac 0 = 0 := by
  unfold frac; rw [fold_l2step_fix _ (by simp [l2step])]

theorem log2Nat_zero : log2Nat 0 = 0 := by
  rw [log2Nat_eq']; simp [frac_zero]

theorem log2Nat_mono {a b : ℕ} (h : a ≤ b) : log2Nat a ≤ log2Nat b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [log2Nat_zero]; exact log2Nat_nonneg b
  have hlog : Nat.log2 a ≤ Nat.log2 b := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right h
  rcases Nat.lt_or_eq_of_le hlog with hlt | heq
  · have h1 := log2Nat_lt a
    have h2 := log2Nat_ge b
    have h3 : ((Nat.log2 a : ℤ) + 1) * ONE ≤ (Nat.log2 b : ℤ) * ONE := by
      apply Int.mul_le_mul_of_nonneg_right _ (by decide); omega
    linarith
  · rw [log2Nat_eq', log2Nat_eq', heq]
    have hm : (a <<< K) >>> Nat.log2 b ≤ (b <<< K) >>> Nat.log2 b := by
      simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)
    have := frac_mono hm
    have : (frac ((a <<< K) >>> Nat.log2 b) : ℤ) ≤ frac ((b <<< K) >>> Nat.log2 b) := by
      exact_mod_cast this
    linarith

theorem l2step_pow : l2step (2 ^ K, 0) = (2 ^ K, 0) := by
  unfold l2step
  simp only [Nat.shiftRight_eq_div_pow, ← pow_add]
  rw [Nat.pow_div (by omega) (by norm_num), show K + K - K = K by omega]
  have : 0 < 2 ^ K := Nat.two_pow_pos K
  split_ifs with h
  · rw [pow_succ] at h; omega
  · rfl

theorem fold_l2step_pow (l : List ℕ) : l.foldl (fun acc _ => l2step acc) (2 ^ K, 0) = (2 ^ K, 0) :=
  fold_l2step_fix l l2step_pow

theorem log2Nat_two_pow (e : ℕ) : log2Nat (2 ^ e) = (e : ℤ) * ONE := by
  rw [log2Nat_eq, Nat.log2_two_pow]
  have : (2 ^ e <<< K) >>> e = 2 ^ K := by
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, ← pow_add]
    rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  rw [this, fold_l2step_pow]; simp

theorem log2Nat_lt_of_lt_two_pow {v e : ℕ} (hv : 0 < v) (h : v < 2 ^ e) :
    log2Nat v < (e : ℤ) * ONE := by
  have : Nat.log2 v < e := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_lt_of_lt_pow (by omega) h
  have h1 := log2Nat_lt v
  have h2 : ((Nat.log2 v : ℤ) + 1) * ONE ≤ (e : ℤ) * ONE :=
    Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt ONE_pos)
  linarith

theorem ONE_toNat : ONE.toNat = 2 ^ P := by decide

theorem log2_mono {a b : Fx} (h : a ≤ b) : log2 a ≤ log2 b := by
  unfold log2; have := log2Nat_mono (Int.toNat_le_toNat h); linarith

theorem log2_ONE : log2 ONE = 0 := by
  unfold log2; rw [ONE_toNat, log2Nat_two_pow]; ring

theorem log2_nonneg {x : Fx} (h : ONE ≤ x) : 0 ≤ log2 x := log2_ONE ▸ log2_mono h

theorem log2_nonpos {x : Fx} (h : x ≤ ONE) : log2 x ≤ 0 := log2_ONE ▸ log2_mono h

/-- The Taylor sum stays in `[0, s + fuel]` for `t ∈ [0, 1]` and a first term in `[0, 1]`. -/
theorem expTaylor_bounds {t : Fx} (ht0 : 0 ≤ t) (ht1 : t ≤ ONE) :
    ∀ (fuel i : ℕ) (s term : Fx), 0 ≤ s → 0 ≤ term → term ≤ ONE →
      0 ≤ expTaylor t fuel i s term ∧ expTaylor t fuel i s term ≤ s + fuel * ONE := by
  intro fuel
  induction fuel with
  | zero => intro i s term hs _ _; simp [expTaylor, hs]
  | succ fuel ih =>
    intro i s term hs ht hT
    simp only [expTaylor]
    have hm0 : 0 ≤ mul term t := by unfold mul; exact Int.fdiv_nonneg (mul_nonneg ht ht0) (le_of_lt ONE_pos)
    have hm1 : mul term t ≤ ONE := by
      unfold mul
      rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
      apply Int.ediv_le_of_le_mul ONE_pos
      nlinarith
    have hd0 : 0 ≤ Int.fdiv (mul term t) i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · exact Int.fdiv_nonneg hm0 (by omega)
    have hd1 : Int.fdiv (mul term t) i ≤ ONE := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp; exact le_of_lt ONE_pos
      · rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
        exact (Int.ediv_le_self _ hm0).trans hm1
    split
    · constructor
      · exact hs
      · have := ONE_pos; push_cast; nlinarith
    · obtain ⟨h1, h2⟩ := ih (i + 1) (s + Int.fdiv (mul term t) i) (Int.fdiv (mul term t) i)
        (by linarith) hd0 hd1
      refine ⟨h1, h2.trans ?_⟩
      push_cast; linarith

theorem exp2_parts (y : Fx) : 0 ≤ y - Int.fdiv y ONE * ONE ∧ y - Int.fdiv y ONE * ONE < ONE := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
  have := Int.mul_ediv_add_emod y ONE
  have h0 := Int.emod_nonneg y (ne_of_gt ONE_pos)
  have h1 := Int.emod_lt_of_pos y ONE_pos
  constructor <;> nlinarith

theorem LN2_le : (0 : ℤ) ≤ LN2 ∧ LN2 ≤ ONE := by decide

theorem mul_LN2_bounds {f : Fx} (h0 : 0 ≤ f) (h1 : f < ONE) : 0 ≤ mul f LN2 ∧ mul f LN2 ≤ ONE := by
  have := LN2_le
  unfold mul
  constructor
  · exact Int.fdiv_nonneg (mul_nonneg h0 this.1) (le_of_lt ONE_pos)
  · rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
    apply Int.ediv_le_of_le_mul ONE_pos
    nlinarith

theorem exp2_sum_bounds (y : Fx) :
    0 ≤ expTaylor (mul (y - Int.fdiv y ONE * ONE) LN2) 63 1 ONE ONE ∧
      expTaylor (mul (y - Int.fdiv y ONE * ONE) LN2) 63 1 ONE ONE ≤ 64 * ONE := by
  obtain ⟨h0, h1⟩ := exp2_parts y
  obtain ⟨t0, t1⟩ := mul_LN2_bounds h0 h1
  have := expTaylor_bounds t0 t1 63 1 ONE ONE (le_of_lt ONE_pos) (le_of_lt ONE_pos) le_rfl
  constructor
  · exact this.1
  · have h := this.2; push_cast at h; linarith

theorem exp2_nonneg (y : Fx) : 0 ≤ exp2 y := by
  obtain ⟨h0, _⟩ := exp2_sum_bounds y
  unfold exp2
  simp only
  split
  · positivity
  · exact Int.fdiv_nonneg h0 (by positivity)

/-- `2^y` underflows to `0` below `-55`. -/
theorem exp2_eq_zero {y : Fx} (hy : y ≤ -55 * ONE) : exp2 y = 0 := by
  obtain ⟨h0, h1⟩ := exp2_sum_bounds y
  have hk : Int.fdiv y ONE ≤ -55 := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt ONE_pos)]
    have := Int.ediv_le_ediv ONE_pos hy
    rwa [Int.mul_ediv_cancel _ (ne_of_gt ONE_pos)] at this
  unfold exp2
  simp only
  have hk' : ¬ (0 ≤ Int.fdiv y ONE) := by omega
  simp only [hk', ↓reduceIte]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity)]
  apply Int.ediv_eq_zero_of_lt h0
  have : (64 : ℤ) * ONE < 2 ^ 55 := by decide
  calc _ ≤ 64 * ONE := h1
    _ < 2 ^ 55 := this
    _ ≤ 2 ^ (-Int.fdiv y ONE).toNat := pow_le_pow_right₀ (by norm_num) (by omega)

theorem log2Add_ge_max (a b : Fx) : max a b ≤ log2Add a b := by
  unfold log2Add
  have := log2_nonneg (x := ONE + exp2 (min a b - max a b)) (by have := exp2_nonneg (min a b - max a b); linarith)
  linarith

theorem le_log2Add_left (a b : Fx) : a ≤ log2Add a b := (le_max_left a b).trans (log2Add_ge_max a b)

theorem le_log2Add_right (a b : Fx) : b ≤ log2Add a b := (le_max_right a b).trans (log2Add_ge_max a b)

end SigabaNeo.Lattices.Estimator.Fx
