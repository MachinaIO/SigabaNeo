import PE.Impl.ExpLUT.Params.Correct
import PE.BranchingProgram

/-!
# From the universe's programs to the branching programs of ExpLUT

The universe of `PE.BranchingProgram` at the width `w8` (16 symbols of 8 bits, 14-bit states):
a program `F : Program w8` has transition tables `step i : ProgState → Symbol → ProgState`
(`i < 15`) and an output table `out : ProgState → Symbol → Bool`. As a branching program of
ExpLUT (`BP`, Definition 2 of ePrint 2026/2539, `toBP`):

* length `T = 16`, width `w = 2^14`, alphabet `|Σ| = 2^8`, so `W = w|Σ| = 2^22`; step `i` reads
  symbol `i` (`read8`);
* the tables (`step8`): `f_i(z, a) = step i z a` for `i < 15` and `f_{15}(z, a) = [out z a]`
  (`1` for `true`), read on residues (`z mod 2^14`, `a mod 2^8`) so that they are total; the lookup
  tables of ExpLUT are then `L_i(z + w a) = f_i(z, a)` (`BP.table`);
* the attribute `x` as the naturals `x_t` (`attrN`).

**`eval_toBP`**: `(toBP F).eval (attrN x) = [F.output x]`, so a key for `F` is authorized for `x`
(`F.output x = false`) iff `(toBP F).eval (attrN x) = 0` (`eval_toBP_eq_zero_iff`); `toBP F` is
well formed for `W = 2^22` (`wf_toBP`).

**`correct_w8`**: for every program `F`, every attribute `x` authorized for `F` and every bit `M`,
decryption at the concrete parameters fails with probability at most `2^{−128}`.
-/

namespace AdvancedEncryption.ExpLUT

open AdvancedEncryption.PE.BranchingProgram
open scoped ENNReal

/-- The positions of the attribute: its `16` symbols. -/
abbrev Pos8 : Type := Fin w8.len

theorem w8_len : w8.len = 16 := rfl

/-- The read map: step `i` reads symbol `i` (modulo `16`). -/
def read8 (i : ℕ) : Pos8 := ⟨i % w8.len, Nat.mod_lt _ w8.len_pos⟩

/-- The tables `f_i(z, a)` of a program, on residues: the transitions for `i < 15`, the output
(`1` for `true`) for the last step. -/
def step8 (F : Program w8) (i z a : ℕ) : ℕ :=
  if h : i + 1 < w8.len then
    (F.step ⟨i, by omega⟩ ⟨z % 2 ^ stateBits, Nat.mod_lt _ (by positivity)⟩
      ⟨a % 2 ^ w8.bits, Nat.mod_lt _ (by positivity)⟩).val
  else if F.out ⟨z % 2 ^ stateBits, Nat.mod_lt _ (by positivity)⟩
      ⟨a % 2 ^ w8.bits, Nat.mod_lt _ (by positivity)⟩ then 1 else 0

/-- **The branching program of a program**: length `16`, width `2^14`, alphabet `2^8`. -/
def toBP (F : Program w8) : BP Pos8 where
  T := w8.len
  w := 2 ^ stateBits
  nsym := 2 ^ w8.bits
  read := read8
  step := step8 F

/-- The attribute as natural numbers. -/
def attrN (x : Attribute w8) : Pos8 → ℕ := fun t => (x t).val

theorem attrN_lt (F : Program w8) (x : Attribute w8) (t : Pos8) : attrN x t < (toBP F).nsym :=
  (x t).isLt

theorem toBP_T (F : Program w8) : (toBP F).T = 16 := rfl

/-- **`toBP F` is well formed** for `W = 2^22`. -/
theorem wf_toBP (F : Program w8) : (toBP F).WF (2 ^ 22) where
  T_pos := w8.len_pos
  w_pos := by show 0 < 2 ^ stateBits; positivity
  le_W := by show 2 ^ 14 * 2 ^ 8 ≤ 2 ^ 22; norm_num
  step_lt i z a hi _ _ := by
    show step8 F i z a < 2 ^ stateBits
    unfold step8
    rw [dite_eq_left_of_eq_true (eq_true (show i + 1 < w8.len from hi))]
    exact Fin.isLt _

/-- The state after `n ≤ 15` steps, as a fold of the transition tables. -/
def runN (F : Program w8) (x : Attribute w8) (n : ℕ) (hn : n ≤ w8.len - 1) : ProgState :=
  Fin.foldl n (fun z i => F.step (Fin.castLE hn i) z (x ⟨i.val, by have := w8.len_pos; omega⟩)) 0

theorem runN_full (F : Program w8) (x : Attribute w8) : runN F x (w8.len - 1) le_rfl = F.run x :=
  rfl

theorem runN_succ (F : Program w8) (x : Attribute w8) (n : ℕ) (hn : n + 1 ≤ w8.len - 1) :
    runN F x (n + 1) hn = F.step ⟨n, by omega⟩ (runN F x n (by omega))
      (x ⟨n, by have := w8.len_pos; omega⟩) := by
  unfold runN
  rw [Fin.foldl_succ_last]
  rfl

/-- **The states agree**: before step `n ≤ 15`, the state of `toBP F` is that of `F`. -/
theorem state_toBP (F : Program w8) (x : Attribute w8) :
    ∀ n (hn : n ≤ w8.len - 1), (toBP F).state (attrN x) n = (runN F x n hn).val := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n + 1 < w8.len := by have := w8.len_pos; omega
    rw [runN_succ F x n hn]
    show step8 F n ((toBP F).state (attrN x) n) (attrN x (read8 n)) = _
    unfold step8
    rw [dite_eq_left_of_eq_true (eq_true hlt), ih (by omega)]
    have hr : read8 n = ⟨n, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hz : (⟨(runN F x n (by omega)).val % 2 ^ stateBits, Nat.mod_lt _ (by positivity)⟩ :
        ProgState) = runN F x n (by omega) := Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
    have ha : (⟨attrN x (read8 n) % 2 ^ w8.bits, Nat.mod_lt _ (by positivity)⟩ : Symbol w8) =
        x ⟨n, by omega⟩ := by
      rw [hr]; exact Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
    rw [hz, ha]

/-- **The output agrees**: `(toBP F)(x) = [F(x)]`. -/
theorem eval_toBP (F : Program w8) (x : Attribute w8) :
    (toBP F).eval (attrN x) = if F.output x then 1 else 0 := by
  have hs := state_toBP F x (w8.len - 1) le_rfl
  rw [runN_full] at hs
  have hT : (toBP F).T = (w8.len - 1) + 1 := rfl
  unfold BP.eval
  rw [hT]
  show step8 F (w8.len - 1) ((toBP F).state (attrN x) (w8.len - 1)) (attrN x (read8 (w8.len - 1))) = _
  unfold step8
  rw [dite_eq_right_of_eq_false (eq_false (by omega)), hs]
  have hr : read8 (w8.len - 1) = ⟨w8.len - 1, by have := w8.len_pos; omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by have := w8.len_pos; omega))
  have hz : (⟨(F.run x).val % 2 ^ stateBits, Nat.mod_lt _ (by positivity)⟩ : ProgState) =
      F.run x := Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
  have ha : (⟨attrN x (read8 (w8.len - 1)) % 2 ^ w8.bits, Nat.mod_lt _ (by positivity)⟩ :
      Symbol w8) = x ⟨w8.len - 1, by have := w8.len_pos; omega⟩ := by
    rw [hr]; exact Fin.ext (Nat.mod_eq_of_lt (Fin.isLt _))
  rw [hz, ha]
  rfl

/-- **Authorization**: `F(x) = 0` for `toBP F` iff the key for `F` is authorized for `x`. -/
theorem eval_toBP_eq_zero_iff (F : Program w8) (x : Attribute w8) :
    (toBP F).eval (attrN x) = 0 ↔ F.output x = false := by
  rw [eval_toBP]
  cases F.output x <;> simp

namespace Params

/-- **Correctness for the universe's programs** at the concrete parameters: for every program `F`
of `w8`, every attribute `x` with `F(x) = 0` and every bit `M`, decryption fails with probability
at most `2^{−128}`. -/
theorem correct_w8 (F : Program w8) (x : Attribute w8) (hFx : F.output x = false) (M : Bool) :
    correctExp (toBP F) (attrN x) M false ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ :=
  correct_fail_le (toBP F) (wf_toBP F) (le_of_eq (toBP_T F)) (attrN x) (attrN_lt F x)
    ((eval_toBP_eq_zero_iff F x).mpr hFx) M

/-- The same as a bound on success: `1 − 2^{−128} ≤ P[Dec = M]`. -/
theorem correct_w8_ge (F : Program w8) (x : Attribute w8) (hFx : F.output x = false) (M : Bool) :
    1 - ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ correctExp (toBP F) (attrN x) M true :=
  correct_ge (toBP F) (wf_toBP F) (le_of_eq (toBP_T F)) (attrN x) (attrN_lt F x)
    ((eval_toBP_eq_zero_iff F x).mpr hFx) M

end Params

end AdvancedEncryption.ExpLUT
