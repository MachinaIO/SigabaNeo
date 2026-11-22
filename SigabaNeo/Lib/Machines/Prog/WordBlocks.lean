import SigabaNeo.Lib.Machines.Prog.Stream

/-!
# Constant words and blocks of words as tape programs

All programs are in the fragment `NoGrow` (no lengthening of words), so the sizes come from
templates: tapes holding words of the right lengths.

* `constP w : Prog 2` (`0` output, `1` a word of length `|w|`): `0 := w`, by shifting the bits of
  `w` into a copy of the template (`run_constP`); `size (constP w) = 36 · (|w| + 2)`.
* `blockP : Prog 9` (`0` output, `1` `w`, `2` a word of length `i`, `3` a word of length `K`;
  scratch `4 … 8`): `0 := (w.drop (i * K)).take K`, the block `i` (`run_blockP`).
* `replaceP : Prog 12` (`0` output, `1` `w`, `2` a word of length `i`, `3` a word of length `K`,
  `4` a word `v` of length `K`; scratch `5 … 11`):
  `0 := w.take (i * K) ++ v ++ w.drop ((i + 1) * K)` (`run_replaceP`).
* Appending a word to a register is `mvP` (`SigabaNeo.Lib.Machines.Prog.Stream`), and the counter
  idiom `for i < n` is `forN`.
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

/-! ### Constant words -/

/-- Shift the bits of a word into the register `0`. -/
def pushBits : List Bool → Prog 2
  | [] => nop 0
  | b :: bs => sin b 0 ⨾ pushBits bs

theorem run_pushBits : ∀ (bs : List Bool) (s : Store 2),
    run (pushBits bs) s = Function.update s 0 ((s 0 ++ bs).drop bs.length)
  | [], s => by funext t; fin_cases t <;> simp [pushBits]
  | b :: bs, s => by
    rw [pushBits, run_seq, run_sin, run_pushBits bs, Function.update_self, Function.update_idem,
      tail_append_drop, List.length_cons]

/-- **A constant word**, from a template of its length. -/
def constP (w : List Bool) : Prog 2 := cp 0 1 ⨾ pushBits w

theorem run_constP (w : List Bool) (s : Store 2) (h : (s 1).length = w.length) :
    run (constP w) s = Function.update s 0 w := by
  rw [constP, run_seq, run_copy, run_pushBits, Function.update_self, Function.update_idem,
    List.drop_left' h]

theorem noGrowB_pushBits : ∀ bs, (pushBits bs).noGrowB = true
  | [] => rfl
  | b :: bs => by simp [pushBits, noGrowB, noGrowB_pushBits bs, sin, Prim.noGrowB]

theorem noGrow_constP (w : List Bool) : (constP w).NoGrow := by
  simp [NoGrow, constP, noGrowB, Prim.noGrowB, noGrowB_pushBits]

theorem size_constP (w : List Bool) : size (constP w) = 36 * (w.length + 2) := by
  have : ∀ bs, size (pushBits bs) = 36 * (bs.length + 1) := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp only [pushBits, size, ih, List.length_cons, sin, Prim.pad]; ring
  simp only [constP, size, this, Prim.pad]; ring

/-! ### Blocks -/

def bk1 : Fin 5 → Fin 9 := ![4, 5, 6, 2, 3]
def bk2 : Fin 5 → Fin 9 := ![4, 0, 7, 8, 3]
theorem bk1_inj : Function.Injective bk1 := by decide
theorem bk2_inj : Function.Injective bk2 := by decide

/-- **The block `i` of `K` bits** of a word. Tapes `4` a stream, `5 … 8` counters and a bit. -/
def blockP : Prog 9 := cp 4 1 ⨾ map bk1 skipP ⨾ cp 0 3 ⨾ map bk2 mvP ⨾ clr 4

set_option linter.unusedSimpArgs false in
theorem run_blockP {i K : ℕ} (s : Store 9) (hs : ∀ j : Fin 9, 4 ≤ j.val → s j = [])
    (hi : (s 2).length = i) (hK : (s 3).length = K) (hw : (i + 1) * K ≤ (s 1).length) :
    run blockP s = Function.update s 0 (((s 1).drop (i * K)).take K) := by
  simp only [blockP, run_seq, run_copy, run_clear]
  rw [run_skipP_map bk1_inj _ ?_ ?_, run_mvP_map bk2_inj _ ?_ ?_]
  rotate_left
  all_goals try simp [bk1, bk2, hs]
  have hle : K ≤ ((s 1).drop (i * K)).length := by
    rw [List.length_drop]; rw [Nat.succ_mul] at hw; omega
  funext t
  fin_cases t <;> simp [bk1, bk2, hi, hK, hs, drop_append_of_length' hK, takeD_eq_take hle]
where
  drop_append_of_length' {r : List Bool} {n : ℕ} (h : r.length = n) (l : List Bool) :
      (r ++ l).drop n = l := by subst h; simp

/-! ### Replacing a block -/

def rpA : Fin 5 → Fin 12 := ![5, 0, 9, 11, 3]
def rpD : Fin 3 → Fin 12 := ![5, 11, 3]
def rpV : Fin 5 → Fin 12 := ![10, 0, 9, 11, 3]
def rpS : Fin 5 → Fin 12 := ![6, 7, 8, 2, 3]
def rpD' : Fin 3 → Fin 12 := ![6, 11, 3]
def rpR : Fin 5 → Fin 12 := ![5, 0, 9, 11, 6]
theorem rpA_inj : Function.Injective rpA := by decide
theorem rpD_inj : Function.Injective rpD := by decide
theorem rpV_inj : Function.Injective rpV := by decide
theorem rpS_inj : Function.Injective rpS := by decide
theorem rpD'_inj : Function.Injective rpD' := by decide
theorem rpR_inj : Function.Injective rpR := by decide

/-- **Replace the block `i` of `K` bits** of `w` by `v`. Tapes `5` the stream of `w`, `6` the
count of the bits after the block, `7` `8` `11` counters, `9` a bit, `10` the stream of `v`. -/
def replaceP : Prog 12 :=
  cp 0 1 ⨾ cp 5 1 ⨾ cp 6 1 ⨾ forN 7 2 (map rpA mvP) ⨾ map rpD dropP ⨾ cp 10 4 ⨾ map rpV mvP ⨾
    map rpS skipP ⨾ map rpD' dropP ⨾ map rpR mvP ⨾ clr 5 ⨾ clr 6 ⨾ clr 10

set_option linter.unusedSimpArgs false in
theorem run_replaceP {i K : ℕ} (s : Store 12) (hs : ∀ j : Fin 12, 5 ≤ j.val → s j = [])
    (hi : (s 2).length = i) (hK : (s 3).length = K) (hv : (s 4).length = K)
    (hw : (i + 1) * K ≤ (s 1).length) :
    run replaceP s = Function.update s 0
      ((s 1).take (i * K) ++ s 4 ++ (s 1).drop ((i + 1) * K)) := by
  set w := s 1
  have hc : ∀ j : Fin 12, 5 ≤ j.val → j ≠ 7 → s j = [] := fun j hj _ => hs j hj
  let G : List Bool × List Bool → Store 12 := fun a =>
    Function.update (Function.update (Function.update s 0 a.2) 5 a.1) 6 w
  have hloop := run_forN 7 2 (map rpA mvP) G (mvK K) (fun a w' => by
      obtain ⟨sv, ov⟩ := a
      rw [run_mvP_map rpA_inj _ (by simp [G, rpA, hc]) (by simp [G, rpA, hc])]
      funext t; fin_cases t <;> simp [G, rpA, hK, mvK]) (w, w)
    (Function.update (Function.update (Function.update s 0 w) 5 w) 6 w)
    (by funext t; fin_cases t <;> simp [G])
  have hsplit : run replaceP s = run (map rpD dropP ⨾ cp 10 4 ⨾ map rpV mvP ⨾
      map rpS skipP ⨾ map rpD' dropP ⨾ map rpR mvP ⨾ clr 5 ⨾ clr 6 ⨾ clr 10)
      (run (forN 7 2 (map rpA mvP)) (run (cp 6 1) (run (cp 5 1) (run (cp 0 1) s)))) := rfl
  have e0 : run (cp 6 1) (run (cp 5 1) (run (cp 0 1) s)) =
      Function.update (Function.update (Function.update s 0 w) 5 w) 6 w := by
    funext t; simp only [run_copy]; fin_cases t <;> simp [w]
  have h2 : Function.update (Function.update (Function.update s 0 w) 5 w) 6 w 2 = s 2 := by simp
  rw [hsplit, e0, hloop, h2, hi, mvK_iter]
  simp only [run_seq, run_copy, run_clear]
  rw [run_dropP_map rpD_inj _ ?_, run_mvP_map rpV_inj _ ?_ ?_, run_skipP_map rpS_inj _ ?_ ?_,
    run_dropP_map rpD'_inj _ ?_, run_mvP_map rpR_inj _ ?_ ?_]
  · have hw' : i * K + K ≤ w.length := by rw [Nat.succ_mul] at hw; exact hw
    have hle : i * K ≤ w.length := by omega
    have hrest : ((w.drop (i * K)).drop K).length = w.length - (i * K + K) := by
      simp only [List.length_drop]; omega
    have e1 := drop_append_drop w (takeD (i * K) w) (takeD K (s 4))
    simp only [length_takeD, List.length_append] at e1
    have hout : List.drop (w.length - (i * K + K))
        (List.drop (i * K + K) (w ++ (takeD (i * K) w ++ takeD K (s 4))) ++
          takeD (w.length - (i * K + K)) (List.drop (i * K + K) w)) =
        List.take (i * K) w ++ (s 4 ++ List.drop ((i + 1) * K) w) := by
      rw [← List.drop_append_of_le_length (by simp), List.drop_drop, List.append_assoc,
        List.drop_left' (l₁ := w) (by omega), takeD_eq_take hle, takeD_of_length' hv,
        takeD_of_length' (by simp), Nat.succ_mul]
      simp only [List.append_assoc]
    funext t
    fin_cases t <;> simp [G, rpD, rpV, rpS, rpD', rpR, hs, hK, hi, hc, e1, hrest, hout,
      List.drop_drop]
  all_goals simp [G, rpD, rpV, rpS, rpD', rpR, hs, hc]

theorem noGrow_blockP : blockP.NoGrow := rfl
theorem noGrow_replaceP : replaceP.NoGrow := rfl
theorem wf_blockP : blockP.WF := wf_of_wfB (by decide)
theorem wf_replaceP : replaceP.WF := wf_of_wfB (by decide)

theorem bounds_blockP (L : ℕ) : lenBound blockP L = L ∧ timeBound blockP L ≤ 46 * (L + 1) ^ 3 ∧
    size blockP = 514 := bounds_of _ noGrow_blockP rfl rfl rfl L
theorem bounds_replaceP (L : ℕ) : lenBound replaceP L = L ∧
    timeBound replaceP L ≤ 125 * (L + 1) ^ 3 ∧ size replaceP = 1395 :=
  bounds_of _ noGrow_replaceP rfl rfl rfl L
theorem bounds_mvP (L : ℕ) : lenBound mvP L = L ∧ timeBound mvP L ≤ 20 * (L + 1) ^ 2 ∧
    size mvP = 220 := bounds_of _ noGrow_mvP rfl rfl rfl L

end Prog

end SigabaNeo.Tape
