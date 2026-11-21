import SigabaNeo.Lib.Machines.Inline.Main

/-!
# Inlining an oracle handler: the preparation

The straight-line preparation writes the encoding `w` of the initial handler state on `st` (and
rewinds it), then the unary clock of `T` cells, and steps back onto its last cell: after
`2 |w| + T + 1` steps the inlined machine simulates the initial configuration of the oracle
machine with all flags `empty` and `T` steps on the clock (`lawR_prep`).
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The tapes after `i` preparation steps. -/
def prepF (i : ℕ) : Tape kA ops m → ℤ → Option Bool
  | .st => tapeOfList (w.take i)
  | .clock => tapeOfList (List.replicate (i - 2 * w.length) true)
  | _ => fun _ => none

/-- The heads after `i` preparation steps. -/
def prepP (i : ℕ) : Tape kA ops m → ℤ
  | .st => if i ≤ w.length then i else if i ≤ 2 * w.length then 2 * w.length - i else 0
  | .clock => (i - 2 * w.length : ℕ)
  | _ => 0

theorem take_succ_eq (i : ℕ) (h : i < w.length) : w.take (i + 1) = w.take i ++ [w[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-- One preparation step. -/
theorem lawR_prep_step (i : ℕ) (hi : i + 1 < 2 * w.length + T + 1) (N : ℕ) :
    lawR H M T w (x := x) (N + 1) (mkR (some (.inl ⟨i, by omega⟩ : RState SA H T w)) 1
        (prepF w i) (prepP w i) []) =
      lawR H M T w N (mkR (some (.inl ⟨i + 1, hi⟩ : RState SA H T w)) 1
        (prepF (m := m) (kA := kA) (ops := ops) w (i + 1)) (prepP w (i + 1)) []) := by
  have hnext : (if h : i + 1 < 2 * w.length + T + 1 then
      (some (.inl ⟨i + 1, h⟩) : Option (RState SA H T w)) else
      some (simS H T w M.initial (fun _ => .empty))) = some (.inl ⟨i + 1, hi⟩) := dite_eq_left hi
  by_cases h1 : i < w.length
  · have hact : prepAct H M T w ⟨i, by omega⟩ = mkAct 0 (mv1 .st (some (some w[i])) 1) none
        (some (.inl ⟨i + 1, hi⟩)) := by
      simp only [prepAct, h1, dite_true]; rw [hnext]
    rw [lawR_det H M T w N _ 1 _ _ [] 0 _ none _ (fun bit => by simp only [machine]; rw [hact])]
    simp only [wr_mv1, pos_mv1, moveInputPos_zero, Option.toList_none, List.append_nil]
    congr 2
    · funext t
      by_cases ht : t = .st
      · subst ht
        simp only [Function.update_self, prepF, prepP, wr, show i ≤ w.length by omega, ite_true]
        rw [take_succ_eq w i h1, tapeOfList_append_single, List.length_take,
          min_eq_left (by omega)]
      · rw [Function.update_of_ne ht]
        have e1 : i - 2 * w.length = 0 := by omega
        have e2 : i + 1 - 2 * w.length = 0 := by omega
        rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepF]
    · funext t
      by_cases ht : t = .st
      · subst ht
        simp only [Function.update_self, prepP, show i ≤ w.length by omega,
          show i + 1 ≤ w.length by omega, ite_true]
        simp
      · rw [Function.update_of_ne ht]
        rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepP]; omega
  by_cases h2 : i < 2 * w.length
  · have hact : prepAct H M T w ⟨i, by omega⟩ = mkAct 0 (mv1 .st none (-1)) none
        (some (.inl ⟨i + 1, hi⟩)) := by
      simp only [prepAct, h1, h2, dite_false, ite_true]; rw [hnext]
    rw [lawR_det H M T w N _ 1 _ _ [] 0 _ none _ (fun bit => by simp only [machine]; rw [hact])]
    simp only [wr_mv1, pos_mv1, moveInputPos_zero, Option.toList_none, List.append_nil, wr_none]
    congr 2
    · funext t
      by_cases ht : t = .st
      · subst ht
        simp only [Function.update_self, prepF]
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      · rw [Function.update_of_ne ht]
        have e1 : i - 2 * w.length = 0 := by omega
        have e2 : i + 1 - 2 * w.length = 0 := by omega
        rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepF]
    · funext t
      by_cases ht : t = .st
      · subst ht
        simp only [Function.update_self, prepP]
        split_ifs <;> simp <;> omega
      · rw [Function.update_of_ne ht]
        rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepP]; omega
  have h3 : i < 2 * w.length + T := by omega
  have hact : prepAct H M T w ⟨i, by omega⟩ = mkAct 0 (mv1 .clock (some (some true)) 1) none
      (some (.inl ⟨i + 1, hi⟩)) := by
    simp only [prepAct, h1, h2, h3, dite_false, ite_false, ite_true]; rw [hnext]
  rw [lawR_det H M T w N _ 1 _ _ [] 0 _ none _ (fun bit => by simp only [machine]; rw [hact])]
  simp only [wr_mv1, pos_mv1, moveInputPos_zero, Option.toList_none, List.append_nil]
  congr 2
  · funext t
    by_cases ht : t = .clock
    · subst ht
      simp only [Function.update_self, prepF, prepP, wr]
      rw [show i + 1 - 2 * w.length = (i - 2 * w.length) + 1 by omega, List.replicate_succ',
        tapeOfList_append_single, List.length_replicate]
    · rw [Function.update_of_ne ht]
      rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepF];
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · funext t
    by_cases ht : t = .clock
    · subst ht
      simp only [Function.update_self, prepP]
      push_cast [show 2 * w.length ≤ i by omega, show 2 * w.length ≤ i + 1 by omega]
      simp; omega
    · rw [Function.update_of_ne ht]
      rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepP]; omega

/-- The last preparation step. -/
theorem lawR_prep_last (N : ℕ) :
    lawR H M T w (x := x) (N + 1) (mkR (some (.inl ⟨2 * w.length + T, by omega⟩ :
        RState SA H T w)) 1 (prepF w (2 * w.length + T)) (prepP w (2 * w.length + T)) []) =
      lawR H M T w N (embA (m := m) H T w (M.initialConfig x) (fun _ => .empty) w T) := by
  have hact : prepAct H M T w ⟨2 * w.length + T, by omega⟩ = mkAct 0 (mv1 .clock none (-1)) none
      (some (simS H T w M.initial (fun _ => .empty))) := by
    simp only [prepAct]
    rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega)]
  rw [lawR_det H M T w N _ 1 _ _ [] 0 _ none _ (fun bit => by simp only [machine]; rw [hact])]
  simp only [wr_mv1, pos_mv1, moveInputPos_zero, Option.toList_none, List.append_nil, wr_none]
  unfold embA
  simp only [MultiTapeMachine.initialConfig, Cfg.init, Option.map_some]
  congr 2
  · funext t
    by_cases ht : t = .clock
    · subst ht; simp [prepF, frameF]
    · rw [Function.update_of_ne ht]
      rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepF, frameF]
      rw [List.take_of_length_le (show w.length ≤ 2 * w.length + T by omega)]
  · funext t
    by_cases ht : t = .clock
    · subst ht; simp [prepP, frameP]; ring
    · rw [Function.update_of_ne ht]
      rcases t with _ | _ | _ | _ | _ | _ <;> simp_all [prepP, frameP]
      omega

/-- **The preparation** reaches the simulation of the initial configuration. -/
theorem lawR_prep (N : ℕ) :
    lawR H M T w (2 * w.length + T + 1 + N) ((machine H M T w).initialConfig x) =
      lawR H M T w N (embA (m := m) H T w (M.initialConfig x) (fun _ => .empty) w T) := by
  have hinit : (machine H M T w).initialConfig x =
      mkR (some (.inl ⟨0, by omega⟩)) 1 (prepF w 0) (prepP w 0) [] := by
    refine Config.ext ?_ rfl
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp only [MultiTapeMachine.initialConfig, Cfg.init, mkR]
      cases kind i <;> simp [prepF]
    · funext i
      simp only [MultiTapeMachine.initialConfig, Cfg.init, mkR]
      cases kind i <;> simp [prepP]
  have key : ∀ k i (hi : i + k = 2 * w.length + T), lawR H M T w (k + 1 + N)
      (mkR (some (.inl ⟨i, by omega⟩)) 1 (prepF w i) (prepP w i) []) =
      lawR H M T w N (embA (m := m) H T w (M.initialConfig x) (fun _ => .empty) w T) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      obtain rfl : i = 2 * w.length + T := by omega
      rw [Nat.zero_add, Nat.add_comm, lawR_prep_last]
    | succ k ih =>
      intro i hi
      rw [show k + 1 + 1 + N = (k + 1 + N) + 1 by omega, lawR_prep_step H M T w i (by omega)]
      exact ih (i + 1) (by omega)
  rw [hinit, show 2 * w.length + T + 1 + N = (2 * w.length + T) + 1 + N by omega]
  exact key _ 0 (by omega)

end SigabaNeo.Inline
