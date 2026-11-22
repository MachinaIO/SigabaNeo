import SigabaNeo.Lib.Machines.Inline.Steps

/-!
# Inlining an oracle handler: the deterministic query phases

* `lawR_clean`: erase the old answer of the channel and return its head to the start, within
  `|p| + 2 |a| + 3` steps (`p` its head, `a` the answer);
* `lawR_rewind`: rewind the query buffer, `|b| + 2` steps;
* `lawR_eraseQuery`: erase the query after the handler, `2 |b| + 2` steps, and resume the
  simulation with the flag of the channel set from its new answer.
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

section

variable (q : SA) (fl : Fin ops → AFlag) (o : Fin ops)
  (work : Fin (nTapes kA ops m) → Option Bool)

theorem noop_eq (t : Tape kA ops m) : (noop : Tape kA ops m → _) = mv1 t none 0 := by
  funext t'; simp [noop, mv1]

/-! Transition facts of the query phases. -/

theorem qAct_cleanStart_empty (h : fl o = .empty) :
    qAct H T w q fl o .cleanStart work =
      mkAct 0 (mv1 (.ans o) none 0) none (some (qS H T w q fl o .rewQ0)) := by
  simp [qAct, h, noop_eq (.ans o)]

theorem qAct_cleanStart_in (h : fl o ≠ .empty) (ha : work (Tape.ans o).idx ≠ none) :
    qAct H T w q fl o .cleanStart work =
      mkAct 0 (mv1 (.ans o) none 1) none (some (qS H T w q fl o .toEnd)) := by
  simp [qAct, h, ha]

theorem qAct_cleanStart_left (h : fl o = .left) (ha : work (Tape.ans o).idx = none) :
    qAct H T w q fl o .cleanStart work =
      mkAct 0 (mv1 (.ans o) none 1) none (some (qS H T w q fl o .seekR)) := by
  simp [qAct, h, ha]

theorem qAct_cleanStart_right (h : fl o = .right) (ha : work (Tape.ans o).idx = none) :
    qAct H T w q fl o .cleanStart work =
      mkAct 0 (mv1 (.ans o) none (-1)) none (some (qS H T w q fl o .seekL)) := by
  simp [qAct, h, ha]

end

/-- The answer tape and its head, as named. -/
theorem update_self_eq {α : Type} (F : Tape kA ops m → α) (t : Tape kA ops m) :
    Function.update F t (F t) = F := Function.update_eq_self t F

/-- **Erase the old answer** of channel `o` and return its head to the start. -/
theorem lawR_clean (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (a : List Bool) (p : ℤ) (hF : F (.ans o) = tapeOfList a)
    (hP : P (.ans o) = if a = [] then 0 else p) (hfl : fl o = .empty ↔ a = [])
    (hside : a ≠ [] → tapeOfList a p = none → (fl o = .left ↔ p < 0)) :
    ∃ j ≤ (if a = [] then 0 else p.natAbs) + 2 * a.length + 3, ∀ N,
      lawR H M T w (j + N) (mkR (some (qS H T w q fl o .cleanStart)) ip F P out) =
        lawR H M T w N (mkR (some (qS H T w q fl o .rewQ0)) ip
          (Function.update F (.ans o) (fun _ => none)) (Function.update P (.ans o) 0) out) := by
  by_cases ha : a = []
  · subst ha
    have he : fl o = .empty := hfl.mpr rfl
    refine ⟨1, by simp, fun N => ?_⟩
    rw [Nat.add_comm, lawR_q H M T w N q fl o .cleanStart ip F P out (.ans o) none 0 _
      (qAct_cleanStart_empty H T w q fl o _ he)]
    simp [hF, hP]
  have hne : fl o ≠ .empty := fun h => ha (hfl.mp h)
  have hlen : 0 < a.length := List.length_pos_iff.mpr ha
  simp only [ha, ite_false] at hP ⊢
  -- the erase-left phase, from the last cell
  have herase : ∀ N j, j ≤ a.length → lawR H M T w (N + j + 1)
      (mkR (some (qS H T w q fl o .eraseL)) ip (Function.update F (.ans o) (tapeOfList (a.take j)))
        (Function.update P (.ans o) ((j : ℤ) - 1)) out) =
      lawR H M T w N (mkR (some (qS H T w q fl o .rewQ0)) ip
          (Function.update F (.ans o) (fun _ => none)) (Function.update P (.ans o) 0) out) :=
    fun N j hj => lawR_eraseLeft H M T w q fl o ip F P out (.ans o) .eraseL
      (fun _ => some (qS H T w q fl o .rewQ0))
      (fun work h => by simp [qAct, h]) (fun work h => by simp [qAct, h]) a N j hj
  -- the scan to the end, then erase
  have hscan : ∀ N j, j ≤ a.length → lawR H M T w (N + a.length + 1 + (a.length - j) + 1)
      (mkR (some (qS H T w q fl o .toEnd)) ip (Function.update F (.ans o) (tapeOfList a))
        (Function.update P (.ans o) (j : ℤ)) out) =
      lawR H M T w N (mkR (some (qS H T w q fl o .rewQ0)) ip
          (Function.update F (.ans o) (fun _ => none)) (Function.update P (.ans o) 0) out) := by
    intro N j hj
    rw [lawR_scanRight H M T w q fl o ip F P out (.ans o) .toEnd
      (some (qS H T w q fl o .eraseL)) (fun work h => by simp [qAct, h])
      (fun work h => by simp [qAct, h]) a _ j hj]
    have := herase N a.length le_rfl
    rw [List.take_length] at this
    rw [← this]
  by_cases hin : tapeOfList a p = none
  · have hsd := hside ha hin
    rcases (tapeOfList_eq_none_iff a p).mp hin with hlt | hge
    · -- left of the answer
      have hl : fl o = .left := hsd.mpr hlt
      refine ⟨1 + ((-p - 1).toNat + 1) + (a.length - 1 + 1) + (a.length + 1), by omega,
        fun N => ?_⟩
      rw [show 1 + ((-p - 1).toNat + 1) + (a.length - 1 + 1) + (a.length + 1) + N =
        ((N + a.length + 1 + (a.length - 1) + 1) + (-p - 1).toNat + 1) + 1 by omega]
      rw [lawR_q H M T w _ q fl o .cleanStart ip F P out (.ans o) none 1 _
        (qAct_cleanStart_left H T w q fl o _ hl (by simp [hF, hP, hin]))]
      simp only [wr_none, hF, hP]
      have hseek := lawR_seekR H M T w q fl o ip F P out (.ans o) .seekR
        (some (qS H T w q fl o .toEnd)) (fun work h => by simp [qAct, h])
        (fun work h => by simp [qAct, h]) a ha (N + a.length + 1 + (a.length - 1) + 1)
        (-p - 1).toNat
      rw [show (-(((-p - 1).toNat : ℕ) : ℤ)) = p + (1 : SignType) by simp; omega] at hseek
      rw [hseek]
      exact_mod_cast hscan N 1 (by omega)
    · -- right of the answer
      have hr : fl o = .right := by
        have : ¬ p < 0 := by omega
        cases h : fl o <;> simp_all
      refine ⟨1 + ((p - a.length).toNat + 1) + (a.length - 1 + 1), by omega, fun N => ?_⟩
      rw [show 1 + ((p - a.length).toNat + 1) + (a.length - 1 + 1) + N =
        ((N + (a.length - 1) + 1) + (p - a.length).toNat + 1) + 1 by omega]
      rw [lawR_q H M T w _ q fl o .cleanStart ip F P out (.ans o) none (-1) _
        (qAct_cleanStart_right H T w q fl o _ hr (by simp [hF, hP, hin]))]
      simp only [wr_none, hF, hP]
      have hseek := lawR_seekL H M T w q fl o ip F P out (.ans o) .seekL
        (some (qS H T w q fl o .eraseL)) (fun work h => by simp [qAct, h])
        (fun work h => by simp [qAct, h]) a ha (N + (a.length - 1) + 1) (p - a.length).toNat
      rw [show (a.length : ℤ) - 1 + (((p - a.length).toNat : ℕ) : ℤ) = p + (-1 : SignType) by
        simp; omega] at hseek
      rw [hseek]
      have := herase N (a.length - 1) (by omega)
      rw [show ((a.length - 1 : ℕ) : ℤ) - 1 = (a.length : ℤ) - 2 by omega] at this
      exact this
  · -- on the answer
    have hp : 0 ≤ p ∧ p < a.length := by
      rw [tapeOfList_eq_none_iff] at hin; omega
    refine ⟨1 + ((a.length - (p.toNat + 1)) + 1) + (a.length + 1), by omega, fun N => ?_⟩
    rw [show 1 + ((a.length - (p.toNat + 1)) + 1) + (a.length + 1) + N =
      (N + a.length + 1 + (a.length - (p.toNat + 1)) + 1) + 1 by omega]
    rw [lawR_q H M T w _ q fl o .cleanStart ip F P out (.ans o) none 1 _
      (qAct_cleanStart_in H T w q fl o _ hne (by simp [hF, hP, hin]))]
    simp only [wr_none, hF, hP]
    have := hscan N (p.toNat + 1) (by omega)
    rw [show (((p.toNat + 1 : ℕ)) : ℤ) = p + (1 : SignType) by simp; omega] at this
    exact this

/-- **Rewind the query buffer** of channel `o`, then start the handler. -/
theorem lawR_rewind (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (b : List Bool) (hF : F (.qry o) = tapeOfList b) (hP : P (.qry o) = b.length) (N : ℕ) :
    lawR H M T w (b.length + 2 + N) (mkR (some (qS H T w q fl o .rewQ0)) ip F P out) =
      lawR H M T w N (mkR (some (hS H T w q fl o (H o).machine.initial)) ip F
        (Function.update P (.qry o) 0) out) := by
  rw [show b.length + 2 + N = (N + b.length + 1) + 1 by omega,
    lawR_q H M T w _ q fl o .rewQ0 ip F P out (.qry o) none (-1) (some (qS H T w q fl o .rewQ))
      (by simp [qAct])]
  have hs := lawR_scanLeft H M T w q fl o ip F P out (.qry o) .rewQ
    (some (hS H T w q fl o (H o).machine.initial)) (fun work h => by simp [qAct, h])
    (fun work h => by simp [qAct, h]) b N b.length le_rfl
  rw [← hF, update_self_eq] at hs
  rw [← hs]
  simp [hF, hP, sub_eq_add_neg]

/-- **Erase the query** after the handler, and resume the simulation. -/
theorem lawR_eraseQuery (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (b : List Bool) (hF : F (.qry o) = tapeOfList b) (hP : P (.qry o) = 0) (N : ℕ) :
    lawR H M T w (2 * b.length + 2 + N) (mkR (some (qS H T w q fl o .qToEnd)) ip F P out) =
      lawR H M T w N (mkR (some (simS H T w q (Function.update fl o
          (if F (.ans o) (P (.ans o)) = none then .empty else .right)))) ip
        (Function.update F (.qry o) (fun _ => none)) (Function.update P (.qry o) 0) out) := by
  have hscan := lawR_scanRight H M T w q fl o ip F P out (.qry o) .qToEnd
    (some (qS H T w q fl o .qErase)) (fun work h => by simp [qAct, h])
    (fun work h => by simp [qAct, h]) b (N + b.length + 1) 0 (by omega)
  have herase := lawR_eraseLeft H M T w q fl o ip F P out (.qry o) .qErase
    (fun work => some (simS H T w q (Function.update fl o
      (if work (Tape.ans o).idx = none then .empty else .right))))
    (fun work h => by simp [qAct, h]) (fun work h => by simp [qAct, h]) b N b.length le_rfl
  rw [List.take_length] at herase
  rw [show 2 * b.length + 2 + N = N + b.length + 1 + (b.length - 0) + 1 by omega]
  have h0 : mkR (some (qS H T w q fl o .qToEnd)) ip F P out =
      qCfg H T w q fl o ip F P out (.qry o) .qToEnd (tapeOfList b) ((0 : ℕ) : ℤ) := by
    simp only [qCfg, Nat.cast_zero, ← hF, ← hP, update_self_eq]
  rw [h0, hscan]
  convert herase using 3
  simp

end SigabaNeo.Inline
