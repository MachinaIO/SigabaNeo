import SigabaNeoStd.Machines.Inline.Defs

/-!
# Inlining an oracle handler: deterministic phases

The run law of `Inline.machine` (`lawR`) through its deterministic phases: one coin-independent
step at a named configuration (`lawR_det`, `lawR_q`), the scans of the query phases
(`lawR_scanRight`, `lawR_eraseLeft`, `lawR_seekR`, `lawR_seekL`, `lawR_rewind`).
-/

namespace SigabaNeo.Inline

open Cslib Turing MultiTapeMachine

variable {kA ops m : ℕ} {SA : Type} (H : Fin ops → Routine (m + 3))
  (M : MultiTapePTM kA Bool SA (Fin ops)) (T : ℕ) (w : List Bool) {x : List Bool}

/-- The run law of the inlined machine (it has no channels). -/
noncomputable def lawR (N : ℕ) (cfg : Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x) :
    PMF (Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x × Unit) :=
  ProbOracleComp.runWith (fun e : Fin 0 × List Bool => e.1.elim0)
    ((machine H M T w).runOracleConfigFrom N cfg) ()

/-- The symbols under the work heads of a named configuration. -/
theorem mkR_workTapeSymbols {S : Type} (q : Option S) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool) :
    (mkR q ip F P out).tapes.workTapeSymbols = fun i => F (kind i) (P (kind i)) := rfl

/-- One coin-independent step from a named configuration. -/
theorem lawR_det (N : ℕ) (q : RState SA H T w) (ip : Fin (x.length + 2))
    (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
    (d : SignType) (W : Tape kA ops m → Option (Option Bool) × SignType) (o : Option Bool)
    (q' : Option (RState SA H T w))
    (htr : ∀ bit, (machine H M T w).tr q (mkR (some q) ip F P out).tapes.inputSymbol
      (fun i => F (kind i) (P (kind i))) (fun e => e.elim0) bit = stepR (mkAct d W o q')) :
    lawR H M T w (N + 1) (mkR (some q) ip F P out) =
      lawR H M T w N (mkR q' (moveInputPos ip d) (fun t => wr (F t) (P t) (W t).1)
        (fun t => P t + (W t).2) (out ++ o.toList)) := by
  unfold lawR
  rw [law_succ_det _ _ N _ () rfl (action := mkAct d W o q') (symbol := fun _ => none)
    (move := fun _ => 0)]
  · rw [step_mkR]
  · intro bit
    have hans : (mkR (some q) ip F P out).answerSymbols = fun e => e.elim0 :=
      funext fun e => e.elim0
    rw [hans]
    exact htr bit

/-- The tapes after acting on one tape. -/
theorem wr_mv1 (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ)
    (t : Tape kA ops m) (b : Option (Option Bool)) (d : SignType) :
    (fun t' => wr (F t') (P t') (mv1 t b d t').1) = Function.update F t (wr (F t) (P t) b) := by
  funext t'
  by_cases h : t' = t
  · subst h; simp [mv1]
  · simp [mv1, h]

theorem pos_mv1 (P : Tape kA ops m → ℤ) (t : Tape kA ops m) (b : Option (Option Bool))
    (d : SignType) :
    (fun t' => P t' + ((mv1 t b d t').2 : ℤ)) = Function.update P t (P t + d) := by
  funext t'
  by_cases h : t' = t
  · subst h; simp [mv1]
  · simp [mv1, h]

/-- One step of a query phase acting on one tape. -/
theorem lawR_q (N : ℕ) (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ph : QStep)
    (ip : Fin (x.length + 2)) (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ)
    (out : List Bool) (t : Tape kA ops m) (b : Option (Option Bool)) (d : SignType)
    (next : Option (RState SA H T w))
    (h : qAct H T w q fl o ph (fun i => F (kind i) (P (kind i))) = mkAct 0 (mv1 t b d) none next) :
    lawR H M T w (N + 1) (mkR (some (qS H T w q fl o ph)) ip F P out) =
      lawR H M T w N (mkR next ip (Function.update F t (wr (F t) (P t) b))
        (Function.update P t (P t + d)) out) := by
  rw [lawR_det H M T w N _ ip F P out 0 (mv1 t b d) none next (fun bit => by
    simp only [machine, qS]; rw [h])]
  rw [wr_mv1, pos_mv1]
  simp

section Scans

variable (q : SA) (fl : Fin ops → AFlag) (o : Fin ops) (ip : Fin (x.length + 2))
  (F : Tape kA ops m → ℤ → Option Bool) (P : Tape kA ops m → ℤ) (out : List Bool)
  (t : Tape kA ops m)

/-- The configuration of a query phase with tape `t` holding `f`, its head at `p`. -/
abbrev qCfg (ph : QStep) (f : ℤ → Option Bool) (p : ℤ) :
    Config (nTapes kA ops m) Bool (RState SA H T w) (Fin 0) x :=
  mkR (some (qS H T w q fl o ph)) ip (Function.update F t f) (Function.update P t p) out

theorem symbols_update (f : ℤ → Option Bool) (p : ℤ) :
    (fun i => (Function.update F t f) (kind i) ((Function.update P t p) (kind i)))
      t.idx = f p := by simp

/-- **Scan right** over a word to its end, then step back onto its last cell. -/
theorem lawR_scanRight (ph : QStep) (next : Option (RState SA H T w))
    (hmove : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx ≠ none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none 1) none (some (qS H T w q fl o ph)))
    (hend : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx = none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none (-1)) none next)
    (a : List Bool) (N j : ℕ) (hj : j ≤ a.length) :
    lawR H M T w (N + (a.length - j) + 1)
        (qCfg H T w q fl o ip F P out t ph (tapeOfList a) j) =
      lawR H M T w N (mkR next ip (Function.update F t (tapeOfList a))
        (Function.update P t ((a.length : ℤ) - 1)) out) := by
  induction h : a.length - j generalizing j with
  | zero =>
    have hj' : j = a.length := by omega
    subst hj'
    rw [Nat.add_zero, lawR_q H M T w N q fl o ph ip _ _ out t none (-1) next
      (hend _ (by simp))]
    simp [Function.update_idem, sub_eq_add_neg]
  | succ n ih =>
    rw [show N + (n + 1) + 1 = (N + n + 1) + 1 by omega,
      lawR_q H M T w (N + n + 1) q fl o ph ip _ _ out t none 1 _
        (hmove _ (by simp; omega))]
    simp only [Function.update_self, Function.update_idem, wr_none, SignType.coe_one]
    have := ih (j + 1) (by omega) (by omega)
    push_cast at this
    exact this

/-- **Erase leftwards** a word whose last cell is under the head, then step back to the start. -/
theorem lawR_eraseLeft (ph : QStep) (next : (Fin (nTapes kA ops m) → Option Bool) →
      Option (RState SA H T w))
    (hmove : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx ≠ none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t (some none) (-1)) none (some (qS H T w q fl o ph)))
    (hend : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx = none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none 1) none (next work))
    (a : List Bool) (N j : ℕ) (hj : j ≤ a.length) :
    lawR H M T w (N + j + 1)
        (qCfg H T w q fl o ip F P out t ph (tapeOfList (a.take j)) ((j : ℤ) - 1)) =
      lawR H M T w N (mkR (next (fun i => (Function.update F t (fun _ => none)) (kind i)
          ((Function.update P t (-1)) (kind i)))) ip
        (Function.update F t (fun _ => none)) (Function.update P t 0) out) := by
  induction j with
  | zero =>
    simp only [List.take_zero, tapeOfList_nil, Nat.cast_zero, zero_sub, Nat.add_zero]
    rw [lawR_q H M T w N q fl o ph ip _ _ out t none 1 _ (hend _ (by simp))]
    simp [Function.update_idem]
  | succ j ih =>
    have hlt : j < a.length := by omega
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawR_q H M T w (N + j + 1) q fl o ph ip _ _ out t (some none) (-1) _
        (hmove _ (by
          simp only [symbols_update, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [tapeOfList_ofNat]; simp [hlt]))]
    simp only [Function.update_self, Function.update_idem, wr]
    have htake : Function.update (tapeOfList (a.take (j + 1))) ((j + 1 : ℕ) - 1 : ℤ) none =
        tapeOfList (a.take j) := by
      funext z
      by_cases hz : z = j
      · subst hz; simp [tapeOfList_ofNat]
      · rw [Function.update_of_ne (by push_cast; simpa using hz)]
        rcases z with z | z
        · change tapeOfList _ (z : ℤ) = tapeOfList _ (z : ℤ)
          simp only [tapeOfList_ofNat, List.getElem?_take]
          have : z ≠ j := fun h => hz (by simp [h])
          by_cases hzj : z < j
          · simp [hzj, show z < j + 1 by omega]
          · simp [hzj, show ¬ z < j + 1 by omega]
        · rfl
    push_cast at htake ⊢
    rw [htake]
    convert ih (by omega) using 4
    simp; ring

/-- **Scan left** over a word to the blank before it, then step back onto its start. -/
theorem lawR_scanLeft (ph : QStep) (next : Option (RState SA H T w))
    (hmove : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx ≠ none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none (-1)) none (some (qS H T w q fl o ph)))
    (hend : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx = none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none 1) none next)
    (a : List Bool) (N j : ℕ) (hj : j ≤ a.length) :
    lawR H M T w (N + j + 1)
        (qCfg H T w q fl o ip F P out t ph (tapeOfList a) ((j : ℤ) - 1)) =
      lawR H M T w N (mkR next ip (Function.update F t (tapeOfList a))
        (Function.update P t 0) out) := by
  induction j with
  | zero =>
    rw [Nat.add_zero, lawR_q H M T w N q fl o ph ip _ _ out t none 1 next
      (hend _ (by simp; rfl))]
    simp [Function.update_idem]
  | succ j ih =>
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawR_q H M T w (N + j + 1) q fl o ph ip _ _ out t none (-1) _
        (hmove _ (by
          simp only [symbols_update]; push_cast
          rw [show (j : ℤ) + 1 - 1 = (j : ℕ) by ring, tapeOfList_ofNat]; simp; omega))]
    simp only [Function.update_self, Function.update_idem, wr_none]
    convert ih (by omega) using 4
    push_cast; simp; ring

/-- **Seek right** from the left of a nonempty word to its first cell, and step past it. -/
theorem lawR_seekR (ph : QStep) (next : Option (RState SA H T w))
    (hmove : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx = none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none 1) none (some (qS H T w q fl o ph)))
    (hend : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx ≠ none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none 1) none next)
    (a : List Bool) (ha : a ≠ []) (N j : ℕ) :
    lawR H M T w (N + j + 1)
        (qCfg H T w q fl o ip F P out t ph (tapeOfList a) (-(j : ℤ))) =
      lawR H M T w N (mkR next ip (Function.update F t (tapeOfList a))
        (Function.update P t 1) out) := by
  induction j with
  | zero =>
    rw [Nat.add_zero, lawR_q H M T w N q fl o ph ip _ _ out t none 1 next
      (hend _ (by
        simp only [symbols_update, Nat.cast_zero, neg_zero]
        rw [tapeOfList_zero]; cases a <;> simp_all))]
    simp [Function.update_idem]
  | succ j ih =>
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawR_q H M T w (N + j + 1) q fl o ph ip _ _ out t none 1 _
        (hmove _ (by
          simp only [symbols_update]
          rw [tapeOfList_eq_none_iff]; left; push_cast; omega))]
    simp only [Function.update_self, Function.update_idem, wr_none]
    convert ih using 4
    push_cast; simp

/-- **Seek left** from the right of a nonempty word to its last cell, erase it and step left. -/
theorem lawR_seekL (ph : QStep) (next : Option (RState SA H T w))
    (hmove : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx = none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t none (-1)) none (some (qS H T w q fl o ph)))
    (hend : ∀ work : Fin (nTapes kA ops m) → Option Bool, work t.idx ≠ none →
      qAct H T w q fl o ph work = mkAct 0 (mv1 t (some none) (-1)) none next)
    (a : List Bool) (ha : a ≠ []) (N j : ℕ) :
    lawR H M T w (N + j + 1)
        (qCfg H T w q fl o ip F P out t ph (tapeOfList a) ((a.length : ℤ) - 1 + j)) =
      lawR H M T w N (mkR next ip (Function.update F t (tapeOfList (a.take (a.length - 1))))
        (Function.update P t ((a.length : ℤ) - 2)) out) := by
  have hlen : 0 < a.length := List.length_pos_iff.mpr ha
  induction j with
  | zero =>
    rw [Nat.add_zero, lawR_q H M T w N q fl o ph ip _ _ out t (some none) (-1) next
      (hend _ (by
        simp only [symbols_update, Nat.cast_zero, add_zero]
        rw [show (a.length : ℤ) - 1 = ((a.length - 1 : ℕ) : ℤ) by omega, tapeOfList_ofNat]
        simp; omega))]
    simp only [Function.update_self, Function.update_idem, wr, Nat.cast_zero, add_zero]
    congr 4
    · funext z
      by_cases hz : z = (a.length : ℤ) - 1
      · subst hz
        rw [Function.update_self, show (a.length : ℤ) - 1 = ((a.length - 1 : ℕ) : ℤ) by omega,
          tapeOfList_ofNat]
        simp
      · rw [Function.update_of_ne hz]
        rcases z with z | z
        · change tapeOfList _ (z : ℤ) = tapeOfList _ (z : ℤ)
          simp only [tapeOfList_ofNat, List.getElem?_take]
          by_cases hzl : z < a.length - 1
          · simp [hzl]
          · simp only [hzl, ite_false]
            have : z ≠ a.length - 1 := fun h => hz (by rw [h, Int.ofNat_eq_natCast]; omega)
            rw [List.getElem?_eq_none]
            omega
        · rfl
    · simp; ring
  | succ j ih =>
    rw [show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      lawR_q H M T w (N + j + 1) q fl o ph ip _ _ out t none (-1) _
        (hmove _ (by
          simp only [symbols_update]
          rw [tapeOfList_eq_none_iff]; right; push_cast; omega))]
    simp only [Function.update_self, Function.update_idem, wr_none]
    convert ih using 4
    push_cast; simp; ring

end Scans

end SigabaNeo.Inline
