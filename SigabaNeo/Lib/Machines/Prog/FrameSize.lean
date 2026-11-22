import SigabaNeo.Lib.Machines.Prog.Frame

/-!
# The state count of a framed program

`XProg.size p` is the number of states of the compiled machine of the framed program `p`
(`card_state`): a frame adds no state, so it is `Prog.size` on the leaves, summed as for `Prog`.
`size_liftP`-style lemmas follow from `size_frame`.
-/

namespace SigabaNeo.Tape

namespace XProg

/-- The number of states of the compiled machine of a framed program. -/
def size : {k : ℕ} → XProg k → ℕ
  | _, prog p => p.size
  | _, frame _ p => size p
  | _, seq p q => size p + size q
  | _, ifBlank _ p q => size p + size q + 1
  | _, ifBit _ p q => size p + size q + 1
  | _, loop _ body => size body + 39

@[simp] theorem size_prog {k : ℕ} (p : Prog k) : (prog p).size = p.size := rfl
@[simp] theorem size_frame {k m : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) :
    (frame e p).size = p.size := rfl
@[simp] theorem size_seq {k : ℕ} (p q : XProg k) : (seq p q).size = p.size + q.size := rfl
@[simp] theorem size_ifBlank {k : ℕ} (i : Fin k) (p q : XProg k) :
    (ifBlank i p q).size = p.size + q.size + 1 := rfl
@[simp] theorem size_ifBit {k : ℕ} (i : Fin k) (p q : XProg k) :
    (ifBit i p q).size = p.size + q.size + 1 := rfl
@[simp] theorem size_loop {k : ℕ} (i : Fin k) (body : XProg k) :
    (loop i body).size = body.size + 39 := rfl

/-- **The state count** of the compiled machine of a framed program. -/
theorem card_state : {k : ℕ} → (p : XProg k) → Fintype.card p.State = p.size
  | _, prog p => Prog.card_state p
  | _, frame _ p => card_state p
  | _, seq p q => by
    rw [show Fintype.card (seq p q).State = Fintype.card (p.State ⊕ q.State) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_sum, card_state p, card_state q]
    rfl
  | _, ifBlank _ p q => by
    rw [show Fintype.card (ifBlank _ p q).State = Fintype.card (Option (q.State ⊕ p.State)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, card_state p,
      card_state q, size]
    ring
  | _, ifBit _ p q => by
    rw [show Fintype.card (ifBit _ p q).State = Fintype.card (Option (p.State ⊕ q.State)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, card_state p,
      card_state q, size]
  | _, loop i body => by
    rw [show Fintype.card (loop i body).State =
        Fintype.card (Option (((CQ (tailSpec i).e ⊕ body.State) ⊕ Unit) ⊕ Unit)) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_sum, card_CQ, Fintype.card_unit, card_state body, size]
    simp only [tailSpec, bwdSpec]
    ring

end XProg

end SigabaNeo.Tape
