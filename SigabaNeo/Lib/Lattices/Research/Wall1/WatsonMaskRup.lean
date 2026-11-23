import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonMaskResolution

/-! Reverse unit propagation on signed bit masks. Each 32-bit hint packs the index of an
earlier clause and a seven-bit literal code. Code 127 marks the final conflict. -/

namespace SigabaNeo.Wall1.Watson.MaskResolution

def propagate (bank : ℕ → Clause) (stop : ℕ) : ℕ → ℕ → Clause → Bool
  | 0, _, _ => false
  | fuel+1, hints, acc =>
    let token := hints % 2^32
    let j := token / 128
    let code := token % 128
    let h := bank j
    decide (j < stop) &&
      if code == 127 then subset h.pos acc.pos && subset h.neg acc.neg
      else
        let bit := code % 64
        let rest := hints / 2^32
        if code < 64 then
          let next := Clause.mk acc.pos (acc.neg ||| 2^bit)
          valid h next acc bit && propagate bank stop fuel rest next
        else
          let next := Clause.mk (acc.pos ||| 2^bit) acc.neg
          valid next h acc bit && propagate bank stop fuel rest next

private theorem propagate_sound {m : ℕ} (b : Fin m → Bool) (bank : ℕ → Clause) (stop : ℕ)
    (prior : ∀ j < stop, (bank j).Sat b) (fuel hints : ℕ) (acc : Clause)
    (ok : propagate bank stop fuel hints acc) : acc.Sat b := by
  induction fuel generalizing hints acc with
  | zero => simp [propagate] at ok
  | succ t ih =>
    simp only [propagate, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨before, good⟩ := ok
    have hs := prior _ before
    split at good
    · simp only [Bool.and_eq_true] at good
      obtain ⟨i,hi | hi⟩ := hs
      · exact ⟨i, Or.inl ⟨subset_bit good.1 hi.1, hi.2⟩⟩
      · exact ⟨i, Or.inr ⟨subset_bit good.2 hi.1, hi.2⟩⟩
    · split at good
      · simp only [Bool.and_eq_true] at good
        obtain ⟨v,rec⟩ := good
        exact resolve b v hs (ih _ _ rec)
      · simp only [Bool.and_eq_true] at good
        obtain ⟨v,rec⟩ := good
        exact resolve b v (ih _ _ rec) hs

def rupCheck (bank : ℕ → Clause) (hints : ℕ → ℕ) (start i : ℕ) : Bool :=
  propagate bank (start+i) 64 (hints i) (bank (start+i))

theorem refuteRup {m : ℕ} (b : Fin m → Bool) (bank : ℕ → Clause) (hints : ℕ → ℕ)
    (start length : ℕ) (checks : ∀ i : Fin length, rupCheck bank hints start i)
    (last : bank (start+length-1) = ⟨0,0⟩) (hn : 0 < start+length) :
    ¬ ∀ i : Fin start, (bank i).Sat b := by
  intro init
  have sat (i : ℕ) (hi : i < start+length) : (bank i).Sat b := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases low : i < start
      · exact init ⟨_,low⟩
      let j := i-start
      have eq : start+j=i := by dsimp [j]; omega
      have h := checks ⟨j,by omega⟩
      change propagate bank (start+j) 64 (hints j) (bank (start+j)) at h
      rw [eq] at h
      exact propagate_sound b bank i (fun l hl ↦ ih l hl (by omega)) _ _ _ h
  obtain ⟨i,hi⟩ := last ▸ sat (start+length-1) (by omega)
  simp at hi

end SigabaNeo.Wall1.Watson.MaskResolution
