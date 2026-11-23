import Mathlib.Data.Nat.Bitwise

/-! A kernel-checkable binary resolution certificate for contact support masks. -/
namespace SigabaNeo.Wall1.Watson.MaskResolution

structure Clause where
  pos : Nat
  neg : Nat
  deriving Inhabited

structure Step where
  left : Nat
  right : Nat
  bit : Nat
  deriving Inhabited

def subset (a b : ℕ) : Bool := (a &&& b) == a

theorem subset_bit {a b : ℕ} (h : subset a b) {i : ℕ} (hi : a.testBit i) : b.testBit i := by
  have e := congrArg (fun x : ℕ ↦ x.testBit i) (beq_iff_eq.mp h)
  simpa [Nat.testBit_and,hi] using e

def Clause.Sat {m : ℕ} (c : Clause) (s : Fin m → Bool) : Prop :=
  ∃ i : Fin m, (c.pos.testBit i ∧ s i = true) ∨ (c.neg.testBit i ∧ s i = false)

def valid (a b c : Clause) (bit : ℕ) : Bool :=
  subset a.pos (c.pos ||| 2^bit) && subset a.neg c.neg &&
  subset b.pos c.pos && subset b.neg (c.neg ||| 2^bit)

theorem resolve {m : ℕ} (s : Fin m → Bool) {a b c : Clause} {bit : ℕ}
    (v : valid a b c bit) (ha : a.Sat s) (hb : b.Sat s) : c.Sat s := by
  simp only [valid,Bool.and_eq_true] at v
  obtain ⟨i,⟨ai,st⟩ | ⟨ai,st⟩⟩ := ha
  · have h := subset_bit v.1.1.1 ai
    rw [Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨i,Or.inl ⟨h,st⟩⟩
    have ie : bit = i.val := by simpa [Nat.testBit_two_pow] using h
    obtain ⟨j,⟨bj,sj⟩ | ⟨bj,sj⟩⟩ := hb
    · exact ⟨j,Or.inl ⟨subset_bit v.1.2 bj,sj⟩⟩
    have h' := subset_bit v.2 bj
    rw [Nat.testBit_or,Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨j,Or.inr ⟨h',sj⟩⟩
    have je : bit = j.val := by simpa [Nat.testBit_two_pow] using h'
    have eq : i = j := Fin.ext (ie.symm.trans je)
    simp [← eq,st] at sj
  · exact ⟨i,Or.inr ⟨subset_bit v.1.1.2 ai,st⟩⟩

def check (bank : ℕ → Clause) (start : ℕ) (proof : ℕ → Step) (i : ℕ) : Bool :=
  let a := proof i
  decide (a.left < start+i ∧ a.right < start+i) &&
    valid (bank (a.left)) (bank (a.right))
      (bank (start+i)) a.bit

theorem splitCheck {P : ℕ → Prop} (a n r : ℕ)
    (left : ∀ j : Fin n, P (a+j.val))
    (right : ∀ j : Fin r, P ((a+n)+j.val)) : ∀ j : Fin (n+r), P (a+j.val) := by
  intro j
  by_cases h : j.val < n
  · exact left ⟨j.val,h⟩
  · have h' := right ⟨j.val-n,by omega⟩
    simpa only [show a+n+(j.val-n) = a+j.val by omega] using h'

/-- An empty terminal clause refutes joint satisfiability of the input clauses. -/
theorem refute {m : ℕ} (s : Fin m → Bool) (bank : ℕ → Clause) (start : ℕ) (proof : ℕ → Step)
    (length : ℕ) (ok : ∀ i : Fin length, check bank start proof i)
    (last : (bank (start+length-1)) = ⟨0,0⟩) (hn : 0 < start+length) :
    ¬ ∀ i : Fin start, (bank (i.val)).Sat s := by
  intro init
  have sat (i : ℕ) (hi : i < start+length) : (bank (i)).Sat s := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases low : i < start
      · exact init ⟨_,low⟩
      let j := i - start
      have eq : start+j=i := by dsimp [j]; omega
      have h := ok ⟨j,by omega⟩
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      rw [eq] at h
      exact resolve s h.2 (ih _ h.1.1 (by omega)) (ih _ h.1.2 (by omega))
  obtain ⟨i,h⟩ := last ▸ sat (start+length-1) (by omega)
  simp at h

end SigabaNeo.Wall1.Watson.MaskResolution

#print axioms SigabaNeo.Wall1.Watson.MaskResolution.refute
