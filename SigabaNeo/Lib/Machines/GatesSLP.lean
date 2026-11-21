import SigabaNeo.Lib.Machines.Gates
import SigabaNeo.Lib.Lattices.Homomorphic.BoolBuild

/-!
# Gate lists of straight-line programs

A straight-line program on `n` inputs (`SLP (Fin n)`) as a gate list (`toGates`): the wires are
numbered `1` (index `0`), the inputs (`1 … n`) and then the gates. Its evaluation by `evalGates`
on the bits `List.ofFn x` computes the same values (`fst_foldl_estep_toGates`). `predGates p w`
appends a gate `NAND(w, w)`, so the last gate of the list is the negation of `w`
(`evalGates_predGates`).
-/

namespace SigabaNeo

open Lattices

/-- The index of a wire: `1`, then the inputs, then the gates. -/
def wireIdx (n : ℕ) : Wire (Fin n) → ℕ
  | .one => 0
  | .input i => 1 + i.val
  | .gate m => 1 + n + m

/-- A program as a gate list. -/
def toGates (n : ℕ) (p : SLP (Fin n)) : GateList := p.map fun g => (wireIdx n g.a, wireIdx n g.b)

theorem getD_wireIdx {n : ℕ} (x : Fin n → Bool) (acc : List Bool) (w : Wire (Fin n)) :
    ((true :: List.ofFn x) ++ acc).getD (wireIdx n w) true = SLP.wireVal x true acc w := by
  cases w with
  | one => rfl
  | input i =>
    simp only [wireIdx, SLP.wireVal]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_append_left (by simp; omega)]
    simp [Nat.add_comm 1 i.val]
  | gate m =>
    simp only [wireIdx, SLP.wireVal]
    have h : (true :: List.ofFn x).length = 1 + n := by simp [Nat.add_comm]
    by_cases hm : m < acc.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hm,
        List.getElem_append_right (by rw [h]; omega)]
      simp only [h, Nat.add_sub_cancel_left]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- **The gate list computes the values of the program.** -/
theorem fst_foldl_estep_toGates {n : ℕ} (x : Fin n → Bool) :
    ∀ (p : SLP (Fin n)) (acc : List Bool) (last : Bool),
      ((toGates n p).foldl estep ((true :: List.ofFn x) ++ acc, last)).1 =
        (true :: List.ofFn x) ++ SLP.run x true (fun a b => !(a && b)) p acc
  | [], acc, last => rfl
  | g :: p, acc, last => by
    simp only [toGates, List.map_cons, List.foldl_cons, SLP.run]
    have h := fst_foldl_estep_toGates x p (acc ++ [!(SLP.wireVal x true acc g.a &&
      SLP.wireVal x true acc g.b)])
    rw [← h]
    simp only [estep, getD_wireIdx, List.append_assoc]
    rfl

/-- The predicate of a wire: the program followed by the gate `NAND(w, w)`. -/
def predGates {n : ℕ} (p : SLP (Fin n)) (w : Wire (Fin n)) : GateList :=
  toGates n (p ++ [⟨w, w⟩])

/-- **The last gate of a predicate is the negation of its wire.** -/
theorem evalGates_predGates {n : ℕ} (x : Fin n → Bool) (p : SLP (Fin n)) (w : Wire (Fin n)) :
    evalGates (List.ofFn x, predGates p w) = !SLP.bv x p w := by
  simp only [evalGates, predGates, toGates, List.map_append, List.map_cons, List.map_nil,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h := fst_foldl_estep_toGates x p [] true
  simp only [toGates, List.append_nil] at h
  have h' := h
  simp only [List.cons_append] at h'
  rw [estep]
  dsimp only
  rw [h']
  have := getD_wireIdx x (SLP.run x true (fun a b => !(a && b)) p []) w
  simp only [List.cons_append] at this
  rw [this, Bool.and_self]
  rfl

end SigabaNeo
