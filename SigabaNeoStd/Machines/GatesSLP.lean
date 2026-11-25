import SigabaNeoStd.Machines.Gates
import SigabaNeoStd.Lattices.Homomorphic.BoolBuild

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

/-! ### From gate lists back to programs -/

/-- The wire of an index. -/
def ofIdx (n : ℕ) (i : ℕ) : Wire (Fin n) :=
  if i = 0 then .one else if h : i - 1 < n then .input ⟨i - 1, h⟩ else .gate (i - 1 - n)

theorem wireIdx_ofIdx (n i : ℕ) : wireIdx n (ofIdx n i) = i := by
  unfold ofIdx
  split_ifs with h0 h1
  · simp [wireIdx, h0]
  · simp [wireIdx]; omega
  · simp [wireIdx]; omega

/-- A gate list as a program. -/
def fromGates (n : ℕ) (gs : GateList) : SLP (Fin n) :=
  gs.map fun g => ⟨ofIdx n g.1, ofIdx n g.2⟩

theorem toGates_fromGates (n : ℕ) (gs : GateList) : toGates n (fromGates n gs) = gs := by
  simp [toGates, fromGates, wireIdx_ofIdx, Function.comp_def]

/-- **The last gate**: a gate list evaluates to the value of the last gate of its program. -/
theorem evalGates_last {n : ℕ} (x : Fin n → Bool) (p : SLP (Fin n)) (g : Gate (Fin n)) :
    evalGates (List.ofFn x, toGates n (p ++ [g])) = SLP.bv x (p ++ [g]) (.gate p.length) := by
  set r := SLP.run x true (fun a b => !(a && b)) p []
  have e1 : evalGates (List.ofFn x, toGates n (p ++ [g])) =
      !(SLP.wireVal x true r g.a && SLP.wireVal x true r g.b) := by
    simp only [evalGates, toGates, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h := fst_foldl_estep_toGates x p [] true
    simp only [toGates, List.append_nil, List.cons_append] at h
    rw [estep]
    dsimp only
    rw [h]
    have ha := getD_wireIdx x r g.a
    have hb := getD_wireIdx x r g.b
    simp only [List.cons_append] at ha hb
    rw [ha, hb]
  have hlen : r.length = p.length := SLP.length_values x true _ p
  have e2 : SLP.bv x (p ++ [g]) (.gate p.length) =
      !(SLP.wireVal x true r g.a && SLP.wireVal x true r g.b) := by
    show (SLP.run x true (fun a b => !(a && b)) (p ++ [g]) []).getD p.length true = _
    rw [SLP.run_append]
    show (r ++ [!(SLP.wireVal x true r g.a && SLP.wireVal x true r g.b)]).getD p.length true = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
      List.getElem_append_right (by rw [hlen])]
    simp only [hlen, Nat.sub_self, List.getElem_singleton]
  rw [e1, e2]

/-- The predicate of a nonempty gate list: its program and its last gate. -/
def predOf (n : ℕ) (gs : GateList) : SLP (Fin n) × Wire (Fin n) :=
  (fromGates n gs, .gate (gs.length - 1))

/-- **A nonempty gate list evaluates to its predicate.** -/
theorem evalGates_predOf {n : ℕ} (x : Fin n → Bool) (gs : GateList) (hgs : gs ≠ []) :
    evalGates (List.ofFn x, gs) = SLP.evalBool x (predOf n gs).1 (predOf n gs).2 := by
  obtain ⟨gs', g, rfl⟩ := List.eq_nil_or_concat gs |>.resolve_left hgs
  have h := evalGates_last x (fromGates n gs') ⟨ofIdx n g.1, ofIdx n g.2⟩
  have hf : fromGates n gs' ++ [⟨ofIdx n g.1, ofIdx n g.2⟩] = fromGates n (gs' ++ [g]) := by
    simp [fromGates]
  rw [hf, toGates_fromGates] at h
  rw [List.concat_eq_append, h]
  simp [predOf, fromGates, SLP.bv]

end SigabaNeo
