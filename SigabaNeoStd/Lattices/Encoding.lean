import SigabaNeoStd.Lattices.Basic

/-!
# Encoding matrices over `Z_q` as bit strings

* `matVals M`: the representatives in `[0, q)` of the entries of `M`, row-major.
* `encEntries W vs`: the numbers `vs`, `W` bits each, low bit first (`bitsOf`).
* `intMod q M`: an integer matrix reduced mod `q`.
-/

namespace SigabaNeo.Lattices

/-- The `W` low bits of `v`, low bit first. -/
def bitsOf (W v : ℕ) : List Bool := (List.range W).map v.testBit

/-- A list of numbers, `W` bits each. -/
def encEntries (W : ℕ) (vs : List ℕ) : List Bool := vs.flatMap (bitsOf W)

/-- The representatives of a matrix over `Z_q`, row-major. -/
def matVals {q r c : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod q)) : List ℕ :=
  (List.finRange r).flatMap fun i => (List.finRange c).map fun j => (M i j).val

/-- An integer matrix, reduced mod `q`. -/
def intMod {r c : ℕ} (q : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) : Matrix (Fin r) (Fin c) (ZMod q) :=
  M.map fun a => (a : ZMod q)

theorem matVals_eq_range {Q r c : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod Q)) (g : ℕ → ℕ → ℕ)
    (hg : ∀ (i : Fin r) (j : Fin c), (M i j).val = g i j) :
    matVals M = (List.range r).flatMap fun i => (List.range c).map (g i) := by
  unfold matVals
  rw [← List.map_coe_finRange_eq_range (n := r), List.flatMap_map]
  congr 1; funext i
  rw [← List.map_coe_finRange_eq_range (n := c), List.map_map]
  congr 1; funext j
  exact hg i j

/-- Element `i·c + j` of a flattened list of equal-length rows. -/
theorem getD_flatMap_rows {α β : Type*} (f : α → List β) (c : ℕ) (hf : ∀ a, (f a).length = c)
    (d : β) : ∀ (L : List α) {i j : ℕ} (hi : i < L.length) (_hj : j < c),
    (L.flatMap f).getD (i * c + j) d = (f L[i]).getD j d
  | [], _, _, hi, _ => by simp at hi
  | a :: L, i, j, hi, hj => by
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.getElem_cons_zero, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [hf]; exact hj)]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hf]; nlinarith), hf,
        show (i + 1) * c + j - c = i * c + j by rw [add_mul, one_mul]; omega,
        ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_rows f c hf d L (by simpa using hi) hj

theorem length_matVals {q r c : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod q)) :
    (matVals M).length = r * c := by
  simp [matVals, List.length_flatMap, List.sum_replicate]

theorem getD_matVals {q r c : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod q)) (i : Fin r) (j : Fin c) :
    (matVals M).getD (i.val * c + j.val) 0 = (M i j).val := by
  unfold matVals
  rw [getD_flatMap_rows _ c (fun a => by simp) 0 (List.finRange r) (by simp) j.isLt]
  simp [List.getD_eq_getElem?_getD]

end SigabaNeo.Lattices
