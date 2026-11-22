import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenIdx
import SigabaNeo.Lib.Lattices.Algo.FhatLoop

/-!
# Generating gate tapes: representations of ciphertexts as lists

A representation `rep : BI N k → Wire ι` of a Ring-GSW ciphertext is held in a list register as
`repList`: for each output position `o = (a, c, j)` in the order `enumO` its `k` bits, i.e. the
bit `(a, c, i, j)` at `oIdx o · k + i` (`repList_slice`, `repList_getD`). The output of a NAND block
has this layout.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

theorem getElem?_product {α β : Type*} (l₂ : List β) : ∀ (l₁ : List α) (i j : ℕ)
    (hi : i < l₁.length) (hj : j < l₂.length),
    (l₁ ×ˢ l₂)[i * l₂.length + j]? = some (l₁[i], l₂[j])
  | [], i, _, hi, _ => by simp at hi
  | a :: t, 0, j, _, hj => by
    rw [List.product_cons, Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by simpa)]
    simp [hj]
  | a :: t, i + 1, j, hi, hj => by
    rw [List.product_cons, List.getElem?_append_right (by simp; nlinarith)]
    simp only [List.length_map, List.getElem_cons_succ]
    rw [show (i + 1) * l₂.length + j - l₂.length = i * l₂.length + j by
      rw [Nat.succ_mul]; omega]
    exact getElem?_product l₂ t i j (by simpa using hi) hj

theorem drop_take_flatten' {α : Type*} {V : ℕ} :
    ∀ (vs : List (List α)), (∀ w ∈ vs, w.length = V) → ∀ (j : ℕ) (hj : j < vs.length),
      ((vs.flatten).drop (j * V)).take V = vs[j]
  | [], _, j, hj => absurd hj (by simp)
  | w :: vs, h, 0, _ => by
    simp only [List.flatten_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
    exact List.take_left' (h w (by simp))
  | w :: vs, h, j + 1, hj => by
    have hw : w.length = V := h w (by simp)
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' hw]
    exact drop_take_flatten' vs (fun x hx => h x (by simp [hx])) j (by simpa using hj)

theorem length_flatten_of' {α : Type*} {V : ℕ} :
    ∀ (vs : List (List α)), (∀ w ∈ vs, w.length = V) → (vs.flatten).length = vs.length * V
  | [], _ => by simp
  | w :: vs, h => by
    rw [List.flatten_cons, List.length_append, h w (by simp),
      length_flatten_of' vs (fun x hx => h x (by simp [hx])), List.length_cons, Nat.succ_mul,
      Nat.add_comm]

variable {N k : ℕ}

/-- The index of an output position in `enumO`. -/
def oIdx (o : OI N k) : ℕ := ((o.1.val * 2 + o.2.1.1.val) * k + o.2.1.2.val) * N + o.2.2.val

theorem enumO_getElem? (o : OI N k) : (enumO N k)[oIdx o]? = some o := by
  obtain ⟨a, ⟨c1, c2⟩, j⟩ := o
  have e0 := getElem?_product (List.finRange k) (List.finRange 2) c1.val c2.val
    (by simpa using c1.isLt) (by simpa using c2.isLt)
  have hc : c1.val * k + c2.val < (List.finRange 2 ×ˢ List.finRange k).length := by
    simp [List.length_product]; nlinarith [c1.isLt, c2.isLt]
  have e0' : (List.finRange 2 ×ˢ List.finRange k)[c1.val * k + c2.val] = (c1, c2) := by
    simp only [List.length_finRange] at e0
    have := (List.getElem?_eq_some_iff.mp e0).2
    simpa using this
  have e1 := getElem?_product (List.finRange N) (List.finRange 2 ×ˢ List.finRange k)
    (c1.val * k + c2.val) j.val hc (by simpa using j.isLt)
  simp only [List.length_finRange] at e1
  rw [e0'] at e1
  have hl : ((List.finRange 2 ×ˢ List.finRange k) ×ˢ List.finRange N).length = 2 * k * N := by
    simp [List.length_product]
  have hj : (c1.val * k + c2.val) * N + j.val < ((List.finRange 2 ×ˢ List.finRange k) ×ˢ
      List.finRange N).length := by
    rw [hl]; nlinarith [c1.isLt, c2.isLt, j.isLt]
  have e1' : ((List.finRange 2 ×ˢ List.finRange k) ×ˢ List.finRange N)[(c1.val * k + c2.val) * N +
      j.val] = ((c1, c2), j) := by
    have := (List.getElem?_eq_some_iff.mp e1).2
    simpa using this
  have e2 := getElem?_product ((List.finRange 2 ×ˢ List.finRange k) ×ˢ List.finRange N)
    (List.finRange 2) a.val ((c1.val * k + c2.val) * N + j.val) (by simpa using a.isLt) hj
  rw [e1', hl] at e2
  simp only [oIdx, enumO]
  rw [show ((a.val * 2 + c1.val) * k + c2.val) * N + j.val =
    a.val * (2 * k * N) + ((c1.val * k + c2.val) * N + j.val) by ring, e2]
  simp

theorem oIdx_lt (o : OI N k) : oIdx o < 4 * k * N := by
  have := enumO_getElem? o
  have h := (List.getElem?_eq_some_iff.mp this).1
  rwa [length_enumO'] at h

/-- The list of a representation: the `k` bits of each output position, in the order `enumO`. -/
def repList {ι : Type*} (E : Env) (ix : ι → ℕ) (rep : BI N k → Wire ι) : List ℕ :=
  ((enumO N k).map fun o => (List.ofFn fun i : Fin k => rep (o.1, o.2.1, i, o.2.2)).map
    (pos E ix)).flatten

theorem length_repList {ι : Type*} (E : Env) (ix : ι → ℕ) (rep : BI N k → Wire ι) :
    (repList (N := N) E ix rep).length = 4 * k * N * k := by
  rw [repList, length_flatten_of' (V := k) _ (fun w hw => by
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hw; simp)]
  simp [length_enumO']

/-- **The bits of one output position** in the list of a representation. -/
theorem repList_slice {ι : Type*} (E : Env) (ix : ι → ℕ) (rep : BI N k → Wire ι) (o : OI N k) :
    ((repList E ix rep).drop (oIdx o * k)).take k =
      (List.ofFn fun i : Fin k => rep (o.1, o.2.1, i, o.2.2)).map (pos E ix) := by
  have hlt : oIdx o < ((enumO N k).map fun o => (List.ofFn fun i : Fin k =>
      rep (o.1, o.2.1, i, o.2.2)).map (pos E ix)).length := by simp [length_enumO', oIdx_lt]
  rw [repList, drop_take_flatten' _ (fun w hw => by
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hw; simp) _ hlt]
  simp only [List.getElem_map]
  congr 2
  have := (List.getElem?_eq_some_iff.mp (enumO_getElem? o)).2
  rw [this]

theorem repList_getD {ι : Type*} (E : Env) (ix : ι → ℕ) (rep : BI N k → Wire ι) (o : OI N k)
    (i : Fin k) : (repList E ix rep).getD (oIdx o * k + i.val) 0 =
      pos E ix (rep (o.1, o.2.1, i, o.2.2)) := by
  have h := congrArg (fun l => l.getD i.val 0) (repList_slice E ix rep o)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at h
  rw [if_pos i.isLt] at h
  rw [List.getD_eq_getElem?_getD, h]
  simp

end FhatGen

end SigabaNeo.Lattices
