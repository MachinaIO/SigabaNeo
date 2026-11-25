import SigabaNeoStd.Lattices.Algorithms.LinearSolve
import Mathlib.Tactic

namespace SigabaNeo.Gauss

variable {K : Type*} [Field K] [DecidableEq K]

private abbrev Row (K : Type*) (d : ℕ) := (Fin d → K) × K

private def dot {d : ℕ} (a y : Fin d → K) := ∑ i, a i * y i

private def Fits {d : ℕ} (rows : List (Row K d)) (y : Fin d → K) :=
  ∀ r ∈ rows, dot r.1 y = r.2

private def tail {d : ℕ} (r : Row K (d+1)) : Row K d := (fun i ↦ r.1 i.succ, r.2)

-- Materialize the updated coefficients once, before entering the next elimination stage.
private def reduce {d : ℕ} (p r : Row K (d+1)) : Row K d :=
  let q := r.1 0 / p.1 0
  let a := Vector.ofFn (fun i : Fin d ↦ r.1 i.succ - q * p.1 i.succ)
  (a.get, r.2 - q * p.2)

private theorem reduced_dot {d : ℕ} (p r : Row K (d+1)) (y : Fin d → K) :
    dot (reduce p r).1 y = dot (tail r).1 y - r.1 0 / p.1 0 * dot (tail p).1 y := by
  simp [dot, reduce, tail, Vector.get, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  rfl

private theorem split_dot {d : ℕ} (r : Row K (d+1)) (y : Fin (d+1) → K) :
    dot r.1 y = r.1 0 * y 0 + dot (tail r).1 (fun i ↦ y i.succ) :=
  Fin.sum_univ_succ _

private def recover {d : ℕ} (p : Row K (d+1)) (y : Fin d → K) : Option (Fin (d+1) → K) :=
  let x := (p.2 - dot (tail p).1 y) / p.1 0
  some (Fin.cons x y)

/-- The counter charges field additions, subtractions, multiplications and divisions.
Pivot search and zero tests use equality. A pivot row is retained as a zero equation. -/
private def elim : (d : ℕ) → List (Row K d) → Option (Fin d → K) × ℕ
  | 0, rows => (if rows.all (fun r ↦ r.2 == 0) then some Fin.elim0 else none, 0)
  | d+1, rows =>
    match rows.find? (fun r ↦ r.1 0 != 0) with
    | none =>
      let (z, k) := elim d (rows.map tail)
      (z.map (Fin.cons 0), k)
    | some p =>
      let (z, k) := elim d (rows.map (reduce p))
      (z.bind (recover p), k + rows.length * (2*d+3) + if z.isSome then 2*d+2 else 0)

private theorem spec (d : ℕ) (rs : List (Row K d)) :
    match (elim d rs).1 with
    | some y => Fits rs y
    | none => ¬ ∃ y, Fits rs y := by
  induction d with
  | zero =>
    simp only [elim]
    by_cases h : rs.all (fun r ↦ r.2 == 0) = true <;> simp only [h, ite_true, ite_false]
    · simp [Fits, dot] at *; grind
    · rintro ⟨y, hy⟩
      apply h
      simp [Fits, dot] at *; grind
  | succ d ih =>
    simp only [elim]
    cases hp : rs.find? (fun r ↦ r.1 0 != 0) with
    | none =>
      have hz := List.find?_eq_none.mp hp
      have hrec := ih (rs.map tail)
      cases he : (elim d (rs.map tail)).1 with
      | none =>
        rw [he] at hrec
        simp [he]
        intro y hy
        apply hrec
        refine ⟨fun i ↦ y i.succ, ?_⟩
        intro r hr
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        have h0 : s.1 0 = 0 := by simpa using hz s hs
        simpa [split_dot s, h0, tail] using hy s hs
      | some y =>
        rw [he] at hrec
        simp only [he, Option.map_some]
        intro r hr
        have h0 : r.1 0 = 0 := by simpa using hz r hr
        simpa [split_dot r, h0] using
          (show dot (tail r).1 y = r.2 from hrec _ (List.mem_map_of_mem hr))
    | some p =>
      have hn : p.1 0 ≠ 0 := by simpa using List.find?_some hp
      have hm := List.mem_of_find?_eq_some hp
      have hrec := ih (rs.map (reduce p))
      cases he : (elim d (rs.map (reduce p))).1 with
      | none =>
        rw [he] at hrec
        simp [he]
        intro y hy
        apply hrec
        refine ⟨fun i ↦ y i.succ, ?_⟩
        intro r hr
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        have h₁ := hy p hm
        have h₂ := hy s hs
        rw [split_dot] at h₁ h₂
        rw [reduced_dot]
        change _ = s.2 - _ * p.2
        rw [← h₁, ← h₂]
        field_simp
        ring
      | some y =>
        rw [he] at hrec
        simp only [he, Option.bind, recover]
        intro r hr
        have h := hrec _ (List.mem_map_of_mem (f := reduce p) hr)
        rw [reduced_dot] at h
        change _ = r.2 - _ * p.2 at h
        rw [split_dot]
        simp
        field_simp at h ⊢
        linear_combination h

private theorem cost (d : ℕ) (rs : List (Row K d)) :
    (elim d rs).2 ≤ 5 * rs.length * d * (d+1) := by
  induction d with
  | zero => simp [elim]
  | succ d ih =>
    simp only [elim]
    split
    · have h := ih (rs.map tail)
      simp only [List.length_map] at h
      nlinarith
    · rename_i p hp
      have h := ih (rs.map (reduce p))
      simp only [List.length_map] at h
      have hm := List.mem_of_find?_eq_some hp
      have hl : 1 ≤ rs.length := List.length_pos_of_mem hm
      split <;> nlinarith [Nat.mul_le_mul_right d hl]

/-- Solve the augmented system by column-wise Gaussian elimination. -/
def solve {m D : ℕ} (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K) :=
  elim D (List.ofFn (fun i ↦ (M i, c i)))

private theorem fits_iff {m D : ℕ} (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K)
    (y : Fin D → K) : Fits (List.ofFn (fun i ↦ (M i, c i))) y ↔ M.mulVec y = c := by
  simp [Fits, funext_iff, Matrix.mulVec, dotProduct, dot, List.mem_ofFn]

theorem sound {m D : ℕ} (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K)
    {y} (h : (solve M c).1 = some y) : M.mulVec y = c := by
  have hs := spec D (List.ofFn (fun i ↦ (M i, c i)))
  rw [← solve, h] at hs
  exact (fits_iff ..).mp hs

theorem complete {m D : ℕ} (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K)
    (hker : LinearMap.ker M.mulVecLin = ⊥) (hc : c ∈ Submodule.span K (Set.range M.col)) :
    ∃ y, (solve M c).1 = some y ∧ M.mulVec y = c ∧ ∀ z, M.mulVec z = c → z = y := by
  obtain ⟨x, hx, hu⟩ := LinearSolve.existsUnique_mulVec M c hker hc
  cases h : (solve M c).1 with
  | some y => exact ⟨y, rfl, sound M c h, fun z hz ↦ (hu z hz).trans (hu y (sound M c h)).symm⟩
  | none =>
    have hs := spec D (List.ofFn (fun i ↦ (M i, c i)))
    rw [← solve, h] at hs
    exact (hs ⟨x, (fits_iff ..).mpr hx⟩).elim

theorem fieldOps_le {m D : ℕ} (M : Matrix (Fin m) (Fin D) K) (c : Fin m → K) :
    (solve M c).2 ≤ 5 * m * D * (D+1) := by
  simpa [solve] using cost D (List.ofFn (fun i ↦ (M i, c i)))

#print axioms sound
#print axioms complete
#print axioms fieldOps_le

end SigabaNeo.Gauss
