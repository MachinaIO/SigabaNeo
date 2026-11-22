module

public import Mathlib

public section

namespace SigabaNeo.Wall1.Rectangular

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The integral coordinate multiples of the given sides. -/
def lattice {n : ℕ} (a : Fin n → ℝ) : Set (E n) :=
  {v | ∃ z : Fin n → ℤ, ∀ i, v i = a i * z i}

/-- The nonzero vector lengths have least element r. -/
def HasMinimum {n : ℕ} (L : Set (E n)) (r : ℝ) : Prop :=
  IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = t} r

theorem diagonal_minimum {n : ℕ} (a : Fin n → ℝ) (k : Fin n)
    (hk : 0 < a k) (hle : ∀ i, a k ≤ a i) : HasMinimum (lattice a) (a k) := by
  classical
  constructor
  · refine ⟨PiLp.single 2 k (a k), ⟨Pi.single k 1, ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i = k <;> simp [PiLp.single_apply, h]
    · intro h
      have := congrArg (fun v : E n ↦ v k) h
      simp [hk.ne'] at this
    · simp [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hk]
  · rintro t ⟨v, ⟨z, hz⟩, hv, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra! h
      apply hv
      ext i
      simp [hz, h]
    have hi' : (1 : ℝ) ≤ |(z i : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |z i| by have := abs_pos.mpr hi; omega)
    calc
      a k ≤ a i := hle i
      _ ≤ a i * |(z i : ℝ)| := le_mul_of_one_le_right (hk.le.trans (hle i)) hi'
      _ = ‖v i‖ := by rw [hz, Real.norm_eq_abs, abs_mul, abs_of_pos (hk.trans_le (hle i))]
      _ ≤ ‖v‖ := PiLp.norm_apply_le v i

/-- Orthogonal projection off the first axis in the remaining coordinate frame. -/
def dropFirst {n : ℕ} (v : E (n+1)) : E n := WithLp.toLp 2 (fun i ↦ v i.succ)

theorem project_lattice {n : ℕ} (a : Fin (n+1) → ℝ) :
    dropFirst '' lattice a = lattice (fun i ↦ a i.succ) := by
  ext v
  constructor
  · rintro ⟨u, ⟨z, hz⟩, rfl⟩
    exact ⟨fun i ↦ z i.succ, fun i ↦ hz i.succ⟩
  · rintro ⟨z, hz⟩
    let w : Fin (n+1) → ℤ := Fin.cons (0 : ℤ) z
    refine ⟨WithLp.toLp 2 (fun i ↦ a i * w i), ⟨w, fun _ ↦ rfl⟩, ?_⟩
    ext i
    exact (hz i).symm

noncomputable def sides (x y : ℝ) : Fin 4 → ℝ := ![1/8, 1/4, x, y]

/-- The appended unit axis is placed last, so deletion keeps its coordinate. -/
noncomputable def extended (x y : ℝ) : Fin 5 → ℝ := ![1/8, 1/4, x, y, 1]

noncomputable def flag (x y : ℝ) : Set (E 5) := lattice (extended x y)

theorem example_determinants :
    (Matrix.diagonal (sides (1/3) 3)).det = 1/32 ∧
    (Matrix.diagonal (sides (1/2) 2)).det = 1/32 := by
  norm_num [Matrix.det_diagonal, sides, Fin.prod_univ_succ]

private theorem flag_minima (x y : ℝ) (hx : 1/4 ≤ x) (hu : x ≤ 1) (hy : 1 ≤ y) :
    HasMinimum (flag x y) (1/8) ∧ HasMinimum (dropFirst '' flag x y) (1/4) ∧
    HasMinimum (dropFirst '' (dropFirst '' flag x y)) x := by
  unfold flag
  simp only [project_lattice]
  refine ⟨diagonal_minimum _ 0 (by norm_num [extended]) ?_,
    diagonal_minimum _ 0 (by norm_num [extended]) ?_,
    diagonal_minimum _ 0 (by change 0 < x; linarith) ?_⟩ <;>
    intro i <;> fin_cases i <;> norm_num [extended] <;> linarith

theorem example_minima :
    (HasMinimum (flag (1/3) 3) (1/8) ∧ HasMinimum (dropFirst '' flag (1/3) 3) (1/4) ∧
      HasMinimum (dropFirst '' (dropFirst '' flag (1/3) 3)) (1/3)) ∧
    (HasMinimum (flag (1/2) 2) (1/8) ∧ HasMinimum (dropFirst '' flag (1/2) 2) (1/4) ∧
      HasMinimum (dropFirst '' (dropFirst '' flag (1/2) 2)) (1/2)) ∧
    (1/3 : ℝ) ≠ 1/2 := by
  exact ⟨flag_minima _ _ (by norm_num) (by norm_num) (by norm_num),
    flag_minima _ _ (by norm_num) (by norm_num) (by norm_num), by norm_num⟩

#print axioms diagonal_minimum
#print axioms project_lattice
#print axioms example_determinants
#print axioms example_minima

end SigabaNeo.Wall1.Rectangular
