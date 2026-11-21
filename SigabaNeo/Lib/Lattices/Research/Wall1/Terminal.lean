module

public import SigabaNeo.Lib.Lattices.Reduction.BKZ

public section

namespace SigabaNeo.Wall1

/-- A nonzero vector with no proper positive integral divisor in the quotient lattice. -/
def Primitive {M : Type*} [AddCommGroup M] (x : M) : Prop :=
  x ≠ 0 ∧ ∀ (a : ℕ) (y : M), 2 ≤ a → x ≠ a • y

private theorem factor {M ι : Type*} [AddCommGroup M] [Module ℤ M]
    (B : Module.Basis ι ℤ M) (i : ι) (x : M) (hx : B.repr x i ≠ 0) :
    ∃ (a : ℕ) (y : M), 0 < a ∧ Primitive y ∧ x = a • y := by
  classical
  by_cases h : Primitive x
  · exact ⟨1, x, by decide, h, (one_smul _ _).symm⟩
  have hn : x ≠ 0 := by rintro rfl; simp at hx
  have bad : ¬ ∀ (a : ℕ) (y : M), 2 ≤ a → x ≠ a • y := fun hdiv ↦ h ⟨hn, hdiv⟩
  push Not at bad
  obtain ⟨k, z, hk, rfl⟩ := bad
  have e : B.repr (k • z) i = (k : ℤ) * B.repr z i := by simp
  have hz : B.repr z i ≠ 0 := by intro eq; simp [eq] at hx
  obtain ⟨a, y, ha, hy, hzy⟩ := factor B i z hz
  exact ⟨k*a, y, Nat.mul_pos (by omega) ha, hy, by rw [hzy, mul_smul]⟩
termination_by (B.repr x i).natAbs
decreasing_by
  rw [show x = k • z by assumption, e, Int.natAbs_mul, Int.natAbs_natCast]
  have := Int.natAbs_pos.mpr hz
  nlinarith

/-- Apply to the orthogonal image Q of a lattice modulo a primitive prefix, with v the
projected vector. Primitive generators are compared up to their two possible signs. -/
theorem terminal_primitive_iff {d : ℕ} {ι : Type*}
    (Q : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (B : Module.Basis ι ℤ Q)
    (v : Q) (hv : v ≠ 0) :
    (∀ w : Q, w ≠ 0 → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖) ↔
    Primitive v ∧ ∀ w : Q, Primitive w → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖ := by
  have scale (a : ℕ) (w : Q) : ‖a • w‖ = (a : ℝ) * ‖w‖ := by
    change ‖a • (w : EuclideanSpace ℝ (Fin d))‖ = _
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
    simp
  constructor
  · intro h
    refine ⟨⟨hv, ?_⟩, fun w hw ↦ h w hw.1⟩
    intro a w ha he
    have hw : w ≠ 0 := by rintro rfl; simp [he] at hv
    have hp := norm_pos_iff.mpr hw
    have hh : ‖w‖ < ‖v‖ := by rw [he, scale]; nlinarith [show (2:ℝ) ≤ a by exact_mod_cast ha]
    apply hh.asymm
    apply h w hw
    · exact fun e ↦ hh.ne (congrArg norm e)
    · intro e
      simp [e] at hh
  · rintro ⟨_, h⟩ w hw hpos hneg
    classical
    obtain ⟨i, hi⟩ : ∃ i, B.repr w i ≠ 0 := by
      by_contra! hh
      apply hw
      apply B.repr.injective
      ext i
      simp [hh]
    obtain ⟨a, y, ha, hy, rfl⟩ := factor B i w hi
    rw [scale]
    have hp := norm_pos_iff.mpr hy.1
    have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
    by_cases hs : y = v ∨ y = -v
    · have hn : a ≠ 1 := by
        rintro rfl
        simp only [one_smul] at hpos hneg
        exact hs.elim hpos hneg
      have hnorm : ‖y‖ = ‖v‖ := by rcases hs with e | e <;> simp [e]
      rw [← hnorm]
      have : (2:ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      nlinarith
    · exact (h y hy (fun e ↦ hs (.inl e)) (fun e ↦ hs (.inr e))).trans_le
        (by nlinarith)

/-- Orthogonal image of the lattice in the complement of the prefix span. -/
noncomputable def projectedLattice {d : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :=
  L.map (Wᗮ.starProjection.toLinearMap.restrictScalars ℤ)

noncomputable def projectedPoint {d : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (u : L) : projectedLattice L W :=
  ⟨Wᗮ.starProjection u.val, ⟨u.val,u.property,rfl⟩⟩

/-- Terminal criterion with the vector and lattice both projected off the same prefix. -/
theorem projected_terminal_iff {d : ℕ} {ι : Type*}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (B : Module.Basis ι ℤ (projectedLattice L W)) (u : L) (hv : projectedPoint L W u ≠ 0) :
    let v := projectedPoint L W u
    (∀ w : projectedLattice L W, w ≠ 0 → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖) ↔
    Primitive v ∧ ∀ w : projectedLattice L W, Primitive w → w ≠ v → w ≠ -v → ‖v‖ < ‖w‖ :=
  terminal_primitive_iff _ B _ hv

#print axioms projected_terminal_iff
end SigabaNeo.Wall1
