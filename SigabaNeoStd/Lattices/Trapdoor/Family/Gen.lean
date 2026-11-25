import SigabaNeoStd.Lattices.Trapdoor.Family.LHL

/-!
# Trapdoor sampler: the public matrix of `GenTrap` is close to uniform

`GenTrap` draws `Ā` uniform and the columns of `R` as codes (`Rcodes`, two fair bits per entry,
decoded by `dec4`), and outputs `B = [Ā | G − Ā R]`. The map `(Ā, V) ↦ [Ā | G − V]` is a bijection
(`bEquiv'`), so `B` is uniform when `V = Ā R` is replaced by a uniform `V`; the columns of `Ā R`
are handled one at a time with the same `Ā` (cslib-frontier's `dist_bind_pair_pi_le_sum`) and
`lhl_column`. Hence `B` is within `εLHL = mb · √(q^n (3/8)^{mb}) / 2` of uniform (`closeTo_genB`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal Matrix Cslib.Probability.PMF

section
variable (κ : ℕ)

/-- The codes of `R`, column by column. -/
abbrev RCodes : Type := Fin (mb κ) → Codes κ

/-- `R` from its codes. -/
def RofCodes (Rc : RCodes κ) : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ := fun a c => dec4 (Rc c a)

theorem abs_RofCodes_le (Rc : RCodes κ) (a c : Fin (mb κ)) : |RofCodes κ Rc a c| ≤ 1 :=
  abs_dec4_le _

/-- `[Ā | G − V]` with `V` given by its columns. -/
noncomputable def Bfrom (p : MatA κ × (Fin (mb κ) → Syn κ)) :
    Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) :=
  (Matrix.fromCols p.1 (gadget κ - Matrix.of fun i c => p.2 c i)).submatrix id (colEquiv κ)

theorem Bmat_eq_Bfrom (Abar : MatA κ) (Rc : RCodes κ) :
    Bmat κ Abar (RofCodes κ Rc) = Bfrom κ (Abar, fun c => hA κ Abar (Rc c)) := by
  unfold Bmat Bfrom
  congr 2

/-- `(Ā, V) ↦ [Ā | G − V]` is a bijection. -/
noncomputable def bEquiv' : (MatA κ × (Fin (mb κ) → Syn κ)) ≃
    Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) where
  toFun := Bfrom κ
  invFun B := (fun i a => B i ((colEquiv κ).symm (Sum.inl a)),
    fun c i => gadget κ i c - B i ((colEquiv κ).symm (Sum.inr c)))
  left_inv p := by
    obtain ⟨A, V⟩ := p
    simp [Bfrom, Matrix.submatrix_apply]
  right_inv B := by
    ext i j
    simp only [Bfrom, Matrix.submatrix_apply, id]
    have hj : j = (colEquiv κ).symm (colEquiv κ j) := by simp
    cases h : colEquiv κ j with
    | inl a => rw [h] at hj; rw [hj]; rfl
    | inr c =>
      rw [h] at hj; rw [hj]
      show gadget κ i c - (gadget κ i c - B i ((colEquiv κ).symm (Sum.inr c))) = _
      ring


/-- The public matrix of `GenTrap` (with exactly uniform `Ā` and codes). -/
noncomputable def genB : PMF (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))) :=
  (PMF.uniformOfFintype (MatA κ × RCodes κ)).map fun p => Bmat κ p.1 (RofCodes κ p.2)

noncomputable def εLHL : ℝ := mb κ * (Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) / 2)

theorem εLHL_nonneg : 0 ≤ εLHL κ := by unfold εLHL; positivity

theorem dist_AV :
    dist ((PMF.uniformOfFintype (MatA κ)).bind fun A =>
        (PMF.pi fun _ : Fin (mb κ) => (PMF.uniformOfFintype (Codes κ)).map (hA κ A)).map (A, ·))
      ((PMF.uniformOfFintype (MatA κ)).bind fun A =>
        (PMF.pi fun _ : Fin (mb κ) => PMF.uniformOfFintype (Syn κ)).map (A, ·)) ≤ εLHL κ := by
  classical
  refine (PMF.dist_bind_pair_pi_le_sum _ _ _).trans ?_
  have h : ∀ c : Fin (mb κ),
      dist ((PMF.uniformOfFintype (MatA κ)).bind fun A =>
          ((PMF.uniformOfFintype (Codes κ)).map (hA κ A)).map (A, ·))
        ((PMF.uniformOfFintype (MatA κ)).bind fun A => (PMF.uniformOfFintype (Syn κ)).map (A, ·)) ≤
        Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) / 2 := by
    intro c
    rw [PMF.dist_bind_pair]
    exact lhl_column κ
  calc _ ≤ ∑ _c : Fin (mb κ), Real.sqrt ((q κ : ℝ) ^ n κ * (3 / 8) ^ mb κ) / 2 :=
        Finset.sum_le_sum fun c _ => h c
    _ = εLHL κ := by simp [εLHL]

theorem closeTo_genB :
    CloseTo (genB κ) (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))))
      (ENNReal.ofReal (εLHL κ)) := by
  classical
  have hlaw : genB κ = (((PMF.uniformOfFintype (MatA κ)).bind fun A =>
      (PMF.pi fun _ : Fin (mb κ) => (PMF.uniformOfFintype (Codes κ)).map (hA κ A)).map
        (A, ·))).map (bEquiv' κ) := by
    unfold genB
    rw [← PMF.uniformOfFintype_prod, PMF.map_bind, PMF.map_bind]
    congr 1; funext A
    rw [PMF.pi_map, PMF.pi_uniformOfFintype, PMF.map_comp, PMF.map_comp, PMF.map_comp]
    congr 1
  have hideal : PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ))) =
      (((PMF.uniformOfFintype (MatA κ)).bind fun A =>
        (PMF.pi fun _ : Fin (mb κ) => PMF.uniformOfFintype (Syn κ)).map (A, ·))).map (bEquiv' κ) := by
    rw [PMF.pi_uniformOfFintype, PMF.uniformOfFintype_prod, PMF.uniformOfFintype_map_equiv]
  rw [hlaw, hideal]
  exact (closeTo_of_dist_le_ofReal (dist_AV κ)).map _

end

end SigabaNeo.Lattices.Trapdoor.Family
