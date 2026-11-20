import SigabaNeo.Lib.Lattices.Trapdoor.Family.Vec
import SigabaNeo.Lib.Lattices.Trapdoor.Family.Gen
import SigabaNeo.Lib.Lattices.Trapdoor.Family.Smooth

/-!
# Trapdoor sampler: the joint law of `(B, K)`

`realJ P`: draw the trapdoor `(Ā, R)` (uniform `Ā`, codes of `R`), set `B = [Ā | G − Ā R]`, and
sample each column of `K` with `colLawOf μV` (the sampler of `Family/Vec.lean`, shifted into
the coset of `P_j`). `idealJ P`: uniform `B` and the coset Gaussian preimage of each column, as in
`Trapdoor.ideal`. When `SmoothCond κ` holds,

  `realJ P` is within `k · colErr + ε_LHL` of `idealJ P`  (`joint_close`),

from `colLawOf_close` (each column), independence of the columns (`closeTo_sampleOptList`) and
the leftover hash lemma (`closeTo_genB`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal Matrix

/-- Independent optional draws, closeness column by column. -/
theorem closeTo_sampleOptList {α : Type} {ε : ℝ≥0∞} :
    ∀ {ds : List (PMF α)} {es : List (Option (PMF α))},
      List.Forall₂ (fun d e => ∃ p, e = some p ∧ CloseTo d p ε) ds es →
      CloseTo (sampleOptList (ds.map some)) (sampleOptList es) (ds.length * ε)
  | [], [], List.Forall₂.nil => by simp
  | d :: ds, e :: es, List.Forall₂.cons ⟨p, hp, hc⟩ h => by
    subst hp
    have ih := closeTo_sampleOptList h
    have : CloseTo (d.bind fun a => (sampleOptList (ds.map some)).map (Option.map (a :: ·)))
        (p.bind fun a => (sampleOptList es).map (Option.map (a :: ·))) (ε + ds.length * ε) :=
      CloseTo.bind hc fun a _ => ih.map _
    show CloseTo (d.bind fun a => (sampleOptList (ds.map some)).map (Option.map (a :: ·)))
      (p.bind fun a => (sampleOptList es).map (Option.map (a :: ·))) _
    exact this.mono (le_of_eq (by rw [List.length_cons]; push_cast; ring))

section
variable (κ : ℕ)

/-- Columns of `K` from per-column laws. -/
noncomputable def colsOf (l : List (Option (PMF (Fin (m κ) → ℤ)))) :
    PMF (Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  (sampleOptList l).map (Option.map fun cols r j => (cols.getD j.val 0) r)

/-- The coset Gaussian preimage of `P` (`Trapdoor.preimage`). -/
noncomputable def colsIdeal (B : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))
    (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    PMF (Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  colsOf κ ((List.finRange (k κ)).map fun j => cosetGauss B (fun i => P i j) (τ κ) (τ_pos κ))

/-- The sampled preimage. -/
noncomputable def colsReal (Abar : MatA κ) (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ)
    (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    PMF (Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  colsOf κ ((List.finRange (k κ)).map fun j => some (colLawOf κ (μV κ) Abar R (fun i => P i j)))

noncomputable def realJ (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    PMF (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) × Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  (PMF.uniformOfFintype (MatA κ × RCodes κ)).bind fun p =>
    (colsReal κ p.1 (RofCodes κ p.2) P).map (Bmat κ p.1 (RofCodes κ p.2), ·)

noncomputable def idealJ (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    PMF (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) × Option (Matrix (Fin (m κ)) (Fin (k κ)) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)))).bind fun B =>
    (colsIdeal κ B P).map (B, ·)

/-- The tail bound of `μV`. -/
noncomputable def tgV : ℝ≥0∞ := (m κ : ℝ≥0∞) * (b1 κ * ENNReal.ofReal (6 * (1 / 4) ^ m κ))

/-- The error of one column. -/
noncomputable def colErr : ℝ≥0∞ :=
  (1 - a1 κ ^ m κ * (b1 κ ^ m κ)⁻¹ * ENNReal.ofReal (Real.exp (-(2 * θT κ))) * (1 - tgV κ)) +
    ENNReal.ofReal (3 * 2 ^ m κ * (1 / 4) ^ (m κ ^ 2))

theorem b1_ne_zero : b1 κ ≠ 0 := by
  unfold b1
  refine (add_pos_of_pos_of_nonneg (pos_iff_ne_zero.mpr (mul_ne_zero (cH_pos κ) ?_)) bot_le).ne'
  exact ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))

theorem b1_ne_top : b1 κ ≠ ⊤ := by
  unfold b1
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
      (qfail_le_one κ))) (Zm_ne_top κ)⟩
  refine ENNReal.inv_ne_top.mpr (mul_ne_zero (cL_pos κ) ?_)
  exact (tsub_pos_of_lt (tq_lt_one κ)).ne'

theorem colLawOf_μV_close (hc : SmoothCond κ) (Abar : MatA κ) (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ)
    (hR : ∀ i j, |R i j| ≤ 1) (u : Fin (n κ) → ZMod (q κ)) :
    ∃ p, cosetGauss (Bmat κ Abar R) u (τ κ) (τ_pos κ) = some p ∧
      CloseTo (colLawOf κ (μV κ) Abar R u) p (colErr κ) := by
  classical
  have hex : ∃ x0 : Fin (m κ) → ℤ, Bmat κ Abar R *ᵥ (fun i => (x0 i : ZMod (q κ))) = u :=
    ⟨xPre κ R u, Bmat_mulVec_xPre κ Abar R u⟩
  have hsome : cosetGauss (Bmat κ Abar R) u (τ κ) (τ_pos κ) =
      some ((ZLattice.discreteGaussian (perp (Bmat κ Abar R)) (τ κ) (τ_pos κ)
        (-(embed (m κ) hex.choose))).map fun z => hex.choose + toInt (z : EuclideanSpace ℝ (Fin (m κ)))) := by
    unfold cosetGauss; rw [dite_eq_left_of_eq_true (eq_true hex)]
  refine ⟨_, hsome, ?_⟩
  exact colLawOf_close κ (μV κ) (pow_ne_zero _ (b1_ne_zero κ)) (ENNReal.pow_ne_top (b1_ne_top κ))
    (fun y hy => μV_ge κ y hy) (fun y => μV_le κ y) (μV_tail κ) Abar R hR u
    (dualMassE_le_half κ Abar R hR hc) hsome

theorem colsReal_close (hc : SmoothCond κ) (Abar : MatA κ) (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ)
    (hR : ∀ i j, |R i j| ≤ 1) (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    CloseTo (colsReal κ Abar R P) (colsIdeal κ (Bmat κ Abar R) P) (k κ * colErr κ) := by
  unfold colsReal colsIdeal colsOf
  refine CloseTo.map ?_ _
  have h := closeTo_sampleOptList (ε := colErr κ)
    (ds := (List.finRange (k κ)).map fun j => colLawOf κ (μV κ) Abar R (fun i => P i j))
    (es := (List.finRange (k κ)).map fun j =>
      cosetGauss (Bmat κ Abar R) (fun i => P i j) (τ κ) (τ_pos κ)) (by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun j _ => ?_
      obtain ⟨p, hp, hcl⟩ := colLawOf_μV_close κ hc Abar R hR (fun i => P i j)
      exact ⟨p, hp, hcl⟩)
  rw [List.map_map, List.length_map, List.length_finRange] at h
  exact h

theorem joint_close (hc : SmoothCond κ) (P : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ))) :
    CloseTo (realJ κ P) (idealJ κ P) (k κ * colErr κ + ENNReal.ofReal (εLHL κ)) := by
  have hmid : (PMF.uniformOfFintype (MatA κ × RCodes κ)).bind (fun p =>
      (colsIdeal κ (Bmat κ p.1 (RofCodes κ p.2)) P).map (Bmat κ p.1 (RofCodes κ p.2), ·)) =
      (genB κ).bind fun B => (colsIdeal κ B P).map (B, ·) := by
    unfold genB
    rw [PMF.bind_map]; rfl
  have h1 : CloseTo (realJ κ P) ((genB κ).bind fun B => (colsIdeal κ B P).map (B, ·))
      (k κ * colErr κ) := by
    rw [← hmid]
    exact CloseTo.bind_right _ fun p _ =>
      (colsReal_close κ hc p.1 (RofCodes κ p.2) (abs_RofCodes_le κ p.2) P).map _
  exact h1.trans ((closeTo_genB κ).bind_left _)

end

end SigabaNeo.Lattices.Trapdoor.Family
