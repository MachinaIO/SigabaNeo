import Solution.Pre1Coord

/-!
# Pre1, the whole row: `2T + E'` is close to uniform

`Zdist κ` is the law of the row `2T + E' (mod q)`. Its coordinates are independent copies of the
law `L1 κ` of `Solution/Pre1Coord.lean` (`Zdist_map`), so it is within `k · εc` of uniform
(`closeTo_Zdist`, by cslib-frontier's `dist_pi_le_sum`).
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability
open scoped ENNReal Cslib.Probability.PMF

section
variable (κ : ℕ)

/-- The row `2T + E' (mod q)`. -/
noncomputable def Zdist : PMF (Row κ) :=
  (PMF.uniformOfFintype (TMat κ)).bind fun T =>
    (sampleMat (gaussZ (σ' κ) (σ'_pos κ)) (ell κ) (k κ)).map fun E' =>
      (2 : ZMod (q κ)) • Tq κ T + intMod (q κ) E'

/-- A row as a vector. -/
noncomputable def rowEquiv : Row κ ≃ (Fin (k κ) → ZMod (q κ)) := Equiv.funUnique (Fin (ell κ)) _

theorem Zdist_map : (Zdist κ).map (rowEquiv κ) = PMF.pi (fun _ : Fin (k κ) => L1 κ) := by
  refine pmf_ext_ev fun g => ?_
  unfold L1
  rw [PMF.pi_bind, ev_bind]
  have hinner : ∀ t : Fin (k κ) → Fin (NT κ),
      PMF.pi (fun j => (gaussZ (σ' κ) (σ'_pos κ)).map (cz κ (t j))) =
        (PMF.pi (fun _ : Fin (k κ) => (gaussZ (σ' κ) (σ'_pos κ)).map (Int.cast : ℤ → ZMod (q κ)))).map
          (fun e j => ((2 * ((t j : ℕ) : ℤ) : ℤ) : ZMod (q κ)) + e j) := by
    intro t
    rw [← PMF.pi_map]
    congr 1; funext j
    rw [PMF.map_comp]
    congr 1; funext e
    simp [cz]
  simp only [hinner, ← sampleList_pi, ev_map]
  rw [PMF.pi_uniformOfFintype]
  unfold Zdist
  rw [ev_bind]
  let e : TMat κ ≃ (Fin (k κ) → Fin (NT κ)) := Equiv.funUnique (Fin (ell κ)) _
  rw [← ev_uniform_equiv e]
  congr 1; funext t
  rw [ev_map, sampleMat_eq, ev_map, show ell κ * k κ = k κ by simp [ell]]
  congr 1; funext l
  simp only [Function.comp_apply]
  congr 1
  funext j
  show ((2 : ZMod (q κ)) • Tq κ t + intMod (q κ) (Matrix.of fun (i : Fin (ell κ)) (j : Fin (k κ)) =>
      l.getD ((i : ℕ) * k κ + j) default)) default j =
    (((2 * ((t default j : ℕ) : ℤ)) : ℤ) : ZMod (q κ)) + ((l.getD (j : ℕ) default : ℤ) : ZMod (q κ))
  simp only [Matrix.add_apply, Matrix.smul_apply, Tq, intMod, Matrix.map_apply, Matrix.of_apply,
    smul_eq_mul, fin_ell_val, zero_mul, zero_add]
  push_cast
  ring

theorem closeTo_Zdist :
    CloseTo (Zdist κ) (PMF.uniformOfFintype (Row κ)) (ENNReal.ofReal (k κ * εc κ)) := by
  have hd : dist (PMF.pi (fun _ : Fin (k κ) => L1 κ))
      (PMF.pi (fun _ : Fin (k κ) => PMF.uniformOfFintype (ZMod (q κ)))) ≤ k κ * εc κ := by
    refine (PMF.dist_pi_le_sum _ _).trans ?_
    have h1 : dist (L1 κ) (PMF.uniformOfFintype (ZMod (q κ))) ≤ εc κ :=
      (closeTo_ofReal_iff_dist_le (εc_nonneg κ)).mp (closeTo_coord κ)
    calc ∑ _j : Fin (k κ), dist (L1 κ) (PMF.uniformOfFintype (ZMod (q κ)))
        ≤ ∑ _j : Fin (k κ), εc κ := Finset.sum_le_sum fun _ _ => h1
      _ = k κ * εc κ := by simp
  rw [PMF.pi_uniformOfFintype, ← Zdist_map] at hd
  have hc := (closeTo_of_dist_le_ofReal hd).map (rowEquiv κ).symm
  rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id, PMF.uniformOfFintype_map_equiv] at hc
  exact hc

end

end TestCase.EvLWE
