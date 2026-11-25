import Solution.Count
import Solution.SmoothParams
import SigabaNeoStd.Lattices.Gaussian.Z

/-!
# Facts about the Post experiments

* `parityOut_nil`: the attack accepts the empty word (the output on an abort).
* `cosetGauss_support`, `preimage_support`: every drawn column `K_j` has `B·K_j = P_j (mod q)`.
* `ev_preimage_none_le`: the experiment aborts only if `B` has a nonzero left kernel vector.
* `ev_preimage_long_le`: with a smooth `B`, some entry of `K` reaches `τ √m` with probability at
  most `k · 3 · 2^{−m}`.
* `ev_E_long_le`: some entry of `E` reaches `σ √m` with probability at most `m · 6 · 4^{−m}`.
* `real_accept`: the attack accepts a real sample whose `K`, `E`, `T` are good.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib.Probability ProbabilityTheory ZLattice MeasureTheory
open scoped ENNReal Matrix

/-! ### The empty word -/

theorem foldr_bit_replicate (W : ℕ) : (List.replicate W false).foldr Nat.bit 0 = 0 := by
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ, ih]

theorem entryAt_nil (κ idx : ℕ) : entryAt κ [] idx = 0 := by
  unfold entryAt Cslib.Matrix.binaryEntry Cslib.BitString.listRow
  simp

theorem parityOut_nil (κ : ℕ) : parityOut κ [] = true := by
  have hw : ∀ j, wAt κ [] j = 0 := by
    intro j
    unfold wAt cAt kAt auxAt qOf
    simp [entryAt_nil]
  unfold parityOut
  simp [hw]

/-! ### Supports -/

section
variable {n m q : ℕ}

theorem cosetGauss_support (B : Matrix (Fin n) (Fin m) (ZMod q)) (u : Fin n → ZMod q) {τ : ℝ}
    (hτ : 0 < τ) {p : PMF (Fin m → ℤ)} (hp : cosetGauss B u τ hτ = some p) {x : Fin m → ℤ}
    (hx : x ∈ p.support) : B *ᵥ (fun i => (x i : ZMod q)) = u := by
  unfold cosetGauss at hp
  split_ifs at hp with h
  obtain rfl := Option.some.inj hp
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz' : z ∈ (perp B : Set (EuclideanSpace ℝ (Fin m))) := by
    have hz2 : z ∈ ((ZLattice.discreteGaussian (perp B) τ hτ (-(embed m h.choose))).map
        Subtype.val).support := hz
    rw [PMF.mem_support_map_iff] at hz2
    obtain ⟨w, -, rfl⟩ := hz2
    exact w.2
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz'
  rw [toInt_embed]
  have hk : B *ᵥ (fun i => (y i : ZMod q)) = 0 := hy
  have : (fun i => ((h.choose + y) i : ZMod q)) =
      (fun i => (h.choose i : ZMod q)) + fun i => (y i : ZMod q) := by
    funext i; simp
  rw [this, Matrix.mulVec_add, h.choose_spec, hk, add_zero]

theorem cosetGauss_isSome [Fact q.Prime] (B : Matrix (Fin n) (Fin m) (ZMod q))
    (hB : ∀ y, y ᵥ* B = 0 → y = 0) (u : Fin n → ZMod q) {τ : ℝ} (hτ : 0 < τ) :
    cosetGauss B u τ hτ ≠ none := by
  obtain ⟨x, hx⟩ := surj_of_ker B hB u
  have hex : ∃ x0 : Fin m → ℤ, B *ᵥ (fun i => (x0 i : ZMod q)) = u :=
    ⟨fun i => ((x i).val : ℤ), by simpa [ZMod.natCast_zmod_val] using hx⟩
  unfold cosetGauss
  rw [dif_pos hex]
  simp

end

section
variable {κ : ℕ}

/-- The columns listed by `preimage`. -/
noncomputable def colDists (d : Draw κ) : List (Option (PMF (Fin (m κ) → ℤ))) :=
  (List.finRange (k κ)).map fun j => cosetGauss d.B (fun i => d.P i j) (τ κ) (τ_pos κ)

/-- The matrix with the given columns. -/
def ofCols (cols : List (Fin (m κ) → ℤ)) : Matrix (Fin (m κ)) (Fin (k κ)) ℤ :=
  fun r j => (cols.getD j.val 0) r

theorem preimage_eq (d : Draw κ) :
    preimage d = (sampleOptList (colDists d)).map (Option.map ofCols) := rfl

theorem preimage_support (d : Draw κ) {K : Matrix (Fin (m κ)) (Fin (k κ)) ℤ}
    (hK : some K ∈ (preimage d).support) (j : Fin (k κ)) :
    d.B *ᵥ (fun r => (K r j : ZMod (q κ))) = fun i => d.P i j := by
  rw [preimage_eq, PMF.mem_support_map_iff] at hK
  obtain ⟨o, ho, hoK⟩ := hK
  have hs := support_sampleOptList _ o ho
  cases o with
  | none => simp at hoK
  | some cols =>
    simp only [Option.map_some, Option.some.injEq] at hoK
    subst hoK
    have hlen := hs.length_eq
    have hj : j.val < cols.length := by rw [hlen]; simp [colDists]
    have hj' : j.val < (colDists d).length := by simp [colDists]
    obtain ⟨p, hp, hx⟩ := hs.get hj hj'
    simp only [List.get_eq_getElem, colDists, List.getElem_map, List.getElem_finRange] at hp
    have := cosetGauss_support d.B _ (τ_pos κ) hp hx
    convert this using 2 <;>
      first | rfl | simp [ofCols, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- The experiment aborts only if `B` has a nonzero left kernel vector. -/
theorem ev_preimage_none_le (d : Draw κ) :
    ev (preimage d) (fun K? => ind (K? = none)) ≤ ind (∃ y ≠ 0, y ᵥ* d.B = 0) := by
  by_cases hB : ∃ y ≠ 0, y ᵥ* d.B = 0
  · rw [ind_of hB]; exact ev_le_const _ fun _ => ind_le_one _
  · rw [ind_of_not hB]
    have hB' : ∀ y, y ᵥ* d.B = 0 → y = 0 := fun y hy => by
      by_contra h0; exact hB ⟨y, h0, hy⟩
    refine (ev_mono_supp _ fun K? hK? => ?_).trans (ev_const _ 0).le
    rw [ind_of_not]
    rintro rfl
    rw [preimage_eq, PMF.mem_support_map_iff] at hK?
    obtain ⟨o, ho, hon⟩ := hK?
    cases o with
    | some _ => simp at hon
    | none =>
      have := support_sampleOptList _ none ho
      simp only [colDists, List.mem_map, List.mem_finRange, true_and] at this
      obtain ⟨j, hj⟩ := this
      exact cosetGauss_isSome d.B hB' _ (τ_pos κ) hj

theorem ev_ind_mem (p : PMF α) (S : Set α) : ev p (fun a => ind (a ∈ S)) = p.toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_apply]
  unfold ev
  refine tsum_congr fun a => ?_
  unfold ind; simp only [Set.indicator_apply]; split_ifs <;> simp

theorem m_pos (κ : ℕ) : 0 < m κ := by unfold m n w; positivity

/-- With a smooth `B`, some entry of `K` reaches `τ √m` with probability at most `k · 3 · 2^{−m}`. -/
theorem ev_preimage_long_le (d : Draw κ) (hB : dualMassE d.B (τ κ) ≤ 1 / 2) :
    ev (preimage d) (fun K? => match K? with
      | none => 0
      | some K => ind (∃ r j, τ κ * Real.sqrt (m κ) ≤ |((K r j : ℤ) : ℝ)|)) ≤
      (k κ : ℝ≥0∞) * ENNReal.ofReal (3 * (1 / 2) ^ m κ) := by
  rw [preimage_eq, ev_map]
  have hlen : (colDists d).length = k κ := by simp [colDists]
  refine (le_trans (ev_mono _ fun o => ?_) (ev_sampleOptList_exists
    (fun x : Fin (m κ) → ℤ => τ κ * Real.sqrt (m κ) ≤ ‖embed (m κ) x‖) (colDists d) ?_)).trans
    (le_of_eq (by rw [hlen]))
  · cases o with
    | none => simp
    | some cols =>
      simp only [Function.comp_apply, Option.map_some]
      refine ind_mono ?_
      rintro ⟨r, j, h⟩
      unfold ofCols at h
      by_cases hj : j.val < cols.length
      · refine ⟨cols[j.val], List.getElem_mem hj, h.trans ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h ⊢
        exact abs_le_norm_embed _ r
      · rw [List.getD_eq_default _ _ (by omega)] at h
        have : 0 < τ κ * Real.sqrt (m κ) :=
          mul_pos (τ_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
        simp at h; linarith
  · intro x hx p hp
    simp only [colDists, List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    exact (le_of_eq (ev_ind_mem p {x | τ κ * Real.sqrt (m κ) ≤ ‖embed (m κ) x‖})).trans
      (cosetGauss_tail d.B _ (τ_pos κ) hB hp)

theorem one_le_σ (κ : ℕ) : 1 ≤ σ κ := by unfold σ; exact one_le_pow₀ (by norm_num)

/-- Some entry of `E` reaches `σ √m` with probability at most `m · 6 · 4^{−m}`. -/
theorem ev_E_long_le :
    ev (sampleMat (gaussZ (σ κ) (σ_pos κ)) (ell κ) (m κ))
      (fun E => ind (∃ i r, σ κ * Real.sqrt (m κ) ≤ |((E i r : ℤ) : ℝ)|)) ≤
      (m κ : ℝ≥0∞) * ENNReal.ofReal (6 * (1 / 4) ^ m κ) := by
  have h := ev_sampleMat_exists (gaussZ (σ κ) (σ_pos κ))
    (fun x : ℤ => σ κ * Real.sqrt (m κ) ≤ |(x : ℝ)|) ?_ (ε := ENNReal.ofReal (6 * (1 / 4) ^ m κ))
    ?_ (ell κ) (m κ)
  · simpa [ell] using h
  · have : 0 < σ κ * Real.sqrt (m κ) :=
      mul_pos (σ_pos κ) (Real.sqrt_pos.mpr (by exact_mod_cast m_pos κ))
    simp only [show (default : ℤ) = 0 from rfl, Int.cast_zero, abs_zero, not_le]; exact this
  · exact (le_of_eq (ev_ind_mem (gaussZ (σ κ) (σ_pos κ))
      {x : ℤ | σ κ * Real.sqrt (m κ) ≤ |(x : ℝ)|})).trans (gaussZ_tail (one_le_σ κ) (σ_pos κ) (m κ))

end

end TestCase.EvLWE
