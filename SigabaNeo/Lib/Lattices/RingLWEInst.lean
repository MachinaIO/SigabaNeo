import SigabaNeo.Lib.Lattices.RingLWE
import SigabaNeo.Lib.Lattices.Stat
import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# Ring-LWE instances over `ℤ_q[X]/(X^N + 1)`

The registry's Ring-LWE (`RingLWE.decision`, Module-LWE of rank `1`) draws coefficient vectors
with `sampleMat`. Here the same laws as laws on ring elements:

* `sampleMat_eq_pi`: `sampleMat` is the independent product, reindexed;
* `pi_comp_equiv`, `pi_curry`: independent products are invariant under reindexing and currying;
* `ringReal`: real pairs `(aᵢ, aᵢ σ + eᵢ)` over the ring; `ringLWE_realLaw_eq`,
  `ringLWE_idealLaw_eq`: the registry's laws are the encoded ring-level laws (`encodeRing`).
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability

/-- Independent identically distributed coordinates are invariant under reindexing. -/
theorem pi_comp_equiv {ι κ α : Type} [Fintype ι] [Fintype κ] [Finite α] (d : PMF α)
    (e : κ ≃ ι) :
    (PMF.pi fun _ : ι => d).map (fun v => v ∘ e) = PMF.pi fun _ : κ => d := by
  classical
  ext w
  rw [PMF.map_apply, tsum_eq_single (w ∘ e.symm)]
  · rw [if_pos (by funext k; simp), PMF.pi_apply, PMF.pi_apply]
    exact Fintype.prod_equiv e.symm _ _ (fun i => rfl)
  · intro v hv
    rw [if_neg]
    intro h
    exact hv (by funext i; rw [h]; simp)

/-- `sampleMat` is the independent product over the entries. -/
theorem sampleMat_eq_pi {α : Type} [Inhabited α] [Finite α] (d : PMF α) (r c : ℕ) :
    sampleMat d r c = (PMF.pi fun _ : Fin r × Fin c => d).map fun v => Matrix.of fun i j => v (i, j) := by
  unfold sampleMat
  have h := sampleList_pi d id (r * c)
  simp only [id, PMF.map_id] at h
  rw [← pi_comp_equiv d finProdFinEquiv, ← h, PMF.map_comp, PMF.map_comp]
  congr 1
  funext l
  ext i j
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Independent coordinates over a product are independent rows of independent coordinates. -/
theorem pi_curry {ι κ α : Type} [Fintype ι] [Fintype κ] [Finite α] (d : PMF α) :
    (PMF.pi fun _ : ι × κ => d).map (fun v i j => v (i, j)) =
      PMF.pi fun _ : ι => PMF.pi fun _ : κ => d := by
  classical
  ext w
  rw [PMF.map_apply, tsum_eq_single (fun ij => w ij.1 ij.2)]
  · rw [if_pos rfl, PMF.pi_apply, PMF.pi_apply, Fintype.prod_prod_type]
    simp only [PMF.pi_apply]
  · intro v hv
    rw [if_neg]
    intro h
    exact hv (by funext ij; rw [h])

variable {N q : ℕ} [NeZero q]

/-- A ring element with independent coefficients from `χ`. -/
noncomputable def polyOf (χ : PMF (ZMod q)) : PMF (Negacyclic (ZMod q) N) :=
  (PMF.pi fun _ : Fin N => χ).map Negacyclic.ofCoeffs

/-- The coefficient vectors of a ring-level pair, as a Module-LWE pair of rank `1`. -/
def coeffPair {m : ℕ}
    (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) :
    Matrix (Fin m) (Fin 1) (Fin N → ZMod q) × (Fin m → Fin N → ZMod q) :=
  (Matrix.of fun i _ => (v.1 i).coeffs, fun i => (v.2 i).coeffs)

/-- A ring-level pair encoded as the registry encodes Module-LWE pairs. -/
def encodeRing {m : ℕ}
    (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) : List Bool :=
  Cslib.Crypto.ModuleLWE.encodeSample (coeffPair v)

/-- **Real Ring-LWE pairs over the ring**: uniform `aᵢ`, and `aᵢ σ + eᵢ` for a secret `σ` and
errors `eᵢ` with independent coefficients from `χs`, `χe`. -/
noncomputable def ringReal (m : ℕ) (χs χe : PMF (ZMod q)) :
    PMF ((Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) := do
  let σ ← polyOf (N := N) χs
  let A ← PMF.uniformOfFintype (Fin m → Negacyclic (ZMod q) N)
  let e ← PMF.pi fun _ : Fin m => polyOf (N := N) χe
  pure (A, fun i => A i * σ + e i)

theorem sampleMat_one_eq (χ : PMF (ZMod q)) :
    sampleMat χ 1 N = (polyOf (N := N) χ).map fun σ _ => σ.coeffs := by
  rw [sampleMat_eq_pi, polyOf, PMF.map_comp,
    ← pi_comp_equiv χ (Equiv.uniqueProd (Fin N) (Fin 1)).symm, PMF.map_comp]
  congr 1
  funext v
  ext i j
  fin_cases i
  rfl

theorem sampleMat_eq_polyOf (χ : PMF (ZMod q)) (m : ℕ) :
    sampleMat χ m N = (PMF.pi fun _ : Fin m => polyOf (N := N) χ).map fun e i => (e i).coeffs := by
  rw [sampleMat_eq_pi]
  unfold polyOf
  rw [Cslib.Probability.PMF.pi_map, ← pi_curry, PMF.map_comp, PMF.map_comp]
  rfl

theorem uniform_coeffs (m : ℕ) :
    PMF.uniformOfFintype (Matrix (Fin m) (Fin 1) (Fin N → ZMod q)) =
      (PMF.uniformOfFintype (Fin m → Negacyclic (ZMod q) N)).map
        fun A => Matrix.of fun i _ => (A i).coeffs := by
  let e : (Fin m → Negacyclic (ZMod q) N) ≃ Matrix (Fin m) (Fin 1) (Fin N → ZMod q) :=
    { toFun := fun A => Matrix.of fun i _ => (A i).coeffs
      invFun := fun M i => Negacyclic.ofCoeffs (M i 0)
      left_inv := fun A => rfl
      right_inv := fun M => by ext i j; fin_cases j; rfl }
  exact (Cslib.Probability.PMF.uniformOfFintype_map_equiv e).symm

/-- **The registry's real Module-LWE pairs of rank `1` are the ring-level pairs.** -/
theorem sampleLaw_eq_ringReal (m : ℕ) (χs χe : PMF (ZMod q)) :
    Cslib.Crypto.ModuleLWE.sampleLaw (sampleMat χs 1 N) (sampleMat χe m N) =
      (ringReal m χs χe).map coeffPair := by
  unfold Cslib.Crypto.ModuleLWE.sampleLaw ringReal
  rw [sampleMat_one_eq, sampleMat_eq_polyOf, uniform_coeffs]
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  congr 1; funext σ
  congr 1; funext A
  congr 1; funext e
  simp only [coeffPair]
  congr 2
  funext i
  simp [Cslib.Crypto.ModuleLWE.sample, Cslib.Crypto.moduleSISMap, Negacyclic.coeffs_mul]

/-- Uniform Module-LWE pairs of rank `1` are uniform ring-level pairs. -/
theorem uniform_pair_eq (m : ℕ) :
    PMF.uniformOfFintype (Matrix (Fin m) (Fin 1) (Fin N → ZMod q) × (Fin m → Fin N → ZMod q)) =
      (PMF.uniformOfFintype ((Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N))).map
        coeffPair := by
  let e : ((Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) ≃
      (Matrix (Fin m) (Fin 1) (Fin N → ZMod q) × (Fin m → Fin N → ZMod q)) :=
    { toFun := coeffPair
      invFun := fun M => (fun i => Negacyclic.ofCoeffs (M.1 i 0), fun i => Negacyclic.ofCoeffs (M.2 i))
      left_inv := fun A => rfl
      right_inv := fun M => by
        refine Prod.ext ?_ rfl
        ext i j; fin_cases j; rfl }
  exact (Cslib.Probability.PMF.uniformOfFintype_map_equiv e).symm

/-- Real pairs indexed by any finite type. -/
noncomputable def ringRealOn (ι : Type) [Fintype ι] [DecidableEq ι] (χs χe : PMF (ZMod q)) :
    PMF ((ι → Negacyclic (ZMod q) N) × (ι → Negacyclic (ZMod q) N)) := do
  let σ ← polyOf (N := N) χs
  let A ← PMF.uniformOfFintype (ι → Negacyclic (ZMod q) N)
  let e ← PMF.pi fun _ : ι => polyOf (N := N) χe
  pure (A, fun i => A i * σ + e i)

/-- **Reindexing real pairs.** -/
theorem ringReal_reindex {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (e : ι ≃ Fin m)
    (χs χe : PMF (ZMod q)) :
    (ringReal (N := N) m χs χe).map (fun v => (v.1 ∘ e, v.2 ∘ e)) = ringRealOn ι χs χe := by
  unfold ringReal ringRealOn
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  congr 1; funext σ
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (Equiv.arrowCongr e.symm (Equiv.refl (Negacyclic (ZMod q) N))), PMF.bind_map]
  congr 1; funext A
  rw [← pi_comp_equiv (polyOf (N := N) χe) e]
  simp only [Function.comp_apply, PMF.bind_map]
  rfl

/-- Uniform pairs reindexed are uniform. -/
theorem uniform_reindex {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (e : ι ≃ Fin m) :
    (PMF.uniformOfFintype ((Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N))).map
        (fun v => (v.1 ∘ e, v.2 ∘ e)) =
      PMF.uniformOfFintype ((ι → Negacyclic (ZMod q) N) × (ι → Negacyclic (ZMod q) N)) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv
    ((Equiv.arrowCongr e.symm (Equiv.refl _)).prodCongr (Equiv.arrowCongr e.symm (Equiv.refl _)))

/-- **The registry's real Ring-LWE law** is that of the encoded ring-level pairs. -/
theorem ringLWE_realLaw_eq (p : RingLWE.Params) :
    haveI : NeZero p.q := ⟨p.q_pos.ne'⟩
    ModuleLWE.realLaw p.toModule =
      (ringReal p.m (ModuleLWE.coeffLaw p.q p.secret) (ModuleLWE.coeffLaw p.q p.error)).map
        (encodeRing (N := p.N)) := by
  have : NeZero p.q := ⟨p.q_pos.ne'⟩
  unfold ModuleLWE.realLaw ModuleLWE.secretLaw ModuleLWE.errorLaw
  exact (congrArg (PMF.map _) (sampleLaw_eq_ringReal (N := p.N) p.m _ _)).trans (PMF.map_comp _ _ _)

/-- **The registry's uniform Ring-LWE law** is that of encoded uniform ring-level pairs. -/
theorem ringLWE_idealLaw_eq (p : RingLWE.Params) :
    haveI : NeZero p.q := ⟨p.q_pos.ne'⟩
    ModuleLWE.idealLaw p.toModule =
      (PMF.uniformOfFintype ((Fin p.m → Negacyclic (ZMod p.q) p.N) ×
        (Fin p.m → Negacyclic (ZMod p.q) p.N))).map (encodeRing (N := p.N)) := by
  have : NeZero p.q := ⟨p.q_pos.ne'⟩
  unfold ModuleLWE.idealLaw
  exact (congrArg (PMF.map _) (uniform_pair_eq (N := p.N) p.m)).trans (PMF.map_comp _ _ _)

end SigabaNeo.Lattices
