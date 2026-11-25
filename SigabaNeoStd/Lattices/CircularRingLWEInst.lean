import SigabaNeoStd.Lattices.CircularRingLWE
import SigabaNeoStd.Lattices.RingLWEInst

/-!
# Circular Ring-LWE instances over `ℤ_q[X]/(X^N + 1)`

The registry's circular Ring-LWE laws (`CircularRingLWE.realLaw`, `idealLaw`: Module-LWE pairs of
rank `1` with `p.rows` rows, encoded by `encodeSample`) as laws on ring elements:

* `CircularRingLWE.circRing p`: `σ ← polyOf χ_s`, uniform `aᵣ`, errors `eᵣ ← polyOf χ_e`, and the
  pairs `(aᵣ, aᵣ σ + eᵣ − keyShiftRing p σ r)` (the key shift of row `r`: `0` on the plain rows,
  `2^i σ_k(σ)` on row `i` of the key of index `k`);
* `realLaw_eq_circRing`: `realLaw p = (circRing p).map encodeRing`;
  `idealLaw_eq_uniform`: `idealLaw p` is the encoding of uniform ring-level pairs.

Independent products split along sums, units and products of index types (`pi_sum_bind`,
`pi_unit_bind`, `pi_prod_bind`), for the reindexing of instances by applications.
-/

namespace SigabaNeo.Lattices

open Cslib Cslib.Probability

/-- Independent coordinates over a sum: the two parts independently. -/
theorem pi_sum_eq {α β X : Type} [Fintype α] [Fintype β] [Finite X] (d : PMF X) :
    (PMF.pi fun _ : α ⊕ β => d) =
      (PMF.pi fun _ : α => d).bind fun a => (PMF.pi fun _ : β => d).map fun b => Sum.elim a b := by
  ext x
  rw [PMF.bind_apply, tsum_eq_single (x ∘ Sum.inl)]
  · rw [PMF.map_apply, tsum_eq_single (x ∘ Sum.inr)]
    · rw [if_pos (by funext i; cases i <;> rfl), PMF.pi_apply, PMF.pi_apply, PMF.pi_apply,
        Fintype.prod_sum_type]
      rfl
    · intro b hb
      rw [if_neg]
      intro h
      exact hb (funext fun j => by rw [h]; rfl)
  · intro a ha
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr fun b => if_neg fun h =>
      ha (funext fun i => by rw [h]; rfl), mul_zero]

theorem pi_sum_bind {α β γ X : Type} [Fintype α] [Fintype β] [Finite X] (d : PMF X)
    (g : (α ⊕ β → X) → PMF γ) :
    (PMF.pi fun _ : α ⊕ β => d).bind g =
      (PMF.pi fun _ : α => d).bind fun a => (PMF.pi fun _ : β => d).bind fun b => g (Sum.elim a b) := by
  rw [pi_sum_eq, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

/-- Independent coordinates over `Unit`: one draw. -/
theorem pi_unit_eq {X : Type} [Finite X] (d : PMF X) :
    (PMF.pi fun _ : Unit => d) = d.map fun x _ => x := by
  ext f
  rw [PMF.map_apply, tsum_eq_single (f ()), if_pos (funext fun u => rfl), PMF.pi_apply]
  · simp
  · intro x hx
    rw [if_neg]
    intro h
    exact hx (by rw [h])

theorem pi_unit_bind {γ X : Type} [Finite X] (d : PMF X) (g : (Unit → X) → PMF γ) :
    (PMF.pi fun _ : Unit => d).bind g = d.bind fun x => g fun _ => x := by
  rw [pi_unit_eq, PMF.bind_map]; rfl

/-- Independent coordinates over a product: independent rows. -/
theorem pi_prod_bind {ι κ γ X : Type} [Fintype ι] [Fintype κ] [Finite X] (d : PMF X)
    (g : (ι × κ → X) → PMF γ) :
    (PMF.pi fun _ : ι × κ => d).bind g =
      (PMF.pi fun _ : ι => PMF.pi fun _ : κ => d).bind fun f => g fun ij => f ij.1 ij.2 := by
  rw [← pi_curry, PMF.bind_map]; rfl

namespace CircularRingLWE

variable (p : Params)

/-- The ring of the parameters. -/
abbrev Ring := Negacyclic (ZMod p.base.q) p.base.N

/-- **The key shift of row `r` as a ring element**: `0` on the plain rows, `2^i σ_k(σ)` on row `i`
of the key of the `j`-th index `k = J[j]`. -/
def keyShiftRing (σ : Ring p) (r : Fin p.rows) : Ring p :=
  Negacyclic.ofCoeffs (keyShift p σ.coeffs r)

/-- **Real circular pairs over the ring.** -/
noncomputable def circRing : PMF ((Fin p.rows → Ring p) × (Fin p.rows → Ring p)) :=
  (polyOf (N := p.base.N) (ModuleLWE.coeffLaw p.base.q p.base.secret)).bind fun σ =>
  (PMF.uniformOfFintype (Fin p.rows → Ring p)).bind fun A =>
  (PMF.pi fun _ : Fin p.rows => polyOf (N := p.base.N) (ModuleLWE.coeffLaw p.base.q p.base.error)).map
    fun e => (A, fun r => A r * σ + e r - keyShiftRing p σ r)

/-- Real pairs with a shift, generic in the sizes: the Module-LWE form is the ring-level form. -/
theorem sampleShift_eq {N q m : ℕ} [NeZero q] (χs χe : PMF (ZMod q))
    (sh : (Fin N → ZMod q) → Fin m → Fin N → ZMod q) :
    ((sampleMat χs 1 N).bind fun s =>
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin 1) (Fin N → ZMod q))).bind fun A =>
      (sampleMat χe m N).bind fun e => PMF.pure (A, Cslib.Crypto.ModuleLWE.sample A s e - sh (s 0))) =
    ((polyOf (N := N) χs).bind fun σ =>
      (PMF.uniformOfFintype (Fin m → Negacyclic (ZMod q) N)).bind fun A =>
      (PMF.pi fun _ : Fin m => polyOf (N := N) χe).map fun e =>
        (A, fun r => A r * σ + e r - Negacyclic.ofCoeffs (sh σ.coeffs r))).map coeffPair := by
  have h1 : sampleMat χs 1 N = (polyOf (N := N) χs).map fun σ =>
      (Matrix.of fun _ j => σ.coeffs j : Matrix (Fin 1) (Fin N) (ZMod q)) := sampleMat_one_eq χs
  have h2 : sampleMat χe m N = (PMF.pi fun _ : Fin m => polyOf (N := N) χe).map fun e =>
      (Matrix.of fun i j => (e i).coeffs j : Matrix (Fin m) (Fin N) (ZMod q)) :=
    sampleMat_eq_polyOf χe m
  rw [h1, h2, uniform_coeffs]
  simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg _ (funext fun σ => ?_)
  refine congrArg _ (funext fun A => ?_)
  rw [← PMF.bind_pure_comp]
  refine congrArg _ (funext fun e => ?_)
  simp only [coeffPair, Function.comp_apply]
  congr 2
  funext i
  simp only [Cslib.Crypto.ModuleLWE.sample, Negacyclic.coeffs_sub, Negacyclic.coeffs_add,
    Negacyclic.coeffs_mul, Pi.sub_apply]
  show (Cslib.Crypto.moduleSISMap (Matrix.of fun i _ => (A i).coeffs)
    (Matrix.of fun _ j => σ.coeffs j) i + (e i).coeffs) - sh σ.coeffs i = _
  rw [show Cslib.Crypto.moduleSISMap (Matrix.of fun i _ => (A i).coeffs)
    (Matrix.of fun _ j => σ.coeffs j) i = negacyclicMul (A i).coeffs σ.coeffs from
      Fin.sum_univ_one _]

/-- **The registry's real circular pairs are the ring-level pairs.** -/
theorem sampleLaw_eq_circRing : sampleLaw p = (circRing p).map coeffPair :=
  sampleShift_eq _ _ (keyShift p)

/-- **The registry's real law** is that of the encoded ring-level pairs. -/
theorem realLaw_eq_circRing : realLaw p = (circRing p).map encodeRing :=
  (congrArg (PMF.map Cslib.Crypto.ModuleLWE.encodeSample) (sampleLaw_eq_circRing p)).trans
    (PMF.map_comp _ _ _)

/-- **The registry's uniform law** is that of encoded uniform ring-level pairs. -/
theorem idealLaw_eq_uniform :
    idealLaw p =
      (PMF.uniformOfFintype ((Fin p.rows → Ring p) × (Fin p.rows → Ring p))).map encodeRing :=
  (congrArg (PMF.map _) (uniform_pair_eq (N := p.base.N) (q := p.base.q) p.rows)).trans
    (PMF.map_comp _ _ _)

end CircularRingLWE

end SigabaNeo.Lattices
