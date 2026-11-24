import PE.Impl.ExpLUT.Laws
import SigabaNeo.Lib.Lattices.LeftoverHash

/-!
# Laws used by the hybrids

Generic facts about uniform laws and independent products used by the hybrids of the proof of
Theorem 2 (`PE.Impl.ExpLUT.Hybrid*`):

* `bind_uniform_equiv`, `uniform_bind_add`: a uniform draw is invariant under bijections and
  translations;
* `uniform_map_fst`, `uniform_fin2_row0`: marginals of uniform laws are uniform;
* `pi_sum'`, `uniform_sum_bind`: independent coordinates over a sum type;
* `closeTo_binaryHash_bind_mid`: **the leftover hash lemma with coins in between**: the seed `A`,
  further independent coins `c ← μ`, then the hashes `A · xᵢ`;
* `bitLaw`, `iidFam_bitLaw`: the binary trapdoor `T ∈ {0,1}^{m̄ × τ}` as `τ` uniform binary columns.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

theorem bind_uniform_equiv {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (g : β → PMF γ) :
    (PMF.uniformOfFintype α).bind (fun a => g (e a)) = (PMF.uniformOfFintype β).bind g := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  rfl

theorem uniform_bind_add {α γ : Type} [Fintype α] [Nonempty α] [AddGroup α] (c : α)
    (g : α → PMF γ) :
    (PMF.uniformOfFintype α).bind (fun u => g (u + c)) = (PMF.uniformOfFintype α).bind g :=
  bind_uniform_equiv (Equiv.addRight c) g

theorem uniform_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv e

/-- The first marginal of a uniform pair is uniform. -/
theorem uniform_map_fst {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have h : ∀ a : α, PMF.map (fun _ : β => a) (PMF.uniformOfFintype β) = PMF.pure a :=
    fun a => PMF.map_const _ _
  simp only [h, PMF.bind_pure]

/-- A uniform draw through a map that is a projection after a bijection. -/
theorem uniform_map_of_equiv_fst {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype γ] [Nonempty γ] (e : α ≃ β × γ) (f : α → β) (hf : ∀ a, f a = (e a).1) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  rw [show f = Prod.fst ∘ e from funext hf, ← PMF.map_comp, uniform_map_equiv, uniform_map_fst]

/-- The first row of a uniform pair of rows is uniform. -/
theorem uniform_fin2_row0 {R : Type} [Fintype R] [Nonempty R] :
    (PMF.uniformOfFintype (Fin 2 → R)).map (fun u => u 0) = PMF.uniformOfFintype R :=
  uniform_map_of_equiv_fst (piFinTwoEquiv fun _ => R) _ fun _ => rfl

/-- Independent coordinates over a sum: the two blocks independently. -/
theorem pi_sum' {α β γ : Type} [Fintype α] [Fintype β] [Finite γ] (μ : PMF γ) :
    Cslib.Probability.PMF.pi (fun _ : α ⊕ β => μ) =
      (Cslib.Probability.PMF.pi fun _ : α => μ).bind fun f =>
        (Cslib.Probability.PMF.pi fun _ : β => μ).map fun g => Sum.elim f g := by
  classical
  ext h
  rw [PMF.bind_apply, tsum_eq_single (fun a => h (.inl a))]
  · rw [PMF.map_apply, tsum_eq_single (fun b => h (.inr b))]
    · have : h = Sum.elim (fun a => h (.inl a)) (fun b => h (.inr b)) := by
        funext x; rcases x <;> rfl
      split_ifs
      simp only [Cslib.Probability.PMF.pi_apply, Fintype.prod_sum_type]
    · intro g hg
      split_ifs with he
      · exact absurd (funext fun b => by rw [he]; rfl) hg
      · rfl
  · intro f hf
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (tsum_eq_zero_iff.mpr fun g => ?_)
    split_ifs with he
    · exact absurd (funext fun a => by rw [he]; rfl) hf
    · rfl

/-- Uniform functions on a sum: the two blocks independently. -/
theorem uniform_sum_bind {α β γ δ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Fintype γ] [Nonempty γ] (g : (α ⊕ β → γ) → PMF δ) :
    (PMF.uniformOfFintype (α ⊕ β → γ)).bind g =
      (PMF.uniformOfFintype (α → γ)).bind fun f =>
        (PMF.uniformOfFintype (β → γ)).bind fun f' => g (Sum.elim f f') := by
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype, pi_sum', PMF.bind_bind,
    ← Cslib.Probability.PMF.pi_uniformOfFintype]
  refine congrArg (PMF.bind _) (funext fun f => ?_)
  rw [PMF.bind_map, ← Cslib.Probability.PMF.pi_uniformOfFintype]
  rfl

/-- Uniform pairs: the two components independently. -/
theorem uniform_prod_bind {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → PMF γ) :
    (PMF.uniformOfFintype (α × β)).bind g =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b => g (a, b) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

/-- **The leftover hash lemma with independent coins in between**: drawing the seed `A`, coins
`c ← μ`, then the hashes `A · xᵢ`, is within `|I| · √(|R|^r 2^{−m}) / 2` of the same experiment with
uniform values. -/
theorem closeTo_binaryHash_bind_mid {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {rr mm I C V : Type} [Fintype rr] [Fintype mm] [Fintype I] [DecidableEq rr] [DecidableEq mm]
    [DecidableEq I] [Nonempty mm] (μ : PMF C) (F : Matrix rr mm R → C → (I → rr → R) → PMF V) :
    CloseTo ((PMF.uniformOfFintype (Matrix rr mm R)).bind fun A => μ.bind fun c =>
        (Cslib.Probability.PMF.pi fun _ : I =>
          (PMF.uniformOfFintype (mm → Bool)).map (binaryHash A)).bind (F A c))
      ((PMF.uniformOfFintype (Matrix rr mm R)).bind fun A => μ.bind fun c =>
        (Cslib.Probability.PMF.pi fun _ : I => PMF.uniformOfFintype (rr → R)).bind (F A c))
      (ENNReal.ofReal
        (Fintype.card I * (Real.sqrt (Fintype.card (rr → R) * (2 ^ Fintype.card mm : ℝ)⁻¹) / 2))) := by
  have h := closeTo_binaryHash_bind (R := R) (rr := rr) (mm := mm) (I := I)
    (fun A hs => μ.bind fun c => F A c hs)
  convert h using 2 <;> funext A <;> exact PMF.bind_comm _ _ _

variable {R : Type} [CommRing R]

/-- The binary law: `0` or `1` with probability `1/2`. -/
noncomputable def bitLaw : PMF R := (PMF.uniformOfFintype Bool).map bitVal

/-- Uniform binary vectors, as ring elements. -/
theorem pi_bitLaw {ι : Type} [Fintype ι] [DecidableEq ι] [Finite R] :
    Cslib.Probability.PMF.pi (fun _ : ι => (bitLaw : PMF R)) =
      (PMF.uniformOfFintype (ι → Bool)).map fun x i => bitVal (x i) := by
  rw [bitLaw, Cslib.Probability.PMF.pi_map, Cslib.Probability.PMF.pi_uniformOfFintype]

/-- **The binary trapdoor as columns**: `T ∈ {0,1}^{m̄ × τ}` with independent binary entries is
`τ` independent uniform binary columns. -/
theorem iidFam_bitLaw [Fintype R] {Wb : Type} [Fintype Wb] [DecidableEq Wb] (τ : ℕ) :
    iidFam (bitLaw : PMF R) Wb (Fin τ) =
      (Cslib.Probability.PMF.pi fun _ : Fin τ => PMF.uniformOfFintype (Wb → Bool)).map
        fun xs w c => bitVal (xs c w) := by
  unfold iidFam iidLaw
  simp only [pi_bitLaw]
  rw [Cslib.Probability.PMF.pi_map, Cslib.Probability.PMF.pi_uniformOfFintype,
    Cslib.Probability.PMF.pi_uniformOfFintype]
  conv_rhs => rw [← uniform_map_equiv (Equiv.piComm fun (_ : Wb) (_ : Fin τ) => Bool), PMF.map_comp]
  rfl

end AdvancedEncryption.ExpLUT
