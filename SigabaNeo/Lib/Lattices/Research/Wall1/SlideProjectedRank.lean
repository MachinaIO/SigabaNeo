module

public import SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
import all SigabaNeo.Lib.Lattices.Research.Wall1.AttackLattice
import Mathlib.Tactic

/-! # The height direction in the final projection (Part 143)

All ranks below are over the integers, including the ranks of image lattices.
The prefix rank is measured in the lattice intersection with its real span. -/

public section

namespace SigabaNeo.Wall1.Slide

open Module

private theorem rank_image_add_intersection {E : Type*} [AddCommGroup E]
    (L : Submodule ℤ E) [Module.Finite ℤ L] (P : E →ₗ[ℤ] E) :
    finrank ℤ (L.map P) + finrank ℤ (L ⊓ P.ker : Submodule ℤ E) = finrank ℤ L := by
  let f := P.domRestrict L
  have hr := f.ker.finrank_quotient_add_finrank
  rw [f.quotKerEquivRange.finrank_eq] at hr
  have he := (Submodule.equivMapOfInjective L.subtype L.subtype_injective f.ker).finrank_eq
  have hk : f.ker.map L.subtype = L ⊓ P.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hy, hz⟩
      exact ⟨⟨x, hy⟩, hz, rfl⟩
  rw [he, hk] at hr
  have him : f.range = L.map P := by ext x; exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, y.property, hy⟩,
      fun ⟨y, hy, he⟩ ↦ ⟨⟨y, hy⟩, he⟩⟩
  rwa [him] at hr

/-- Rank-nullity for the orthogonal projection of a lattice and its horizontal
part. A real linear height functional vanishes on the prefix, and a height-one
vector still has height one in the image. -/
theorem projected_rank_with_height {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L H : Submodule ℤ E)
    [Module.Finite ℤ L] [Module.Finite ℤ H] (W : Submodule ℝ E) (height : E →ₗ[ℝ] ℝ)
    (horizontal : W ≤ height.ker)
    (nullPart : H = L ⊓ (height.ker.restrictScalars ℤ))
    (N J : ℕ) (rankL : finrank ℤ L = N + 1) (rankH : finrank ℤ H = N)
    (rankPrefix : finrank ℤ (L ⊓ W.restrictScalars ℤ : Submodule ℤ E) = J)
    (u : E) (hu : u ∈ L) (heightOne : height u = 1) :
    let P := Wᗮ.starProjection.toLinearMap.restrictScalars ℤ
    finrank ℤ (H.map P) = N - J ∧ finrank ℤ (L.map P) = N + 1 - J ∧
    finrank ℤ (L.map P) = finrank ℤ (H.map P) + 1 ∧
    P u ∈ L.map P ∧ height (P u) = 1 := by
  let P := Wᗮ.starProjection.toLinearMap.restrictScalars ℤ
  change finrank ℤ (H.map P) = N - J ∧ finrank ℤ (L.map P) = N + 1 - J ∧
    finrank ℤ (L.map P) = finrank ℤ (H.map P) + 1 ∧ P u ∈ L.map P ∧ height (P u) = 1
  have hk : P.ker = W.restrictScalars ℤ := by
    ext x
    change Wᗮ.starProjection x = 0 ↔ x ∈ W
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  have he : H ⊓ P.ker = L ⊓ P.ker := by
    rw [nullPart, inf_assoc, hk, inf_eq_right.mpr (show W.restrictScalars ℤ ≤
      height.ker.restrictScalars ℤ from fun _ h ↦ horizontal h)]
  have hL := rank_image_add_intersection L P
  have hH := rank_image_add_intersection H P
  rw [he, hk, rankPrefix, rankH] at hH
  rw [hk, rankPrefix, rankL] at hL
  refine ⟨by omega, by omega, by omega, ⟨u, hu, rfl⟩, ?_⟩
  have hw : u - P u ∈ W := by
    simp [P]
  have hz := horizontal hw
  change height (u - P u) = 0 at hz
  rw [map_sub, heightOne] at hz
  linarith

open AttackLattice DecoupledDecoder

private theorem modular_kernel_rank {k m q : ℕ} [NeZero q]
    (f : (Fin k → ℤ) →+ (Fin m → ZMod q)) :
    let L := (f.ker.map (intEmb k)).toIntSubmodule
    Module.Finite ℤ L ∧ finrank ℤ L = k := by
  let K := f.ker.toIntSubmodule
  let mulQ : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℤ) := (q : ℤ) • LinearMap.id
  have hm (x : Fin k → ℤ) : mulQ x ∈ K := by
    change f ((q : ℤ) • x) = 0
    rw [map_zsmul]
    ext i; simp [Pi.smul_apply, zsmul_eq_mul]
  let incl := mulQ.codRestrict K hm
  have hin : Function.Injective incl := by
    intro x y h
    have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
    funext i
    have hh := congrArg (fun z : K ↦ (z : Fin k → ℤ) i) h
    exact mul_left_cancel₀ hq (show (q : ℤ) * x i = (q : ℤ) * y i from hh)
  have hlo := LinearMap.finrank_le_finrank_of_injective (f := incl) hin
  have hhi := LinearMap.finrank_le_finrank_of_injective (f := K.subtype) K.subtype_injective
  have hj : Function.Injective (intEmb k) := by
    intro x y h
    funext i
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin k) ↦ z i) h
    change (x i : ℝ) = y i at he
    exact_mod_cast he
  let eK := Submodule.equivMapOfInjective (intEmb k).toIntLinearMap hj K
  refine ⟨Module.Finite.equiv eK, ?_⟩
  change finrank ℤ (K.map (intEmb k).toIntLinearMap) = k
  rw [← eK.finrank_eq]
  simpa using le_antisymm hhi hlo

/-- For the concrete Part 47 projection, an ordered null-lattice basis of length J+d=N
gives integer ranks d and d+1. This holds for every observed right-hand side. -/
theorem canonical_projected_ranks {N m n q J d : ℕ} [NeZero q]
    (A : Fin m → Fin n → ZMod q) (σ : Fin N ≃ Fin n ⊕ Fin m) (b : Fin m → ZMod q)
    (hd : J + d = N) (B : Basis (Fin (J+d)) ℤ (nullLattice A σ)) :
    let P := (perpProj (prefixOf B).b J).toLinearMap.restrictScalars ℤ
    finrank ℤ ((nullLattice₀ A σ).toIntSubmodule.map P) = d ∧
    finrank ℤ ((attackLattice A σ b).toIntSubmodule.map P) = d+1 ∧
    ∃ v ∈ (attackLattice A σ b).toIntSubmodule.map P, v (Fin.last N) = 1 := by
  let L := (attackLattice A σ b).toIntSubmodule
  let H := (nullLattice₀ A σ).toIntSubmodule
  let W := prefixSpan (prefixOf B).b J
  let height := (LinearMap.proj (R := ℝ) (Fin.last N)).comp
    (WithLp.linearEquiv 2 ℝ (Fin (N+1) → ℝ)).toLinearMap
  have hor : W ≤ height.ker := by
    change prefixSpan (canonicalPrefix (basisVec B)).b J ≤ _
    rw [prefixSpan_canonical]
    rintro _ ⟨x, _, rfl⟩
    change (snocE x 0) (Fin.last N) = 0
    exact snocE_last _ _
  have nullPart : H = L ⊓ height.ker.restrictScalars ℤ := by
    ext x
    exact mem_nullLattice₀_iff A σ b x
  obtain ⟨hfiniteL, hL⟩ := modular_kernel_rank (attackResidue A σ b)
  let : Module.Finite ℤ L := hfiniteL
  let S := (nullLattice A σ).toIntSubmodule
  let : Module.Finite ℤ S := Module.Finite.of_basis B
  let eH := Submodule.equivMapOfInjective ((horiz N).restrictScalars ℤ) horiz_injective S
  let : Module.Finite ℤ H := Module.Finite.equiv eH
  have hH : finrank ℤ H = N := by
    change finrank ℤ (S.map ((horiz N).restrictScalars ℤ)) = N
    rw [← eH.finrank_eq]
    let BS : Basis (Fin (J+d)) ℤ S := B
    simpa [hd] using Module.finrank_eq_card_basis BS
  have hK : L ⊓ W.restrictScalars ℤ = (prefixLattice (prefixOf B).b J).toIntSubmodule := by
    have he : L ⊓ W.restrictScalars ℤ = H ⊓ W.restrictScalars ℤ := by
      rw [nullPart, inf_assoc, inf_eq_right.mpr (show W.restrictScalars ℤ ≤
        height.ker.restrictScalars ℤ from fun _ h ↦ hor h)]
    rw [he]
    exact congrArg AddSubgroup.toIntSubmodule (nullLattice₀_inf_prefixSpan hd B)
  have hpre : finrank ℤ (L ⊓ W.restrictScalars ℤ : Submodule ℤ _) = J := by
    rw [hK]
    have li := (basisVec_linearIndependent hd B).comp (Fin.castAdd d) (Fin.castAdd_injective J d)
    have li' : LinearIndependent ℝ (fun i : Fin J ↦ (prefixOf B).b i) := by
      simpa only [prefixOf, canonicalPrefix_b, preVec, Function.comp_def] using
        li.map' (horiz N) (LinearMap.ker_eq_bot.mpr horiz_injective)
    change finrank ℤ (Submodule.span ℤ (Set.range fun i : Fin J ↦ (prefixOf B).b i)) = J
    rw [finrank_span_eq_card (li'.restrict_scalars' ℤ), Fintype.card_fin]
  let z : Fin (N+1) → ℤ := Fin.snoc (α := fun _ ↦ ℤ)
    (fun i : Fin N ↦ (σ i).elim (fun _ ↦ 0) (fun a ↦ (b a).val)) 1
  have hu : intEmb (N+1) z ∈ L := by
    refine ⟨z, AddMonoidHom.mem_ker.mpr ?_, rfl⟩
    ext a
    simp [attackResidue_apply, z]
  have hone : height (intEmb (N+1) z) = 1 := by
    change ((z (Fin.last N) : ℤ) : ℝ) = 1
    simp [z]
  obtain ⟨hh, hl, _, hm, hv⟩ := projected_rank_with_height L H W height hor nullPart N J
    hL hH hpre _ hu hone
  refine ⟨hh.trans (by omega), hl.trans (by omega), _, hm, hv⟩

end SigabaNeo.Wall1.Slide

#print axioms SigabaNeo.Wall1.Slide.projected_rank_with_height
#print axioms SigabaNeo.Wall1.Slide.canonical_projected_ranks
