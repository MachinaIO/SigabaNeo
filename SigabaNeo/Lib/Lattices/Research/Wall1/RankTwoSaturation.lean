import SigabaNeo.Lib.Lattices.Research.Wall1.RankTwoFrames

/-! The two primitive contents characterize saturated rank-two submodules of the grid. -/

noncomputable section
open Matrix Submodule Module SigabaNeo.Rogers
namespace SigabaNeo.Wall1.RankTwo

def Saturated {V : Type*} [AddCommGroup V] (P : Submodule ℤ V) : Prop :=
  ∀ (d : ℤ), d ≠ 0 → ∀ z, d • z ∈ P → z ∈ P

def pairSpan {V : Type*} [AddCommGroup V] (x : Fin 2 → V) :=
  Submodule.span ℤ (Set.range x)

theorem pairSpan_mem {V : Type*} [AddCommGroup V] (x : Fin 2 → V) (z : V) :
    z ∈ pairSpan x ↔ ∃ s t : ℤ, s • x 0 + t • x 1 = z := by
  have he : Set.range x = {x 0, x 1} := by
    ext y; simp [Fin.exists_fin_two, eq_comm]
  rw [pairSpan, he, Submodule.mem_span_pair]

variable {m : ℕ} (hm : 2 ≤ m)
local notation "n" => (m+1)

def gridFrame (a b : ℕ) (p : Core m) := ![first a p, second (by omega : 1 ≤ m) b p]

private def axisId : Fin m := ⟨0, by omega⟩

/-- The two ambient integer changes of basis straighten both primitive marks. -/
private def chart (p : Core m) : (ℤ × IV m) ≃ₗ[ℤ] IV n :=
  (((LinearEquiv.refl ℤ ℤ).prodCongr (primitiveFrame hm p.2.2).toLin').trans
    (Fin.consLinearEquiv ℤ (fun _ : Fin n ↦ ℤ))).trans (completion (by omega) p.1)

private theorem chart_first (a : ℕ) (p : Core m) :
    chart hm p (((a+1 : ℕ) : ℤ),0) = first a p := by
  change completion (by omega) p.1 (Fin.cons _ ((primitiveFrame hm p.2.2).toLin' 0)) = _
  rw [map_zero]
  have he : (Fin.cons (((a+1 : ℕ) : ℤ)) 0 : IV n) = ((a+1 : ℕ) : ℤ) • Pi.single 0 1 := by
    funext i
    exact Fin.cases (by simp) (fun _ ↦ by simp) i
  change completion (by omega) p.1 (Fin.cons (((a+1 : ℕ) : ℤ)) 0) = _
  rw [he, map_smul, completion_axis]; rfl

private theorem chart_second (b : ℕ) (p : Core m) :
    chart hm p (p.2.1, ((b+1 : ℕ) : ℤ) • Pi.single (axisId hm) 1) =
      second (by omega) b p := by
  change completion (by omega) p.1 (Fin.cons _ ((primitiveFrame hm p.2.2).toLin' _)) = _
  rw [map_smul, show (primitiveFrame hm p.2.2).toLin' (Pi.single (axisId hm) 1) =
    p.2.2.val.val from primitiveFrame_column hm p.2.2]
  rfl

private theorem mem_chart (a b : ℕ) (p : Core m) (x : ℤ × IV m) :
    chart hm p x ∈ pairSpan (gridFrame hm a b p) ↔ ∃ s t : ℤ,
      s * (a+1 : ℕ) + t * p.2.1 = x.1 ∧
        (t * (b+1 : ℕ)) • Pi.single (axisId hm) 1 = x.2 := by
  rw [pairSpan_mem]
  apply exists_congr; intro s; apply exists_congr; intro t
  change s • first a p + t • second _ b p = _ ↔ _
  rw [← chart_first hm, ← chart_second hm, ← map_smul, ← map_smul, ← map_add,
    (chart hm p).injective.eq_iff, Prod.ext_iff]
  simp [mul_assoc]

theorem saturated_iff_contents (a b : ℕ) (p : Core m) :
    Saturated (pairSpan (gridFrame hm a b p)) ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hX : chart hm p (1,0) ∈ pairSpan (gridFrame hm a b p) := by
      apply h (a+1 : ℕ) (by positivity)
      rw [← map_smul, mem_chart]
      exact ⟨1,0,by simp,by simp⟩
    obtain ⟨s,t,hs,ht⟩ := (mem_chart hm a b p _).mp hX
    have ht0 := congrFun ht (axisId hm)
    simp [Pi.smul_apply, mul_eq_zero] at ht0
    have ht' : t = 0 := by rcases ht0 with h | h <;> omega
    simp [ht'] at hs
    have ha : a = 0 := by
      have hu := Int.isUnit_iff.mp (isUnit_of_dvd_one
        (show ((a+1 : ℕ) : ℤ) ∣ 1 from ⟨s, by simpa [mul_comm] using hs.symm⟩))
      omega
    subst a
    have hY : chart hm p (0,Pi.single (axisId hm) 1) ∈ pairSpan (gridFrame hm 0 b p) := by
      apply h (b+1 : ℕ) (by positivity)
      rw [← map_smul, mem_chart]
      exact ⟨-p.2.1,1,by simp,by simp⟩
    obtain ⟨s,t,_,ht⟩ := (mem_chart hm 0 b p _).mp hY
    have he := congrFun ht (axisId hm)
    simp [Pi.smul_apply] at he
    have hu := Int.isUnit_iff.mp (isUnit_of_dvd_one
      (show ((b+1 : ℕ) : ℤ) ∣ 1 from ⟨t, by simpa [mul_comm] using he.symm⟩))
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl,rfl⟩ d hd z hz
    obtain ⟨x,rfl⟩ := (chart hm p).surjective z
    rw [← map_smul, mem_chart] at hz
    rw [mem_chart]
    obtain ⟨s,t,_,ht⟩ := hz
    refine ⟨x.1 - x.2 (axisId hm) * p.2.1, x.2 (axisId hm), by simp, ?_⟩
    funext j
    by_cases hj : j = axisId hm
    · subst j; simp
    · have he := congrFun ht j
      have h0 : x.2 j = 0 := by
        simpa [Pi.smul_apply, Pi.single_eq_of_ne hj, hd] using he.symm
      simp [Pi.single_eq_of_ne hj,h0]

abbrev Plane (d : ℕ) :=
  {P : Submodule ℤ (IV d) // Module.finrank ℤ P = 2 ∧ Saturated P}

/-- Forget the ordered basis and retain its actual saturated integer submodule. -/
def plane (p : Core m) : Plane n :=
  ⟨pairSpan (gridFrame hm 0 0 p), by
    unfold pairSpan
    rw [finrank_span_eq_card (show LinearIndependent ℤ (gridFrame hm 0 0 p) from
      independent (by omega : 1 ≤ m) 0 0 p)]
    rfl,
   (saturated_iff_contents hm 0 0 p).mpr ⟨rfl,rfl⟩⟩

theorem primitive_basis_iff (x : Fin 2 → IV n) (hx : LinearIndependent ℤ x) :
    Saturated (pairSpan x) ↔ ∃ p, gridFrame hm 0 0 p = x := by
  let z : orderTwoIndependent n := ⟨fun i ↦ ⟨x i,hx.ne_zero i⟩,hx⟩
  obtain ⟨⟨a,b,p⟩,he⟩ := (bijective_toPair (by omega : 1 ≤ m)).surjective z
  have eqn : gridFrame hm a b p = x := congrArg
    (fun v : orderTwoIndependent n ↦ fun i ↦ (v.val i).val) he
  constructor
  · intro h
    obtain ⟨rfl,rfl⟩ := (saturated_iff_contents hm a b p).mp (eqn ▸ h)
    exact ⟨p,eqn⟩
  · rintro ⟨q,rfl⟩
    exact (plane hm q).property.2

theorem gridFrame_injective : Function.Injective (gridFrame hm 0 0) := by
  intro p q h
  have he : toPair (by omega) ((0,0,p) : Indices m) = toPair (by omega) (0,0,q) :=
    Subtype.ext (funext fun i ↦ Subtype.ext (congrFun h i))
  exact congrArg (fun z : Indices m ↦ z.2.2) ((bijective_toPair _).injective he)

theorem plane_surjective : Function.Surjective (plane hm) := by
  intro P
  let b := Module.finBasisOfFinrankEq ℤ P.val P.property.1
  let x := P.val.subtype ∘ ⇑b
  have hx : LinearIndependent ℤ x :=
    b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr P.val.injective_subtype)
  have he : pairSpan x = P.val := by
    rw [pairSpan, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      P.val.range_subtype]
  obtain ⟨p,hp⟩ := (primitive_basis_iff hm x hx).mp (he ▸ P.property.2)
  exact ⟨p, Subtype.ext ((congrArg pairSpan hp).trans he)⟩

end SigabaNeo.Wall1.RankTwo

#print axioms SigabaNeo.Wall1.RankTwo.saturated_iff_contents
#print axioms SigabaNeo.Wall1.RankTwo.primitive_basis_iff
#print axioms SigabaNeo.Wall1.RankTwo.plane_surjective
