module

public import SigabaNeo.Lib.Lattices.Research.Wall1.SelectedSlide
import all SigabaNeo.Lib.Lattices.Planted.Probability

@[expose] public section

namespace SigabaNeo.Wall1
open QAry
open scoped Matrix
noncomputable section

def selectedPrefixSpan {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q)) :=
  let c := fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i
  let B := selectedRows pos shape A c
  let eu := fun (z : Fin (dim m n) → ℤ) ↦
    (WithLp.toLp 2 (fun i ↦ (z i : ℝ)) : EuclideanSpace ℝ (Fin (dim m n)))
  let W := Submodule.span ℝ (Set.range (fun i : {i : Fin (k*β) // i.val < k*β-β} ↦ eu (B i)))
  W

def horizontalPrefix {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  ∀ x ∈ selectedPrefixSpan pos shape e s A, x (indexEquiv (.inr (.inr ()))) = 0

/-- The embedding coordinate is an integer-valued witness after any horizontal prefix. -/
theorem sameLine_of_horizontal {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β)
    (shape : k*β = dim m n) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (h : horizontalPrefix pos shape e s A) :
    (terminal pos shape e s A).sameLine := by
  let W := selectedPrefixSpan pos shape e s A
  let j : Fin (dim m n) := indexEquiv (.inr (.inr ()))
  let eu (z : Fin (dim m n) → ℤ) : EuclideanSpace ℝ (Fin (dim m n)) :=
    WithLp.toLp 2 (fun i ↦ (z i : ℝ))
  let P z := Wᗮ.orthogonalProjectionOnto (eu z)
  let u := Planted.plantedPoint e s ∘ indexEquiv.symm
  have coord (z) : (P z).val j = (z j : ℝ) := by
    change (Wᗮ.starProjection (eu z)) j = _
    rw [Submodule.starProjection_orthogonal_val]
    have zero := h _ (W.orthogonalProjectionOnto (eu z)).property
    change (eu z) j - (W.orthogonalProjectionOnto (eu z)).val j = _
    rw [show (W.orthogonalProjectionOnto (eu z)).val j = 0 from zero, sub_zero]
  have unit : (P u).val j = 1 := by simp [coord, u, j, Planted.plantedPoint]
  have nz : P u ≠ 0 := by
    intro eq
    rw [eq] at unit
    exact zero_ne_one (α := ℝ) unit
  refine ⟨nz, ?_⟩
  intro z hz line
  change P z = P u ∨ P z = -P u
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp line
  change a • P u = P z at ha
  have eq := congrArg (fun x : Wᗮ ↦ x.val j) ha
  change a * (P u).val j = (P z).val j at eq
  rw [unit, mul_one, coord] at eq
  have bound := hz.2.2
  change ‖P z‖ ≤ ‖P u‖ at bound
  rw [← ha, norm_smul, Real.norm_eq_abs] at bound
  have ab : |a| ≤ 1 := by nlinarith [norm_pos_iff.mpr nz]
  have iz : |z j| ≤ 1 := by exact_mod_cast (eq ▸ ab : |((z j : ℤ) : ℝ)| ≤ 1)
  have ne : z j ≠ 0 := by
    intro zero
    rw [zero, Int.cast_zero] at eq
    exact hz.2.1 (by change P z = 0; rw [← ha, eq, zero_smul])
  rcases abs_le.mp iz with ⟨lo, hi⟩
  rcases (show z j = 1 ∨ z j = -1 by omega) with ep | en
  · left
    simpa [eq, ep] using ha.symm
  · right
    simpa [eq, en] using ha.symm

/-- A full-dimensional terminal block has empty prefix. -/
theorem sameLine_singleBlock {m n q β : ℕ} [Fact q.Prime] (pos : 0 < β)
    (shape : 1*β = dim m n) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) : (terminal pos shape e s A).sameLine := by
  apply sameLine_of_horizontal
  intro x hx
  have empty : selectedPrefixSpan pos shape e s A = ⊥ := by
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have bad := i.property
    simp at bad
  rw [empty] at hx
  change x = 0 at hx
  subst x
  rfl

theorem horizontalResidual_iff {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β)
    (shape : k*β = dim m n) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) :
    (¬ horizontalPrefix pos shape e s A → (terminal pos shape e s A).sameLine) ↔
      (terminal pos shape e s A).sameLine := by
  by_cases h : horizontalPrefix pos shape e s A
  · simp [sameLine_of_horizontal pos shape e s A h]
  · simp [h]

/-- Competitors on a given projected norm stratum. -/
def offLineStratum {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β) (shape : k*β = dim m n)
    (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (rel : ℝ → ℝ → Prop) : Prop :=
  let c := fun i ↦ A i ⬝ᵥ (fun j ↦ (s j : ZMod q)) + e i
  let W := selectedPrefixSpan pos shape e s A
  let P := fun (z : Fin (dim m n) → ℤ) ↦ Wᗮ.orthogonalProjectionOnto
    (WithLp.toLp 2 (fun i ↦ (z i : ℝ)))
  let u := P (Planted.plantedPoint e s ∘ indexEquiv.symm)
  ∀ z, FinMember A c z → P z ≠ 0 → rel ‖P z‖ ‖u‖ → P z ∈ Submodule.span ℝ {u}

theorem offLineStrata_iff {m n q β k : ℕ} [Fact q.Prime] (pos : 0 < β)
    (shape : k*β = dim m n) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) :
    offLineStratum pos shape e s A (· < ·) ∧ offLineStratum pos shape e s A (· = ·) ↔
      (terminal pos shape e s A).offLine := by
  constructor
  · rintro ⟨h, g⟩ z ⟨hz, hn, le⟩
    exact le.lt_or_eq.elim (h z hz hn) (g z hz hn)
  · intro h
    exact ⟨fun z hz hn lt ↦ h z ⟨hz, hn, lt.le⟩, fun z hz hn eq ↦ h z ⟨hz, hn, eq.le⟩⟩

end
end SigabaNeo.Wall1
