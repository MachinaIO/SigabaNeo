import SigabaNeo.Lib.Lattices.Research.Wall1.WatsonHigherPolytope
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! Pass from a residue-code chart to a lattice basis. The normalization cancels the
index of the numerator lattice and leaves exactly the square of the code order. -/
noncomputable section
namespace SigabaNeo.Wall1.Watson.HigherGram
open Matrix Finset Module
variable {n d : ℕ}
local notation "I" => Fin n

/-- The columns of an integer matrix generate the numerator lattice. Its determinant
has absolute value equal to the index of the residue code. -/
theorem code_basis (hd : 0 < d) (C : Code n d) (card : Nat.card C = d) :
    ∃ U : Matrix I I ℤ, U.det.natAbs * d = d^n ∧
      ∀ z : I → ℤ, z ≠ 0 → U *ᵥ z ≠ 0 ∧ (fun i ↦ ((U *ᵥ z) i : ZMod d)) ∈ C := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  let f : (I → ℤ) →+ (I → ZMod d) :=
    { toFun := fun z i ↦ (z i : ZMod d)
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext; simp }
  have surj : Function.Surjective f := fun z ↦
    ⟨fun i ↦ (z i).cast,funext fun i ↦ ZMod.intCast_zmod_cast _⟩
  let H := C.comap f
  have ind : H.index = C.index := C.index_comap_of_surjective surj
  have total : H.index * d = d^n := by
    calc
      H.index * d = C.index * Nat.card C := congrArg₂ (· * ·) ind card.symm
      _ = Nat.card (I → ZMod d) := C.index_mul_card
      _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_pi]
  letI : H.FiniteIndex := ⟨fun h ↦ by rw [h,zero_mul] at total; exact (pow_pos hd n).ne' total.symm⟩
  have rk : finrank ℤ H.toIntSubmodule = n := (H.finrank_eq_of_finiteIndex).trans (by simp)
  let B := (finBasis ℤ H.toIntSubmodule).reindex (finCongr rk)
  let U : Matrix I I ℤ := of fun i j ↦ (B j : I → ℤ) i
  have idx : H.index = U.det.natAbs := by
    rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ I) H B]
    rfl
  refine ⟨U,idx ▸ total,fun z nz ↦ ?_⟩
  let x := ∑ i, z i • B i
  have eq : U *ᵥ z = (x : I → ℤ) := by
    ext i; simp [U,x,mulVec,dotProduct,Finset.sum_apply,mul_comm]
  rw [eq]
  refine ⟨?_,(x.property : (x : I → ℤ) ∈ H)⟩
  intro zero
  have hx : x = 0 := Subtype.ext zero
  apply nz
  funext i
  have e : B.repr x i = z i := congrFun (B.repr_sum_self z) i
  simpa [hx] using e.symm

/-- A uniform normalized determinant inequality implies the marked determinant
inequality for every residue chart of the indicated order. -/
theorem chart_bound_of_minimum (p : ℝ) (hd : 0 < d) (C : Code n d) (card : Nat.card C = d)
    (G : Mat n) (pd : G.PosDef)
    (minimum : ∀ z : I → ℤ, z ≠ 0 → (fun i ↦ (z i : ZMod d)) ∈ C → (d : ℝ)^2 ≤ value G z)
    (unmarked : ∀ A : Mat n, A.PosDef → (∀ z : I → ℤ, z ≠ 0 → 1 ≤ value A z) → 1 ≤ p * A.det) :
    (d : ℝ)^2 ≤ p * G.det := by
  obtain ⟨U,idx,member⟩ := code_basis hd C card
  let P := (Int.castRingHom ℝ).mapMatrix U
  let A := ((d:ℝ)^2)⁻¹ • (Pᴴ * G * P)
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have detP : P.det = (U.det : ℝ) := (Int.cast_det U).symm
  have count : |P.det| * d = (d:ℝ)^n := by
    rw [detP,← Int.cast_abs,Int.abs_eq_natAbs]; exact_mod_cast idx
  have nz : P.det ≠ 0 := fun h ↦ by simp [h] at count; exact (pow_pos dp n).ne' count.symm
  have ap : A.PosDef := (pd.conjTranspose_mul_mul_same
    (mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr nz)))).smul
      (inv_pos.mpr (sq_pos_of_pos dp))
  have minA (z : I → ℤ) (hz : z ≠ 0) : 1 ≤ value A z := by
    have m := minimum _ (member z hz).1 (member z hz).2
    have eq : (fun i ↦ ((U *ᵥ z) i : ℝ)) = P *ᵥ (fun i ↦ (z i : ℝ)) :=
      funext ((Int.castRingHom ℝ).map_mulVec U z)
    have eval : value A z = ((d:ℝ)^2)⁻¹ * value G (U *ᵥ z) := by
      simp only [value,A,smul_mulVec,dotProduct_smul,smul_eq_mul,eq,
        Matrix.conjTranspose_eq_transpose_of_trivial,← mulVec_mulVec]
      rw [dotProduct_mulVec,vecMul_transpose]
    rwa [eval,← div_eq_inv_mul,le_div_iff₀ (sq_pos_of_pos dp),one_mul]
  have hh := unmarked A ap minA
  have divisor : ((d:ℝ)^2)^n = P.det^2 * (d:ℝ)^2 := by
    rw [pow_right_comm,← count,mul_pow,sq_abs]
  have cancel : (d:ℝ)^2 * A.det = G.det := by
    simp only [A,det_smul,Fintype.card_fin,det_mul,det_conjTranspose,star_trivial,inv_pow]
    field_simp [dp.ne']
    rw [divisor]; ring
  calc
    (d:ℝ)^2 ≤ (d:ℝ)^2 * (p*A.det) := le_mul_of_one_le_right (sq_nonneg _) hh
    _ = p*G.det := by rw [← cancel]; ring

end SigabaNeo.Wall1.Watson.HigherGram

#print axioms SigabaNeo.Wall1.Watson.HigherGram.code_basis
#print axioms SigabaNeo.Wall1.Watson.HigherGram.chart_bound_of_minimum
