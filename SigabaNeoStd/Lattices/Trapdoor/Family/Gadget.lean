import SigabaNeoStd.Lattices.Trapdoor.Family.Helpers
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Trapdoor sampler: the MP12 gadget trapdoor over `Z_q`

The trapdoor of [MP12], Section 5, at the parameters of the family: `m = 2·mb` with
`mb = n (w + 1)`, a uniform `Ā ∈ Z_q^{n×mb}`, a short `R ∈ {−1, 0, 1}^{mb×mb}`, the gadget
`G = I_n ⊗ (1, 2, …, 2^w)`, and

  `B = [Ā | G − Ā R]` (`Bmat`).

`G` is inverted on every syndrome by binary decomposition (`gInv`, `gadget_mulVec_gInv`: `q ≤ 2^{w+1}`),
and `xPre R v = [R z; z]` with `z = gInv v` is a short preimage: `B · xPre R v = v`
(`Bmat_mulVec_xPre`) with entries at most `mb` in absolute value (`abs_xPre_le`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open SigabaNeo.Lattices
open scoped Matrix

section
variable (κ : ℕ)

/-- Columns of `Ā` and of `G`. -/
abbrev mb : ℕ := n κ * (w κ + 1)

theorem m_eq_mb : m κ = mb κ + mb κ := by unfold m mb; ring

/-- `Fin m = Fin mb ⊕ Fin mb`. -/
def colEquiv : Fin (m κ) ≃ Fin (mb κ) ⊕ Fin (mb κ) :=
  (finCongr (m_eq_mb κ)).trans finSumFinEquiv.symm

/-- The row and bit of a gadget column. -/
def gRow (c : Fin (mb κ)) : Fin (n κ) := (finProdFinEquiv.symm c).1
def gBit (c : Fin (mb κ)) : Fin (w κ + 1) := (finProdFinEquiv.symm c).2

/-- The gadget `G = I_n ⊗ (1, 2, …, 2^w)`. -/
noncomputable def gadget : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)) :=
  fun i c => if gRow κ c = i then 2 ^ (gBit κ c : ℕ) else 0

/-- Binary decomposition of a syndrome. -/
noncomputable def gInv (v : Fin (n κ) → ZMod (q κ)) : Fin (mb κ) → ℤ :=
  fun c => if (v (gRow κ c)).val.testBit (gBit κ c) then 1 else 0

/-- The public matrix `[Ā | G − Ā R]`. -/
noncomputable def Bmat (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) : Matrix (Fin (n κ)) (Fin (m κ)) (ZMod (q κ)) :=
  (Matrix.fromCols Abar (gadget κ - Abar * R.map (Int.cast : ℤ → ZMod (q κ)))).submatrix id
    (colEquiv κ)

/-- The short preimage `[R z; z]`, `z = gInv v`. -/
noncomputable def xPre (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (v : Fin (n κ) → ZMod (q κ)) : Fin (m κ) → ℤ :=
  Sum.elim (R *ᵥ gInv κ v) (gInv κ v) ∘ colEquiv κ

theorem q_le_two_pow : q κ ≤ 2 ^ (w κ + 1) := by
  have := (exists_q κ).choose_spec.2.2; rw [pow_succ]; unfold q; omega

/-- `gadget κ` is the library's gadget, so binary decomposition inverts it (`q ≤ 2^{w+1}`). -/
theorem gadget_eq_lib : gadget κ = Lattices.gadget (n κ) (w κ + 1) (q κ) := rfl

theorem gadget_mulVec_gInv (v : Fin (n κ) → ZMod (q κ)) :
    gadget κ *ᵥ (fun c => (gInv κ v c : ZMod (q κ))) = v :=
  gadget_mulVec_gadgetInv (q_le_two_pow κ) v

theorem Bmat_mulVec_xPre (Abar : Matrix (Fin (n κ)) (Fin (mb κ)) (ZMod (q κ)))
    (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (v : Fin (n κ) → ZMod (q κ)) :
    Bmat κ Abar R *ᵥ (fun j => (xPre κ R v j : ZMod (q κ))) = v := by
  have hx : (fun j => (xPre κ R v j : ZMod (q κ))) =
      (Sum.elim ((R.map (Int.cast : ℤ → ZMod (q κ))) *ᵥ fun c => (gInv κ v c : ZMod (q κ)))
        (fun c => (gInv κ v c : ZMod (q κ)))) ∘ colEquiv κ := by
    funext j
    unfold xPre
    simp only [Function.comp_apply]
    cases colEquiv κ j with
    | inl a => simp [Matrix.mulVec, dotProduct]
    | inr a => simp
  rw [hx, Bmat, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [Matrix.fromCols_mulVec_sumElim, Matrix.sub_mulVec, Matrix.mulVec_mulVec, gadget_mulVec_gInv]
  simp

theorem abs_gInv_le (v : Fin (n κ) → ZMod (q κ)) (c : Fin (mb κ)) : |gInv κ v c| ≤ 1 := by
  unfold gInv; split_ifs <;> simp

theorem abs_xPre_le (R : Matrix (Fin (mb κ)) (Fin (mb κ)) ℤ) (hR : ∀ i j, |R i j| ≤ 1)
    (v : Fin (n κ) → ZMod (q κ)) (j : Fin (m κ)) : |xPre κ R v j| ≤ mb κ := by
  unfold xPre
  simp only [Function.comp_apply]
  cases colEquiv κ j with
  | inl a =>
    simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c, |R a c * gInv κ v c| ≤ ∑ _c : Fin (mb κ), (1 : ℤ) := Finset.sum_le_sum fun c _ => by
          rw [abs_mul]
          exact mul_le_one₀ (hR a c) (abs_nonneg _) (abs_gInv_le κ v c)
      _ = mb κ := by simp
  | inr a =>
    simp only [Sum.elim_inr]
    refine (abs_gInv_le κ v a).trans ?_
    have : 1 ≤ mb κ := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    exact_mod_cast this

end

end SigabaNeo.Lattices.Trapdoor.Family
