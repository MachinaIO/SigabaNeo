import SigabaNeoStd.Lattices.Basic

/-!
# The gadget matrix

`gadget n b q = I_n ⊗ (1, 2, …, 2^{b−1}) ∈ Z_q^{n×nb}` ([MP12], Section 4): column `r·b + t` is
`2^t` times the `r`-th unit vector. `gadgetInv n b q v` is the binary decomposition of a syndrome
`v ∈ Z_q^n` (the `b` low bits of each representative). It inverts the gadget when `q ≤ 2^b`
(`gadget_mulVec_gadgetInv`), with entries in `{0, 1}` (`abs_gadgetInv_le`).

cslib-frontier's gadget (`CslibFrontier.Crypto.Computational.LWE.Trapdoor.Gadget`) is for
`q = 2^w`; this one works for every modulus.
-/

namespace SigabaNeo.Lattices

open scoped Matrix

variable (n b q : ℕ)

/-- The row of a gadget column. -/
def gadgetRow (c : Fin (n * b)) : Fin n := (finProdFinEquiv.symm c).1
/-- The bit of a gadget column. -/
def gadgetBit (c : Fin (n * b)) : Fin b := (finProdFinEquiv.symm c).2

/-- The gadget `G = I_n ⊗ (1, 2, …, 2^{b−1})`. -/
def gadget : Matrix (Fin n) (Fin (n * b)) (ZMod q) :=
  fun i c => if gadgetRow n b c = i then 2 ^ (gadgetBit n b c : ℕ) else 0

/-- Binary decomposition of a syndrome. -/
def gadgetInv (v : Fin n → ZMod q) : Fin (n * b) → ℤ :=
  fun c => if (v (gadgetRow n b c)).val.testBit (gadgetBit n b c) then 1 else 0

theorem gadgetRow_val (c : Fin (n * b)) : (gadgetRow n b c).val = c.val / b := by
  simp [gadgetRow, finProdFinEquiv, Fin.divNat]

theorem gadgetBit_val (c : Fin (n * b)) : (gadgetBit n b c).val = c.val % b := by
  simp [gadgetBit, finProdFinEquiv, Fin.modNat]

/-- The gadget, entrywise. -/
theorem gadget_apply (i : Fin n) (c : Fin (n * b)) :
    gadget n b q i c = if c.val / b = i.val then 2 ^ (c.val % b) else 0 := by
  simp only [gadget, ← gadgetRow_val, ← gadgetBit_val, Fin.val_inj]

theorem sum_testBit_pow (a W : ℕ) :
    ∑ t : Fin W, (if a.testBit t then 2 ^ (t : ℕ) else 0) = a % 2 ^ W := by
  induction W with
  | zero => simp [Nat.mod_one]
  | succ W ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ W) with h | h <;> simp [h]

variable {n b q}

/-- The decomposition inverts the gadget when `q ≤ 2^b`. -/
theorem gadget_mulVec_gadgetInv [NeZero q] (hq : q ≤ 2 ^ b) (v : Fin n → ZMod q) :
    gadget n b q *ᵥ (fun c => (gadgetInv n b q v c : ZMod q)) = v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, gadget, gadgetInv]
  rw [← (finProdFinEquiv (m := n) (n := b)).sum_comp]
  simp only [gadgetRow, gadgetBit, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    have h := sum_testBit_pow (v i).val b
    rw [Nat.mod_eq_of_lt ((ZMod.val_lt (v i)).trans_le hq)] at h
    have h2 : (((∑ t : Fin b, (if (v i).val.testBit t then 2 ^ (t : ℕ) else 0) : ℕ)) :
        ZMod q) = v i := by rw [h, ZMod.natCast_zmod_val]
    refine Eq.trans ?_ h2
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  · intro b _ hb; simp [hb]
  · simp

theorem abs_gadgetInv_le (v : Fin n → ZMod q) (c : Fin (n * b)) : |gadgetInv n b q v c| ≤ 1 := by
  unfold gadgetInv; split_ifs <;> simp

end SigabaNeo.Lattices
