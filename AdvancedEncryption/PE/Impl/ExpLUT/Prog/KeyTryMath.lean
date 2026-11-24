import PE.Impl.ExpLUT.KeyGen

/-!
# KeyGen (package F3): the try of box rejection, row by row

The quantities of one try of `boxSample` (`keyLaw`), in the form a machine computes them row by
row `i' < W`:

* **`pubShort_apply`**: `M_F (p, 0)` at row `i'` is
  `Σ_w σ_{i'}(B_{0,w}) p_{i',w} + Σ_{k,c} σ_{i'}(H_k[0,c]) p_{i',k,c}
   − Σ_{i,k} [i' = i·k] Σ_c G_{0,c} p_{i,k,c} + [i' = 0] Σ_c A_F[0,c] p_c`;
* `realTrap_inl`, `realTrap_inr`: the shift of the real trapdoor on the `Ā` columns of row `i`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] {S : Setting R} {Wb J Pos : Type*} [Fintype Wb] [Fintype J]
  [DecidableEq Wb] [DecidableEq J]

/-- **The public map on the short part, row by row.** -/
theorem pubShort_apply (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (p : PIdx Wb J S.τ S.E.W → R) (i' : Fin S.E.W) :
    pubShort M mpk F p i' =
      (∑ w, S.E.σ (S.idx i') (mpk.B 0 (.inl w)) * p (.inl (i', w))) +
      (∑ k, ∑ c, S.E.σ (S.idx i') (mpk.H k 0 c) * p (.inr (.inl (i', k, c)))) -
      (∑ i, ∑ k, if i' = M.mulRow i k then ∑ c, S.G 0 c * p (.inr (.inl (i, k, c))) else 0) +
      (if i' = S.row0 then ∑ c, keyPK M mpk F 0 c * p (.inr (.inr c)) else 0) := by
  simp only [pubShort, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type, keyMat, Matrix.of_apply, assemble, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp only [ite_self, Finset.sum_ite_irrel, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  abel

/-- The row `i` with `i · k = i'`: `(i' + W − (je k mod W)) mod W`. -/
def HelperMap.backRow {J : Type*} (M : HelperMap S J) (i' : Fin S.E.W) (k : J) : Fin S.E.W :=
  ⟨(i' + (S.E.W - M.je k % S.E.W)) % S.E.W, Nat.mod_lt _ S.E.W_pos⟩

theorem mod_add_lt_of {W x : ℕ} (h1 : W ≤ x) (h2 : x < 2 * W) : x % W = x - W := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem mod_inv_iff {W a b c : ℕ} (ha : a < W) (hb : b < W) (hc : c < W) :
    c = (a + b) % W ↔ a = (c + (W - b)) % W := by
  rcases Nat.lt_or_ge (a + b) W with h | h
  · rw [Nat.mod_eq_of_lt h]
    rcases Nat.lt_or_ge (c + (W - b)) W with h' | h'
    · rw [Nat.mod_eq_of_lt h']; omega
    · rw [mod_add_lt_of h' (by omega)]; omega
  · rw [mod_add_lt_of h (by omega)]
    rcases Nat.lt_or_ge (c + (W - b)) W with h' | h'
    · rw [Nat.mod_eq_of_lt h']; omega
    · rw [mod_add_lt_of h' (by omega)]; omega

theorem HelperMap.mulRow_eq_iff {J : Type*} (M : HelperMap S J) (i i' : Fin S.E.W) (k : J) :
    i' = M.mulRow i k ↔ i = M.backRow i' k := by
  have hW := S.E.W_pos
  simp only [HelperMap.mulRow, HelperMap.backRow, Fin.ext_iff]
  rw [Nat.add_mod (i.val) (M.je k), Nat.mod_eq_of_lt i.isLt, ← Nat.mod_eq_of_lt i.isLt]
  have e : (i.val % S.E.W + M.je k % S.E.W) % S.E.W = (i.val + M.je k % S.E.W) % S.E.W := by
    rw [Nat.mod_eq_of_lt i.isLt]
  rw [e, Nat.mod_eq_of_lt i.isLt]
  exact mod_inv_iff i.isLt (Nat.mod_lt _ hW) i'.isLt

/-- **The rows of `η_{i,k}` meeting row `i'`**: `Σ_i [i' = i·k] f_i = f_{i'·k⁻¹}`. -/
theorem sum_mulRow {J : Type*} {A : Type*} [AddCommMonoid A] (M : HelperMap S J) (i' : Fin S.E.W)
    (k : J) (f : Fin S.E.W → A) :
    (∑ i, if i' = M.mulRow i k then f i else 0) = f (M.backRow i' k) := by
  simp only [M.mulRow_eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end AdvancedEncryption.ExpLUT
