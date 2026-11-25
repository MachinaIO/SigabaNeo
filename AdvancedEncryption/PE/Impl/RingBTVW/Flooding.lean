import PE.Impl.RingBTVW.Hybrid4
import SigabaNeo.Lib.Lattices.Flood
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseBound

/-!
# The flooding hypothesis of hybrid 4 over `R_q`

The errors of the encodings are drawn with independent coefficients uniform in `{0, …, W − 1}`
(`floodRows`). If the error `e₀` has coefficients at most `Bχ`, every shift `e₀ W_j` by binary
`W_j` has coefficients at most `|Wd| · N · Bχ`, so the shifted law is within
`|J| · |W| · N · |Wd| · N · Bχ / W` of the unshifted one (`flood_hyp`): the hypothesis `hflood` of
`RingBTVW.hybrid4`.
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib Cslib.Probability
open scoped ENNReal

variable {N q : ℕ} [NeZero q] {k : ℕ} {S : Setting (Negacyclic (ZMod q) N) k}
  {Wd : Type} [Fintype Wd] [DecidableEq Wd]
  [Fintype S.Attr] [DecidableEq S.Attr] [DecidableEq S.ctBits.Index]

omit [Fintype Wd] [DecidableEq Wd] [Fintype S.Attr] [DecidableEq S.Attr]
  [DecidableEq S.ctBits.Index] in
theorem cnorm_one_le : cnorm (1 : Negacyclic (ZMod q) N) ≤ 1 := by
  rw [cnorm_le_iff]
  intro j
  rw [Negacyclic.coeffs_one]
  split_ifs
  · exact zabs_one_le
  · simp [zabs]

/-- The errors of the encodings: independent coefficients uniform in `{0, …, W − 1}`. -/
noncomputable def floodRows (W : ℕ) [NeZero W] :
    PMF (S.Attr × S.ctBits.Index → Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)) :=
  (floodLaw (N := N) (Q := q) (JC S) W).map fun v j => Matrix.of fun _ c => v (j, c)

omit [DecidableEq Wd] in
/-- **The flooding hypothesis.** -/
theorem flood_hyp (W : ℕ) [NeZero W] (Bχ : ℕ) (e₀ : Matrix (Fin 1) Wd (Negacyclic (ZMod q) N))
    (he₀ : rnorm e₀ ≤ Bχ) (w : JC S → (Wd → Bool)) :
    CloseTo ((floodRows (S := S) W).map fun e j => e j + e₀ * wMat w j) (floodRows W)
      (ENNReal.ofReal (Fintype.card (JC S) * N * (Fintype.card Wd * N * Bχ : ℕ) / W)) := by
  classical
  set δ : JC S → Negacyclic (ZMod q) N := fun jc => (e₀ * wMat w jc.1) 0 jc.2
  have h := (closeTo_floodLaw_add (N := N) (Q := q) (JC S) W δ).map
    (fun v j => (Matrix.of fun _ c => v (j, c) : Matrix (Fin 1) (Col k) (Negacyclic (ZMod q) N)))
  rw [PMF.map_comp] at h
  unfold floodRows
  rw [PMF.map_comp]
  have hW : ∀ jc : JC S, rnorm (e₀ * wMat w jc.1) ≤ Fintype.card Wd * N * Bχ := by
    intro jc
    refine (rnorm_mul_le e₀ _ 1 fun c c' => ?_).trans ?_
    · simp only [wMat, Matrix.of_apply, bitVal]
      split_ifs <;> simp [cnorm_zero, cnorm_one_le]
    · rw [mul_one]; exact Nat.mul_le_mul_left _ he₀
  refine CloseTo.mono (ε := ENNReal.ofReal (∑ ij : JC S × Fin N,
      ((ZMod.valMinAbs ((δ ij.1).coeffs ij.2 : ZMod q)).natAbs : ℝ) / W)) ?_ ?_
  · convert h using 2
    funext v j
    ext a c
    fin_cases a
    simp [δ]
  · apply ENNReal.ofReal_le_ofReal
    calc (∑ ij : JC S × Fin N, ((ZMod.valMinAbs ((δ ij.1).coeffs ij.2 : ZMod q)).natAbs : ℝ) / W)
        ≤ ∑ _ij : JC S × Fin N, ((Fintype.card Wd * N * Bχ : ℕ) : ℝ) / W := by
          refine Finset.sum_le_sum fun ij _ => ?_
          gcongr
          have h1 := zabs_coeffs_le_cnorm (δ ij.1) ij.2
          have h2 := (cnorm_le_rnorm (e₀ * wMat w ij.1.1) ij.1.2).trans (hW ij.1)
          exact_mod_cast h1.trans h2
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

end AdvancedEncryption.RingBTVW
