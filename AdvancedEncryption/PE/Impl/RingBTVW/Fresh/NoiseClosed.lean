import PE.Impl.RingBTVW.Fresh.Noise
import SigabaNeoStd.Lattices.Homomorphic.GSWNoise
import SigabaNeoStd.Lattices.Homomorphic.Depth

/-!
# The noise bound in closed form

With `WN = |W| N` and `G = gswFactor WN N k` (the factor of one Ring-GSW NAND evaluated as a
Boolean program), the noise bound of a predicate given by a straight-line program of `n` gates is
at most `Bχ + WN Bχ K + WN (|rowBits| WN + 1) G^n Bχ K` (`noiseBound_le`): `f̂` contributes
`G^n Bχ` per output bit (`SigabaNeo.Lattices.nb_fhatSLP`) and `f` itself `(WN + 1)^n Bχ ≤ G^n Bχ`.
The same holds with the depth `D` of the predicate's wire in place of `n` (`noiseBound_le_depth`,
`noiseBound_le_of_depth_le`).
-/

namespace AdvancedEncryption.RingBTVW.Fresh

open SigabaNeo.Lattices Cslib

variable {N q k : ℕ} [NeZero q] (hk : q < 2 ^ k) {Attr : Type} [Fintype Attr]

theorem le_gswFactor (WN N k : ℕ) : WN + 1 ≤ gswFactor WN N k := by
  unfold gswFactor
  exact Nat.le_mul_of_pos_left _ (pow_pos (modFactor_pos WN k) _)

/-- **The noise bound in closed form.** -/
theorem noiseBound_le (Bχ K : ℕ) (f : SLP Attr × Wire Attr) :
    noiseBound (N := N) hk Bχ K f ≤
      Bχ + Fintype.card (Col k) * N * Bχ * K +
        Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
          (Fintype.card (Col k) * N) + 1) *
          (gswFactor (Fintype.card (Col k) * N) N k ^ f.1.length * Bχ)) * K := by
  set WN := Fintype.card (Col k) * N
  set G := gswFactor WN N k
  unfold noiseBound
  have hs : ∀ b, slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤ G ^ f.1.length * Bχ := fun b =>
    nb_fhatSLP WN Bχ hk f.1 f.2 _
  have he : errBound WN Bχ (f.1.circuit f.2) ≤ G ^ f.1.length * Bχ := by
    rw [errBound_circuit]
    exact (slpBound_le_length WN Bχ f.1 f.2).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (le_gswFactor WN N k) _))
  have hsum : ∑ b, WN * slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤
      Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (WN * (G ^ f.1.length * Bχ)) := by
    refine (Finset.sum_le_sum fun b _ => Nat.mul_le_mul_left WN (hs b)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  calc Bχ + WN * Bχ * K + WN * (∑ b, WN * slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
          (((ringSetting N q k hk Attr).fhat f).2 b) + errBound WN Bχ (f.1.circuit f.2)) * K
      ≤ Bχ + WN * Bχ * K + WN * (Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
          (WN * (G ^ f.1.length * Bχ)) + G ^ f.1.length * Bχ) * K := by gcongr
    _ = _ := by ring

/-- **The noise bound in closed form, by depth**: as `noiseBound_le` with the depth of the
predicate's wire in place of its number of gates (`SigabaNeo.Lattices.nb_fhatSLP_depth`). -/
theorem noiseBound_le_depth (Bχ K : ℕ) (f : SLP Attr × Wire Attr) :
    noiseBound (N := N) hk Bχ K f ≤
      Bχ + Fintype.card (Col k) * N * Bχ * K +
        Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
          (Fintype.card (Col k) * N) + 1) *
          (gswFactor (Fintype.card (Col k) * N) N k ^ SLP.depth f.1 f.2 * Bχ)) * K := by
  set WN := Fintype.card (Col k) * N
  set G := gswFactor WN N k
  unfold noiseBound
  have hs : ∀ b, slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤ G ^ SLP.depth f.1 f.2 * Bχ := fun b =>
    nb_fhatSLP_depth WN Bχ hk f.1 f.2 _
  have he : errBound WN Bχ (f.1.circuit f.2) ≤ G ^ SLP.depth f.1 f.2 * Bχ := by
    rw [errBound_circuit]
    exact (slpBound_le_depth WN Bχ f.1 f.2).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (le_gswFactor WN N k) _))
  have hsum : ∑ b, WN * slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
      (((ringSetting N q k hk Attr).fhat f).2 b) ≤
      Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (WN * (G ^ SLP.depth f.1 f.2 * Bχ)) := by
    refine (Finset.sum_le_sum fun b _ => Nat.mul_le_mul_left WN (hs b)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  calc Bχ + WN * Bχ * K + WN * (∑ b, WN * slpBound WN Bχ ((ringSetting N q k hk Attr).fhat f).1
          (((ringSetting N q k hk Attr).fhat f).2 b) + errBound WN Bχ (f.1.circuit f.2)) * K
      ≤ Bχ + WN * Bχ * K + WN * (Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
          (WN * (G ^ SLP.depth f.1 f.2 * Bχ)) + G ^ SLP.depth f.1 f.2 * Bχ) * K := by gcongr
    _ = _ := by ring

/-- `noiseBound_le_depth` at any bound `D` on the depth. -/
theorem noiseBound_le_of_depth_le (Bχ K : ℕ) (f : SLP Attr × Wire Attr) {D : ℕ}
    (hD : SLP.depth f.1 f.2 ≤ D) :
    noiseBound (N := N) hk Bχ K f ≤
      Bχ + Fintype.card (Col k) * N * Bχ * K +
        Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
          (Fintype.card (Col k) * N) + 1) *
          (gswFactor (Fintype.card (Col k) * N) N k ^ D * Bχ)) * K := by
  refine (noiseBound_le_depth hk Bχ K f).trans ?_
  have hG : 1 ≤ gswFactor (Fintype.card (Col k) * N) N k := gswFactor_pos _ N k
  gcongr

end AdvancedEncryption.RingBTVW.Fresh
