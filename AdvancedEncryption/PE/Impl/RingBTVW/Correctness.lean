import PE.Impl.RingBTVW.KeyGen
import PE.Impl.RingBTVW.Noise
import SigabaNeo.Lib.Lattices.Decode

/-!
# The probability of a correct decryption

A key drawn by one try of box rejection is valid with short parts unless the try aborts
(`RingBTVW.valid_of_mem_support`). With the coins of `Enc` bounded on their support and
`4 · noiseBound + 2 < q`, every accepted key decrypts every ciphertext correctly
(`RingBTVW.decrypt_correct_of_bounds`), so decryption fails with probability at most the abort
probability, at most `1 − |Inner| / |Big|` (`decrypt_fail_le`, with
`SigabaNeo.Lattices.boxSample_none_le`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
open scoped ENNReal

variable {N q k : ℕ} [NeZero q] (hk : q < 2 ^ k) {Attr : Type} {Wd Wt : Type} [Fintype Wd]
  [Fintype Wt]

/-- **Decryption fails at most when key generation aborts.** -/
theorem decrypt_fail_le (hN : 0 < N) (hW : 0 < Fintype.card Wd)
    (mpk : MPK (ringSetting N q k hk Attr) Wd Wt) (x : Attr → Bool) (M : Bool)
    (f : SLP Attr × Wire Attr) (hfx : SLP.evalBool x f.1 f.2 = false)
    (Big Small : Finset (KeyShort Wd Wt (Negacyclic (ZMod q) N))) (hBig : Big.Nonempty)
    (dec : Negacyclic (ZMod q) N → (Col k → Negacyclic (ZMod q) N))
    (hdec : ∀ u, gadgetMap (S := ringSetting N q k hk Attr) (dec u) = u)
    (T : (Col k → Negacyclic (ZMod q) N) → KeyShort Wd Wt (Negacyclic (ZMod q) N))
    (hT : ∀ z, shortMap mpk (T z) + gadgetMap (S := ringSetting N q k hk Attr) z =
      (keyMatrix mpk f *ᵥ z) 0)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec y) ∈ Big)
    (lawR : PMF (EncCoins (ringSetting N q k hk Attr) Wd Wt)) (Bχ K : ℕ)
    (hSmall : ∀ v ∈ Small, (∀ c, cnorm (v.1 c) ≤ K) ∧ ∀ c, cnorm (v.2 c) ≤ K)
    (hdecK : ∀ y c, cnorm (dec y c) ≤ K)
    (hr : ∀ r ∈ lawR.support, cnorm r.e' ≤ Bχ ∧ rnorm r.e₀ ≤ Bχ ∧ rnorm r.e₁ ≤ Bχ ∧
      (∀ i c c', cnorm (r.Rm i c c') ≤ 1) ∧ ∀ j, rnorm (r.ej j) ≤ Bχ)
    (hq : 4 * noiseBound (Wd := Wd) (Wt := Wt) (N := N) hk Bχ K f + 2 < q) :
    ((keyLaw Big Small hBig dec mpk T).bind fun o => lawR.map fun r =>
        decide (decodeBit hN (decryptRaw mpk f (keyOfOutput o) (encrypt mpk x M r)) = M)) false ≤
      keyLaw Big Small hBig dec mpk T none := by
  rw [PMF.bind_apply, tsum_eq_single none]
  · exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
  · intro o ho
    cases o with
    | none => exact absurd rfl ho
    | some v =>
      by_cases hv : some v ∈ (keyLaw Big Small hBig dec mpk T).support
      · refine mul_eq_zero_of_right _ ?_
        rw [PMF.map_apply]
        refine tsum_eq_zero_iff.mpr fun r => ?_
        by_cases hrs : r ∈ lawR.support
        · obtain ⟨he', he₀, he₁, hR, hej⟩ := hr r hrs
          have hvalid := valid_of_mem_support Big Small hBig dec hdec mpk T (keyMatrix mpk f) hT hcov
            (some v) hv v rfl
          -- the short parts lie in the small box
          have hpos := (PMF.mem_support_iff _ _).mp hv
          rw [keyLaw, boxSample_some Big hBig Small (shortMap mpk)
            (gadgetMap (S := ringSetting N q k hk Attr)) dec hdec T mpk.p hcov] at hpos
          have ht : boxTarget Small (shortMap mpk) dec
              (fun z => shortMap mpk (T z) + gadgetMap (S := ringSetting N q k hk Attr) z) mpk.p v := by
            by_contra h; exact hpos (if_neg h)
          obtain ⟨hvS, ⟨y, hy⟩, -⟩ := ht
          have hK := hSmall v.1 hvS
          have hc := decrypt_correct_of_bounds hk hN hW mpk x M r f (keyOfOutput (some v)) hvalid
            hfx Bχ K he' he₀ he₁ hR hej (fun c d => by simpa [keyOfOutput] using hK.1 c)
            (fun c d => by simpa [keyOfOutput] using hK.2 c)
            (fun c d => by simpa [keyOfOutput, ← hy] using hdecK y c) hq
          simp [hc]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hrs]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hv]

end AdvancedEncryption.RingBTVW
