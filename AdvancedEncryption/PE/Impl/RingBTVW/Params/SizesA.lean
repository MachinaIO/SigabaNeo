import PE.Impl.RingBTVW.Params.NoiseGen
import PE.Impl.RingBTVW.Params.Stat

/-!
# The sizes and the noise at `confA` (Stage II, not yet wired)

The numbers of the configuration for branching programs (`BP_PLAN.md` §4): ring degree
`N = 2^36`, `K = log₂ q = 2^27`, `k = K + 1` digits, `|Wd| = d = 2^65`, flooding width `768`,
predicates of depth at most `1054`. Every statement is for variable `N`, `K`, `k`, `d` bounded by
hypotheses that the configuration discharges from its `irreducible_def`s (`k ≤ 2^28` from
`kp = Kp + 1`, `Kp = 2^27`, …), so the switch only instantiates them; the proofs are the generic
chain of `Params/NoiseGen.lean` with numeral side conditions.

The chain (§4.2): `WN ≤ 2^65`, `modFactor ≤ 2^722`, `treeHeight ≤ 66`, `gswFactor ≤ 2^48440`,
`G^1054 ≤ 2^51055760`, `|rowBits| WN + 1 ≤ 2^159`, `E = d N 2^768 ≤ 2^869`; the shifts of the
trapdoors within `τ = 2^Eτ`, `Eτ = 51055984`; with keys within `2^(B − 1)`, `B = Eτ + 240`:

  `4 · noise + 2 < 2^102113082 ≤ 2^K = 2^134217728` (`noise_ok_A`),

a margin of `32104646` bits (24 % of `K`). The statistical terms (§4.4): `2 K N + 1000 ≤ d`
(`KN2_le_A`), `|JC| ≤ 2^128`, `|HC| ≤ 2^129` for `128` attribute bits (`card_JC_A`, `card_HC_A`),
`δ₁, δ₆ ≤ 2^-370` (`lhl_A`), flooding `ε ≤ 2^-499` (`flood_A`; `|JC| = 2^127 (1 + 2^-27)^3` is
just above `2^127`, so the bound `2^-500` of the plan holds only up to that factor).
-/

namespace AdvancedEncryption.RingBTVW.Params.A

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.RingBTVW.Fresh
open AdvancedEncryption.RingBTVW.Concrete (pow_mul_le' pow_mul_le pow_le_pow' sum_bound)

/-- The bound on the depth of the predicates. -/
def Dmax : ℕ := 1054
/-- `log₂` of the bound on the shifts of the trapdoors: `65 + 159 + 1054 · 48440`. -/
irreducible_def Eτ : ℕ := 51055984
/-- The bits of a coefficient of the big box: `Eτ + 240`. -/
irreducible_def Bp : ℕ := 51056224
/-- The flooding width. -/
def wA : ℕ := 768
/-- The exponent of the noise bound: `65 + 159 + 51055760 + 869 + (Bp − 1) + 6`. -/
irreducible_def eNoise : ℕ := 102113082

variable {N K k d : ℕ}

section Chain

variable (hk : k ≤ 2 ^ 28) (hN : N ≤ 2 ^ 36)
include hk hN

theorem WN_le : Fintype.card (Col k) * N ≤ 2 ^ 65 := Gen.WN_le hk hN (by norm_num)

theorem WN1_le : Fintype.card (Col k) * N + 1 ≤ 2 ^ 66 := Gen.WN1_le hk hN (by norm_num)

theorem modFactor_le : modFactor (Fintype.card (Col k) * N) k ≤ 2 ^ 722 :=
  Gen.modFactor_le hk hN (by norm_num) (by norm_num)

theorem treeHeight_le : treeHeight N k ≤ 66 := Gen.treeHeight_le hk hN (by norm_num)

theorem gswFactor_le : gswFactor (Fintype.card (Col k) * N) N k ≤ 2 ^ 48440 :=
  Gen.gswFactor_le hk hN (by norm_num) (le_refl 722) (by norm_num)

/-- `G^n ≤ 2^51055760` for `n ≤ 1054`. -/
theorem gswPow_le {n : ℕ} (hn : n ≤ Dmax) :
    gswFactor (Fintype.card (Col k) * N) N k ^ n ≤ 2 ^ 51055760 :=
  Gen.gswPow_le (gswFactor_le hk hN) (by norm_num [Dmax]) hn

theorem R_le : Fintype.card (Fin 1 × Col k × Fin k × Fin N) ≤ 2 ^ 93 :=
  Gen.R_le hk hN (by norm_num)

theorem RW_le :
    Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (Fintype.card (Col k) * N) + 1 ≤ 2 ^ 159 :=
  Gen.RW_le hk hN (by norm_num)

omit hN in
theorem card_trapCol_le : Fintype.card (RingBTVW.TrapCol k) ≤ 2 ^ 31 :=
  Gen.card_trapCol_le hk (by norm_num) (by norm_num)

/-- **The shift of the simulated trapdoor** for predicates of depth at most `1054`. -/
theorem simTrapBound_le {n : ℕ} (hn : n ≤ Dmax) : RingBTVW.simTrapBound N k n ≤ 2 ^ Eτ :=
  Gen.simTrapBound_le (WN_le hk hN) (RW_le hk hN) (gswPow_le hk hN le_rfl) hn
    (by rw [Eτ_def])

/-- **The shift of the real trapdoor** (errors within `16`). -/
theorem realShift_le : (Fintype.card (Col k) * N) ^ 2 * 16 ≤ 2 ^ Eτ :=
  Gen.realShift_le (WN_le hk hN) (by rw [Eτ_def]; norm_num)

end Chain

theorem E_le (hd : d ≤ 2 ^ 65) (hN : N ≤ 2 ^ 36) : Fintype.card (Fin d) * N * 2 ^ wA ≤ 2 ^ 869 :=
  Gen.E_le hd hN wA (by norm_num [wA])

/-- **The noise of a predicate of depth at most `1054` is far below `q/4`** for keys within
`2^(Bp − 1)`, as soon as `K ≥ 102113082` (`K = 2^27` leaves `32104646` bits). -/
theorem noise_ok {Attr : Type} [Fintype Attr] (hk' : 2 ^ K < 2 ^ k) (hk : k ≤ 2 ^ 28)
    (hN : N ≤ 2 ^ 36) (hd : d ≤ 2 ^ 65) (hK : eNoise ≤ K) (f : SLP Attr × Wire Attr)
    (hf : SLP.depth f.1 f.2 ≤ Dmax) (S : ℕ) (hS : S ≤ 2 ^ (Bp - 1)) :
    4 * RingBTVW.noiseBound (Wd := Fin d) (Wt := RingBTVW.TrapCol k) (N := N) hk' (2 ^ wA) S f + 2
      < 2 ^ K :=
  Gen.noise_ok hk' wA f hf S (WN_le hk hN) (RW_le hk hN) (gswPow_le hk hN le_rfl) (E_le hd hN)
    (pow_mul_le (pow_mul_le (card_trapCol_le hk) hN) (le_refl (2 ^ wA))) hS
    (by norm_num [wA]) (by rw [Bp_def]; rw [eNoise_def] at hK; omega)

/-- The margin: `eNoise ≤ 2^27`, with `2^27 − eNoise = 32104646` bits to spare. -/
theorem eNoise_margin : eNoise + 32104646 = 2 ^ 27 := by rw [eNoise_def]; norm_num

/-! ### The abort probability -/

theorem card_coef_le (hk : k ≤ 2 ^ 28) (hN : N ≤ 2 ^ 36) (hd : d ≤ 2 ^ 65) :
    Fintype.card (RingBTVW.Coef d (RingBTVW.TrapCol k) N) ≤ 2 ^ 102 :=
  Gen.card_coef_le hd (by have : (4 : ℕ) * 2 ^ 28 + 1 ≤ 2 ^ 65 := by norm_num
                          omega) hN (by norm_num)

/-- `|Coef| (4 τ + 1) 2^128 ≤ 2^Bp`. -/
theorem abort_prod (hk : k ≤ 2 ^ 28) (hN : N ≤ 2 ^ 36) (hd : d ≤ 2 ^ 65) :
    Fintype.card (RingBTVW.Coef d (RingBTVW.TrapCol k) N) * (4 * 2 ^ Eτ + 1) * 2 ^ 128 ≤ 2 ^ Bp :=
  Gen.abort_prod (card_coef_le hk hN hd) (by rw [Eτ_def, Bp_def]; norm_num)

/-- `2 τ + 2 ≤ 2^(Bp − 1)`. -/
theorem hτM : 2 * 2 ^ Eτ + 2 ≤ 2 ^ (Bp - 1) := by
  have h1 : 2 * 2 ^ Eτ + 2 ≤ 2 ^ (Eτ + 2) := by
    rw [pow_add]
    have : 1 ≤ 2 ^ Eτ := Nat.one_le_two_pow
    omega
  exact h1.trans (pow_le_pow' (by rw [Eτ_def, Bp_def]; norm_num))

theorem hBp (hK : 2 ^ 27 ≤ K) : 2 ^ Bp ≤ 2 ^ K :=
  pow_le_pow' (le_trans (by rw [Bp_def]; norm_num) hK)

/-! ### The statistical terms -/

/-- `2 K N + 1000 ≤ d`. -/
theorem KN2_le (hK : K ≤ 2 ^ 27) (hN : N ≤ 2 ^ 36) (hd : 2 ^ 65 ≤ d) : 2 * (K * N) + 1000 ≤ d := by
  have h : 2 * (K * N) ≤ 2 * (2 ^ 27 * 2 ^ 36) := by gcongr
  have : 2 * (2 ^ 27 * 2 ^ 36) + 1000 ≤ (2 : ℕ) ^ 65 := by norm_num
  omega

/-- `K N + 1000 ≤ d`. -/
theorem KN_le (hK : K ≤ 2 ^ 27) (hN : N ≤ 2 ^ 36) (hd : 2 ^ 65 ≤ d) : K * N + 1000 ≤ d := by
  have := KN2_le hK hN hd; omega

/-- `8 k³ ≤ 2^85` for `k ≤ 2^27 + 1`. -/
theorem k3_le (hk : k ≤ 2 ^ 27 + 1) : 8 * k ^ 3 ≤ 2 ^ 85 := by
  calc 8 * k ^ 3 ≤ 8 * (2 ^ 27 + 1) ^ 3 := by gcongr
    _ ≤ 2 ^ 85 := by norm_num

/-- `|JC| ≤ 2^128` for `128` attribute bits. -/
theorem card_JC {q : ℕ} [NeZero q] (hq : q < 2 ^ k) (hk : k ≤ 2 ^ 27 + 1) (hN : N ≤ 2 ^ 36) :
    Fintype.card (JC (ringSetting N q k hq (Fin 128))) ≤ 2 ^ 128 :=
  card_JC_le hq (by norm_num : 128 ≤ 2 ^ 7) (k3_le hk) hN (by norm_num)

/-- `|HC| ≤ 2^129` for `128` attribute bits. -/
theorem card_HC {q : ℕ} [NeZero q] (hq : q < 2 ^ k) (hk : k ≤ 2 ^ 27 + 1) (hN : N ≤ 2 ^ 36) :
    Fintype.card (HC (ringSetting N q k hq (Fin 128))) ≤ 2 ^ 129 :=
  card_HC_le hq (card_JC hq hk hN) (by
    calc 128 * (2 * k) ≤ 128 * (2 * (2 ^ 27 + 1)) := by gcongr
      _ ≤ 2 ^ 128 := by norm_num)

/-- **The leftover hash bound at `confA`**: `C ≤ 2^130` columns and slack `500` give `2^-370`. -/
theorem lhl_A {C a d : ℕ} (hC : C ≤ 2 ^ 130) (had : a + 1000 ≤ d) :
    (C : ℝ) * (Real.sqrt ((2 : ℝ) ^ a * ((2 : ℝ) ^ d)⁻¹) / 2) ≤ ((2 : ℝ) ^ 370)⁻¹ :=
  lhl_le_gen hC (show a + 2 * 500 ≤ d by omega) (by norm_num)

/-- **The flooding term at `confA`**: `|JC| N (d N 16) / 2^768 ≤ 2^-499`. -/
theorem flood_A {q : ℕ} [NeZero q] (hq : q < 2 ^ k) (hk : k ≤ 2 ^ 27 + 1) (hN : N ≤ 2 ^ 36)
    (hd : d ≤ 2 ^ 65) :
    ((Fintype.card (JC (ringSetting N q k hq (Fin 128))) * N * (d * N * 16) : ℕ) : ℝ) /
        ((2 ^ wA : ℕ) : ℝ) ≤ ((2 : ℝ) ^ 499)⁻¹ :=
  rpow_div_le (pow_mul_le (pow_mul_le (card_JC hq hk hN) hN)
    (pow_mul_le (pow_mul_le hd hN) (le_refl (2 ^ 4)))) (by norm_num [wA])

end AdvancedEncryption.RingBTVW.Params.A
