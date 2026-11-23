import PE.Impl.DualUse.ConcreteNoise
import PE.Impl.DualUse.Params.NoiseGen

/-!
# Parameters for simulated keys: the sizes and the noise

The parameters of the configuration `confP` for branching programs (`BP_PLAN.md` §4):

* `q = 2^K`, `K = 2^27`, `k = K + 1` binary digits;
* ring degree `N = 2^36`, so that `log₂ q / N = 2^{-9}` (Ring-LWE estimate in
  `Params/Strength.lean`);
* `|Wd| = 2^65 ≥ 2 · K · N + 1000` columns of `B₀`, for the leftover hash lemma over `R_q²`;
* the shift of every trapdoor (real, or simulated for predicates of depth at most `Dmax = 1054`,
  which covers the circuits of the branching programs, `depth_bpPred`) within
  `τ = 2^{51055984}` (`simTrapBound_le`, `realShift_le`);
* key boxes of `B = 51056224` bits per coefficient;
* errors from the centered binomial law of width `16`, flooding below `2^768`.

For every predicate of depth at most `Dmax` and keys within `2^{B−1}`, the noise bound is below
`2^{eNoise} / 4 < q / 4` with `eNoise = 102113082` (`noise_ok`), a margin of `32104646` bits. The
sizes are opaque (`irreducible_def`): no power of `2` with a large exponent is evaluated, all
bounds are exponent arithmetic through the generic chain of `Params/NoiseGen.lean`. Every bound is
stated through a named exponent (`ak`, `an`, `ad`, `wP`, `Dmax`, `eWN`, …, `eNoise`).
-/

namespace AdvancedEncryption.DualUse.Params

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.RingBTVW
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_mul_le pow_le_pow' sum_bound)

/-- `K = log₂ q`. -/
irreducible_def Kp : ℕ := 2 ^ 27
/-- The number of digits. -/
def kp : ℕ := Kp + 1
/-- The ring degree. -/
irreducible_def Np : ℕ := 2 ^ 36
/-- The columns of `B₀`. -/
irreducible_def dp : ℕ := 2 ^ 65
/-- `log₂` of the bound on the shifts of the trapdoors. -/
irreducible_def Eτ : ℕ := 51055984
/-- The bits of a coefficient of the big box. -/
irreducible_def Bp : ℕ := 51056224

theorem hkp : 2 ^ Kp < 2 ^ kp := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self Kp)

theorem Np_pos : 0 < Np := by rw [Np_def]; positivity

/-! ### Named bounds

The exponents of the bounds; every statement below is through them. -/

/-- The bound on the depth of the predicates. -/
def Dmax : ℕ := 1054
/-- `k ≤ 2^ak`. -/
def ak : ℕ := 28
/-- `N ≤ 2^an`. -/
def an : ℕ := 36
/-- `|Wd| ≤ 2^ad`. -/
def ad : ℕ := 65
/-- The flooding width: flooding errors below `2^wP`. -/
def wP : ℕ := 768
/-- `|Col k| N ≤ 2^eWN`. -/
def eWN : ℕ := 65
/-- `log₂` of the bound on `modFactor`. -/
def eMod : ℕ := 722
/-- The bound on `treeHeight`. -/
def eTree : ℕ := 66
/-- `gswFactor ≤ 2^eG`. -/
def eG : ℕ := 48440
/-- `gswFactor^Dmax ≤ 2^eGD`. -/
def eGD : ℕ := 51055760
/-- `|rowBits| ≤ 2^eR`. -/
def eR : ℕ := 93
/-- `|rowBits| WN + 1 ≤ 2^eRW`. -/
def eRW : ℕ := 159
/-- `|TrapCol k| ≤ 2^eTC`. -/
def eTC : ℕ := 31
/-- `|Wd| N 2^wP ≤ 2^eE`. -/
def eE : ℕ := 869
/-- `4 · noise + 2 < 2^eNoise ≤ 2^K`. -/
def eNoise : ℕ := 102113082

theorem kp_le : kp ≤ 2 ^ ak := by
  have : 2 ^ 27 + 1 ≤ 2 ^ 28 := by norm_num
  rw [kp, Kp_def]; exact this

theorem two_le_ak : 2 ≤ ak := by norm_num [ak]

theorem Np_le : Np ≤ 2 ^ an := by rw [Np_def]; norm_num [an]

theorem dp_le : dp ≤ 2 ^ ad := by rw [dp_def]; norm_num [ad]

theorem card_colP : Fintype.card (Col kp) = 2 * kp :=
  Gen.card_col kp

theorem WN_le : Fintype.card (Col kp) * Np ≤ 2 ^ eWN :=
  Gen.WN_le kp_le Np_le (by norm_num [ak, an, eWN])

theorem WN1_le : Fintype.card (Col kp) * Np + 1 ≤ 2 ^ (eWN + 1) :=
  Gen.WN1_le kp_le Np_le (by norm_num [ak, an, eWN])

theorem modFactor_le : modFactor (Fintype.card (Col kp) * Np) kp ≤ 2 ^ eMod :=
  Gen.modFactor_le kp_le Np_le two_le_ak (by norm_num [ak, an, eMod])

theorem treeHeight_le : treeHeight Np kp ≤ eTree :=
  Gen.treeHeight_le kp_le Np_le (by norm_num [ak, an, eTree])

theorem gswFactor_le : gswFactor (Fintype.card (Col kp) * Np) Np kp ≤ 2 ^ eG :=
  Gen.gswFactor_le kp_le Np_le two_le_ak (le_refl _) (by norm_num [ak, an, eG])

/-- `G^n` for `n ≤ Dmax`. -/
theorem gswPow_le {n : ℕ} (hn : n ≤ Dmax) :
    gswFactor (Fintype.card (Col kp) * Np) Np kp ^ n ≤ 2 ^ eGD :=
  Gen.gswPow_le gswFactor_le (by norm_num [eG, Dmax, eGD]) hn

theorem R_le : Fintype.card (Fin 1 × Col kp × Fin kp × Fin Np) ≤ 2 ^ eR :=
  Gen.R_le kp_le Np_le (by norm_num [ak, an, eR])

theorem RW_le : Fintype.card (Fin 1 × Col kp × Fin kp × Fin Np) * (Fintype.card (Col kp) * Np) + 1
    ≤ 2 ^ eRW :=
  Gen.RW_le kp_le Np_le (by norm_num [ak, an, eRW])

theorem card_trapColP : Fintype.card (DualUse.TrapCol kp) ≤ 2 ^ eTC :=
  Gen.card_trapCol_le kp_le (by norm_num [ak]) (by norm_num [ak, eTC])

theorem E_le : Fintype.card (Fin dp) * Np * 2 ^ wP ≤ 2 ^ eE :=
  Gen.E_le dp_le Np_le wP (by norm_num [ad, an, wP, eE])

/-- `τ = 2^{Eτ}`: the bound on the shifts of the trapdoors. -/
noncomputable def τp : ℕ := 2 ^ Eτ

/-- **The shift of the simulated trapdoor** for predicates of depth at most `Dmax`. -/
theorem simTrapBound_le {n : ℕ} (hn : n ≤ Dmax) : DualUse.simTrapBound Np kp n ≤ τp :=
  Gen.simTrapBound_le WN_le RW_le (gswPow_le le_rfl) hn
    (by rw [Eτ_def]; norm_num [eWN, eRW, eGD])

/-- **The shift of the real trapdoor** (errors within `16`). -/
theorem realShift_le : (Fintype.card (Col kp) * Np) ^ 2 * 16 ≤ τp :=
  Gen.realShift_le WN_le (by rw [Eτ_def]; norm_num [eWN])

/-- **The noise of a predicate of depth at most `Dmax` is far below `q/4`**, for keys within
`2^{B−1}`. -/
theorem noise_ok {Attr : Type} [Fintype Attr] (f : SLP Attr × Wire Attr)
    (hf : SLP.depth f.1 f.2 ≤ Dmax) (S : ℕ) (hS : S ≤ 2 ^ (Bp - 1)) :
    4 * DualUse.noiseBound (Wd := Fin dp) (Wt := DualUse.TrapCol kp) (N := Np) hkp (2 ^ wP) S f + 2
      < 2 ^ Kp :=
  Gen.noise_ok hkp wP f hf S WN_le RW_le (gswPow_le le_rfl) E_le
    (pow_mul_le (pow_mul_le card_trapColP Np_le) (le_refl (2 ^ wP))) hS
    (by norm_num [eTC, an, wP, eWN, eRW, eGD, eE])
    (by rw [Bp_def, Kp_def]; norm_num [eWN, eRW, eGD, eE])

/-- The exponent of `noise_ok`: `eWN + eRW + eGD + eE + (Bp − 1) + 6 = eNoise ≤ K`. -/
theorem eNoise_eq : eWN + eRW + eGD + eE + (Bp - 1) + 6 = eNoise := by
  rw [Bp_def]; norm_num [eWN, eRW, eGD, eE, eNoise]

theorem eNoise_le : eNoise ≤ Kp := by rw [Kp_def]; norm_num [eNoise]

end AdvancedEncryption.DualUse.Params
