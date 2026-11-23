import PE.Impl.DualUse.AHConcreteV
import PE.Impl.DualUse.ReductionCompsBoundG
import PE.Impl.Game.HandlersBP

/-!
# Attribute hiding for branching programs: the pieces that do not wait for the switch

Stage II preparation (BP plan §4.3, §4.4, WS8). Everything here is generic in the numbers; the
switch (`PUniv := bpUniverse`, `confA`) only instantiates it.

* **Statistical terms** (`statTerm_le_gen`, `stat_of_le`): if the attributes are at most `2^a`
  and `δ₁, δ₆, ε ≤ 2^{-(a + s + 3)}`, then `statTerm ≤ 2^{-s}`, and `4 · 2^λ · statTerm² ≤ 1` as
  soon as `λ + 2 ≤ 2 s`. For `bpUniverse`: `a = 128` (`card_attr`), WS2's `δ₁, δ₆ ≤ 2^{-370}` and
  `ε ≤ 2^{-499}` give `s = 239` (`statTerm_bp`); `2 · 239 ≥ 130`.
* **The constant at the numbers of the branching-program universe** (`compBoundBP_le`): codes
  `nA = 128`, `nM = 1`, parameter word `515` bits (`length_paramsWord_bp`), decoder `≤ 2^16`
  states, `≤ 2^350` steps, `14` tapes; components with `R` scratch tapes, `Sz2 ≤ 2^199` states
  (the key component's public-key prefixes `264 · lenPK`, `lenPK = 8 nA k³ N² K = 2^190` at
  `confA`), the cut `c.L ≤ 2^49` (`bpLen = 481 · 2^40`), slope `≤ 2^660`:
  **`C ≤ 2^233 · 3^(44 + R)`**.
* **The strength** (`kb_bp`, `attributeHiding_of_constExp`): `kb ≥ 6 + 2 · 128 + log₂ C`. With
  the components at `R = 254 + tc` tapes (`tc`: the tapes the compiler adds to the key component,
  a parameter until WS5 fixes it), `log₂ C ≤ 233 + 1.585 (298 + tc)`:

  | `tc` | 0 | 32 | 64 | 96 | 120 | 121 |
  | --- | --- | --- | --- | --- | --- | --- |
  | `kb` (proved bound) | 968 | 1019 | **1069** | 1120 | 1158 | 1160 |

  `kb_bp_64 : 64 · (2^128)² · (2^233 · 3^362) ≤ 2^1069`. With `tc ≤ 120` the strength needed is
  at most `1158`, the strength WS3 estimates for ring degree `2^35`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 3000

/-! ### Statistical terms, generic -/

section Stat

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- **The statistical part from exponents**: attributes at most `2^a`, every term at most
`2^{-(a + s + 3)}`; then `statTerm ≤ 2^{-s}`. -/
theorem statTerm_le_gen {ε : ℝ≥0∞} (a s : ℕ)
    (hA : (Fintype.card PUniv.Attr : ℝ≥0∞) ≤ 2 ^ a)
    (h1 : delta1 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹)
    (h6 : delta6 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹)
    (hε : ε ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹) :
    statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹ := by
  set x : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (s + 3))⁻¹
  have m : ∀ {δ : ℝ≥0∞}, δ ≤ ((2 : ℝ≥0∞) ^ (a + (s + 3)))⁻¹ →
      (Fintype.card PUniv.Attr : ℝ≥0∞) * δ ≤ x := fun h =>
    card_mul_le (a := a) (t := s + 3) hA le_rfl h
  unfold statTerm
  calc _ ≤ x + x + x + x + x := by
        gcongr
        exacts [m h1, m hε, m h6, m h1, m h1]
    _ = 5 * x := by ring
    _ ≤ 2 ^ 3 * x := by gcongr; norm_num
    _ = ((2 : ℝ≥0∞) ^ s)⁻¹ := by
        show (2 : ℝ≥0∞) ^ 3 * ((2 : ℝ≥0∞) ^ (s + 3))⁻¹ = _
        rw [Nat.add_comm s 3]; exact two_pow_mul_inv 3 s

/-- **The statistical condition of the hybrid argument from an exponent**: `statTerm ≤ 2^{-s}`
and `λ + 2 ≤ 2 s` give `4 · 2^λ · statTerm² ≤ 1`. -/
theorem stat_of_le {ε : ℝ≥0∞} (s : ℕ) (h : statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹)
    (hs : params.secBits + 2 ≤ 2 * s) :
    4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1 := by
  have h' := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) h
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h'
  have h0 := ENNReal.toReal_nonneg (a := statTerm c hk ε)
  generalize (statTerm c hk ε).toReal = r at *
  have hr : r ^ 2 ≤ (((2 : ℝ) ^ s)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h' 2
  generalize params.secBits = l at *
  calc 4 * (2 : ℝ) ^ l * r ^ 2 ≤ 2 ^ 2 * 2 ^ l * (((2 : ℝ) ^ s)⁻¹) ^ 2 := by
        gcongr; norm_num
    _ = 2 ^ (l + 2) / 2 ^ (2 * s) := by rw [← pow_add, inv_pow, ← pow_mul]; ring_nf
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact pow_le_pow_right₀ (by norm_num) hs

theorem statTerm_ne_top_of_le {ε : ℝ≥0∞} {s : ℕ} (h : statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹) :
    statTerm c hk ε ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero)) h

/-- **The statistical part at the numbers of the branching-program universe** (BP plan §4.4):
`2^128` attributes, `δ₁, δ₆ ≤ 2^{-370}`, `ε ≤ 2^{-499}` (WS2): `statTerm ≤ 2^{-239}`, and the
condition `4 · 2^λ · statTerm² ≤ 1` holds. -/
theorem statTerm_bp {ε : ℝ≥0∞} (hA : (Fintype.card PUniv.Attr : ℝ≥0∞) ≤ 2 ^ 128)
    (h1 : delta1 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ 370)⁻¹)
    (h6 : delta6 (Sdw (N := N) hk) (Fin c.d) ≤ ((2 : ℝ≥0∞) ^ 370)⁻¹)
    (hε : ε ≤ ((2 : ℝ≥0∞) ^ 499)⁻¹) :
    statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ 239)⁻¹ ∧
      4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1 := by
  have hle : ∀ {e : ℕ}, 370 ≤ e → ((2 : ℝ≥0∞) ^ e)⁻¹ ≤ ((2 : ℝ≥0∞) ^ (128 + (239 + 3)))⁻¹ :=
    fun he => ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by omega))
  have h := statTerm_le_gen (c := c) 128 239 hA (h1.trans (hle le_rfl)) (h6.trans (hle le_rfl))
    (hε.trans (hle (by norm_num)))
  exact ⟨h, stat_of_le 239 h (by show 128 + 2 ≤ 2 * 239; norm_num)⟩

end Stat

/-! ### The constant at the numbers of the branching-program universe -/

/-- **The reductions' constant for the branching-program codes**: `nA = 128`, `nM = 1`, the
parameter word of `515` bits; a decoder of at most `2^16` states, `2^350` steps and `14` tapes;
`254 ≤ R ≤ 370` scratch tapes of the components, their states `Sz2 ≤ 2^199`, the cut `≤ 2^49`, the
slope `≤ 2^660`: at most `2^233 · 3^(14 + R + 30)`. -/
theorem compBoundBP_le {tP R Sz2 Lc Sl : ℕ} (htP : tP ≤ 2 ^ 350) (hR0 : 254 ≤ R) (hR : R ≤ 370)
    (hSz : Sz2 ≤ 2 ^ 199) (hLc : Lc ≤ 2 ^ 49) (hSl : Sl ≤ 2 ^ 660) :
    compBoundG 128 1 515 (2 ^ 16) tP 14 R Sz2 Lc Sl 660 ≤ 2 ^ 233 * 3 ^ (14 + R + 30) := by
  have hS : compStatesG 128 1 515 (2 ^ 16) Sz2 Lc 660 ≤
      compStatesG 128 1 515 (2 ^ 16) (2 ^ 199) (2 ^ 49) 660 :=
    compStatesG_mono le_rfl hSz hLc
  have hS0 : compStatesG 128 1 515 (2 ^ 16) (2 ^ 199) (2 ^ 49) 660 < 2 ^ 215 := by
    unfold compStatesG postStatesG glue3; norm_num
  have hz : Nat.size (compStatesG 128 1 515 (2 ^ 16) Sz2 Lc 660) ≤ 215 :=
    Nat.size_le.mpr (hS.trans_lt hS0)
  have h3 : (1 : ℕ) ≤ 3 ^ (14 + R + 30) := Nat.one_le_pow _ _ (by norm_num)
  have h44 : (3 : ℕ) ^ 298 ≤ 3 ^ (14 + R + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold compBoundG
  generalize hT : (3 : ℕ) ^ (14 + R + 30) = T at *
  generalize compStatesG 128 1 515 (2 ^ 16) Sz2 Lc 660 = S at *
  generalize Nat.size S = z at *
  have hS' := (hS.trans hS0.le)
  have hA : 60 * S * T * (5 + 4 * (14 + R + 30) + z) ≤ 2 ^ 232 * T := by
    have : 5 + 4 * (14 + R + 30) + z ≤ 1876 := by omega
    calc 60 * S * T * (5 + 4 * (14 + R + 30) + z) ≤ 60 * 2 ^ 215 * T * 1876 := by gcongr
      _ = (60 * 2 ^ 215 * 1876) * T := by ring
      _ ≤ 2 ^ 232 * T := by gcongr; norm_num
  have hB : 11 * tP + 11 * Sl + 24 ≤ 2 ^ 232 * T := by
    have : 11 * tP + 11 * Sl + 24 ≤ 2 ^ 232 * 3 ^ 298 := by
      have : 11 * (2 : ℕ) ^ 350 + 11 * 2 ^ 660 + 24 ≤ 2 ^ 232 * 3 ^ 298 := by norm_num
      omega
    exact this.trans (Nat.mul_le_mul_left _ h44)
  calc _ ≤ 2 ^ 232 * T + 2 ^ 232 * T := by omega
    _ = 2 ^ 233 * T := by ring

/-- **The strength from the constant**: `64 · (2^128)² · 2^233 · 3^(298 + tc) ≤ 2^kb` with
`kb = 495 + ⌈log₂ 3^(298 + tc)⌉`. -/
theorem kb_bp (tc : ℕ) :
    64 * ((2 : ℝ) ^ 128) ^ 2 * ((2 : ℝ) ^ 233 * 3 ^ (298 + tc)) ≤
      2 ^ (495 + Nat.clog 2 (3 ^ (298 + tc))) := by
  have h : ((3 ^ (298 + tc) : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (3 ^ (298 + tc)) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.le_pow_clog (by norm_num) _)
  push_cast at h
  have e : (64 : ℝ) * ((2 : ℝ) ^ 128) ^ 2 * 2 ^ 233 = 2 ^ 495 := by norm_num
  calc 64 * ((2 : ℝ) ^ 128) ^ 2 * ((2 : ℝ) ^ 233 * 3 ^ (298 + tc)) =
        (64 * ((2 : ℝ) ^ 128) ^ 2 * 2 ^ 233) * 3 ^ (298 + tc) := by ring
    _ = 2 ^ 495 * 3 ^ (298 + tc) := by rw [e]
    _ ≤ 2 ^ 495 * 2 ^ Nat.clog 2 (3 ^ (298 + tc)) := by gcongr
    _ = 2 ^ (495 + Nat.clog 2 (3 ^ (298 + tc))) := (pow_add 2 495 _).symm

/-- **The strength at `tc = 64`** (the compiler's tapes, BP plan §5.2): `2^1069`. -/
theorem kb_bp_64 : 64 * ((2 : ℝ) ^ 128) ^ 2 * ((2 : ℝ) ^ 233 * 3 ^ (298 + 64)) ≤ 2 ^ 1069 := by
  norm_num

/-- **The largest `tc` for ring degree `2^35`**: at `tc = 120` the strength needed is `≤ 1158`. -/
theorem kb_bp_120 : 64 * ((2 : ℝ) ^ 128) ^ 2 * ((2 : ℝ) ^ 233 * 3 ^ (298 + 120)) ≤ 2 ^ 1158 := by
  norm_num

/-! ### Attribute hiding from an exponent of the constant -/

section AH

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d] {ms : Machines hk c}

/-- **Attribute hiding from bounds on the three reductions' constants** (any configuration): the
constants at most `C`, `64 · (2^λ)² · C ≤ 2^kb`, the statistical part at most `2^{-s}` with
`λ + 2 ≤ 2 s`. The switch instantiates it with the bundles at `confA`, `C = 2^233 · 3^(298 + tc)`
(`compBoundBP_le`) and `statTerm_bp`. -/
theorem attributeHiding_of_constBound
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u) (hcov : RealCovered hk c)
    (hL : bpLen ≤ c.L) (hscov : SimCovered hk c) {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (s : ℕ) (hS : statTerm c hk ε ≤ ((2 : ℝ≥0∞) ^ s)⁻¹) (hs : params.secBits + 2 ≤ 2 * s)
    (err : SecretDist) (hχ : χR c = polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))
    (B3 : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setup3 hk c) (view3 hk c) (sd3 hk c))
    (B5 : Bundle hk c (inst5Enc (N := N) (K := K) (k := k) c.d) (setup5 hk c) (view5 hk c)
      (sd5 hk c))
    (BI : Bundle hk c (inst3Enc (N := N) (K := K) (k := k)) (setupI hk c) (viewI hk c) (sdI hk c))
    (kb : ℕ) (C : ℝ) (hC : 0 < C)
    (hC3 : (B3.const (dec3M N K k) : ℝ) ≤ C) (hC5 : (B5.const (dec5M N K k c.d) : ℝ) ≤ C)
    (hCI : (BI.const (dec3M N K k) : ℝ) ≤ C)
    (hk64 : 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * C ≤ (2 : ℝ) ^ kb)
    (hard3 : RingLWE.decision.HardAt (params3 N (2 ^ K) k err) kb)
    (hard5 : RingLWE.decision.HardAt (params5 N (2 ^ K) k (Fin c.d) err) kb) :
    AttributeHiding PUniv params (impl hk c ms) :=
  attributeHiding_of_comps_rlwe hdec hcov hL hscov hflood (statTerm_ne_top_of_le hS)
    (stat_of_le s hS hs) err hχ B3 B5 BI kb C hC hC3 hC5 hCI hk64 hard3 hard5

end AH

end AdvancedEncryption.DualUse
