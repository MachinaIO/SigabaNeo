import PE.Impl.ExpLUT.Prog.RedSetupP
import PE.Impl.ExpLUT.Prog.EncSamplersConf

/-!
# The setup component of the reduction at the concrete parameters (package G2, item 2)

The counts of the raw secret in closed form (`nU_eq`, `nFl_eq`, `nZ_eq`, `nS_rawEnc`: no
enumeration of a large index type is evaluated), then, for dimensions with `e = 24`,
`K = 2^16`, `b = 22`, `m̄ = 3 · 2^40 + 408` and the flooding width `400` (`decide +kernel` on
numerals only):

* the handlers' input bound `stateBound (w8Codes (rawEnc D)) (WR D) ≤ 2^99`;
* **`time_setupRX_conf`**: `timeBoundT (setupRX D hR e) (io2 (stateBound …) 128 0) ≤ 2^205`;
* **`len_setupRX_conf`**: `lenBoundT … ≤ io2 (2^101) 0 0`;

and at `Dc` with `e = eFl` (`χfl = floodR Dc eFl`): **`law_setupRX_Dc`**, **`time_setupRX_Dc`**,
**`len_setupRX_Dc`**.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.PE.Generic

/-! ### The counts in closed form -/

theorem len_pos : (Enum.list (α := Pos)).length = 16 := len_fin 16

theorem nU_eq (D : Dims) : nU D = D.mb + D.K + D.b * 2 * (2 * D.K) + 1 := by
  simp only [nU, len_sum, Enum.length_prod, len_fin]
  omega

theorem nFl_eq (D : Dims) : nFl D = D.b * (2 * (2 * D.K * D.K)) * (2 * D.K) +
    (16 * (2 * D.K) + (16 * (2 * (2 * D.K * D.K)) * (2 * D.K) + 2 * D.K)) := by
  simp only [nFl, Enum.length_prod, len_fin, w8_len]

theorem nZ_eq (D : Dims) : nZ D = (16 * (2 * D.K) + (2 * D.K + (16 * (2 * (2 * D.K * D.K) *
    (2 * D.K)) + D.b * (2 * (2 * D.K * D.K) * (2 * D.K))))) * D.mb := by
  show (Enum.list (α := (Pos × Col D.K) ⊕ Col D.K ⊕ (Pos × Dig D.K × Col D.K) ⊕
    (Fin D.b × Dig D.K × Col D.K))).length * (Enum.list (α := Fin D.mb)).length = _
  simp only [len_sum, Enum.length_prod, len_fin, w8_len]

/-- **The length of the raw secret's word.** -/
theorem nS_rawEnc (D : Dims) : (w8Codes (rawEnc D)).nS = 128 + (2 * (rowsD D * (D.N * D.K)) +
    (nU D * (D.N * D.K) + (nFl D * (D.N * D.K) + nZ D))) := by
  show 128 + ((Enum.list (α := Fin (rowsD D))).length * (D.N * D.K) +
      (Enum.list (α := Fin (rowsD D))).length * (D.N * D.K) +
    ((Enum.list (α := BCol (Wb D) D.K)).length * (D.N * D.K) +
      ((Enum.list (α := Jh D)).length * ((Enum.list (α := Col D.K)).length * (D.N * D.K)) +
      (D.N * D.K +
    (((Enum.list (α := Fin D.b)).length * ((Enum.list (α := Dig D.K)).length *
        ((Enum.list (α := Col D.K)).length * (D.N * D.K))) +
      ((Enum.list (α := Pos)).length * ((Enum.list (α := Col D.K)).length * (D.N * D.K)) +
      ((Enum.list (α := Pos)).length * ((Enum.list (α := Dig D.K)).length *
        ((Enum.list (α := Col D.K)).length * (D.N * D.K))) +
        (Enum.list (α := Col D.K)).length * (D.N * D.K)))) +
     (Enum.list (α := PrI (setting D) Pos)).length * ((Enum.list (α := Wb D)).length * 1)))))) = _
  simp only [nU, nFl, nZ, len_prodE, len_fin]
  ring

/-! ### The concrete dimensions -/

section Conf

variable (D : Dims) (he : D.e = 24) (hK : D.K = 2 ^ 16) (hb : D.b = 22)
  (hmb : D.mb = 3 * 2 ^ 40 + 408)
include he hK hb hmb

/-- The handlers' input bound for the setup component. -/
theorem stateBound_raw_conf : stateBound (w8Codes (rawEnc D)) (WR D) ≤ 2 ^ 99 := by
  unfold stateBound WR
  refine max_le ?_ ?_
  · rw [rowsD_eq, mCirc]
    simp only [Dims.N, he, hK, hb, hmb]
    decide +kernel
  · show 1 + 128 + (w8Codes (rawEnc D)).nS + 3 ≤ _
    rw [nS_rawEnc, rowsD_eq, mCirc, nU_eq, nFl_eq, nZ_eq]
    simp only [Dims.N, he, hK, hb, hmb]
    decide +kernel

variable {e : ℕ} (hfl : e = 400)
include hfl

theorem rsHyp_conf : RsHyp D e (2 ^ 99) (2 ^ 100) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mU, nU_eq, Dims.N, he, hK, hb, hmb]; decide +kernel
  · rw [hK]; norm_num
  · simp only [nU_eq, Dims.N, he, hK, hb, hmb]; decide +kernel
  · simp only [bFl, mU, nU_eq, nFl_eq, Dims.N, he, hK, hb, hmb, hfl]; decide +kernel
  · simp only [bFl, bZr, mU, nU_eq, nFl_eq, nZ_eq, Dims.N, he, hK, hb, hmb, hfl]; decide +kernel

set_option maxRecDepth 100000 in
theorem rsT_conf : rsT D e (2 ^ 99) (2 ^ 100) ≤ 2 ^ 205 := by
  simp only [rsT, rsM, bFl, bZr, mU, nU_eq, nFl_eq, nZ_eq, Dims.N, he, hK, hb, hmb, hfl]
  decide +kernel

theorem rsL_conf : rsL D e (2 ^ 100) ≤ 2 ^ 101 := by
  simp only [rsL, bFl, bZr, mU, nU_eq, nFl_eq, nZ_eq, Dims.N, he, hK, hb, hmb, hfl]
  decide +kernel

/-- **The time of the setup component** at the concrete dimensions: at most `2^205` steps. -/
theorem time_setupRX_conf {R : ℕ} (hR : 38 ≤ R) :
    XProg.timeBoundT (setupRX D hR e)
      (io2 (R := R) (stateBound (w8Codes (rawEnc D)) (WR D)) (w8Codes (rawEnc D)).nA 0) ≤
      2 ^ 205 :=
  (time_setupRX hR e (2 ^ 99) (2 ^ 100) (stateBound_raw_conf D he hK hb hmb) (le_refl 128)
    (rsHyp_conf D he hK hb hmb hfl)).trans (rsT_conf D he hK hb hmb hfl)

/-- **The output of the setup component** at the concrete dimensions: at most `2^101` bits on
tape `0`, every other tape blank. -/
theorem len_setupRX_conf {R : ℕ} (hR : 38 ≤ R) :
    XProg.lenBoundT (setupRX D hR e)
      (io2 (R := R) (stateBound (w8Codes (rawEnc D)) (WR D)) (w8Codes (rawEnc D)).nA 0) ≤
      io2 (R := R) (2 ^ 101) 0 0 := by
  refine (len_setupRX hR e (2 ^ 99) (2 ^ 100) (stateBound_raw_conf D he hK hb hmb) (le_refl 128)
    (rsHyp_conf D he hK hb hmb hfl)).trans fun t => ?_
  have := rsL_conf D he hK hb hmb hfl
  simp only [io2_apply]; split_ifs <;> omega

end Conf

/-! ### At `Dc` -/

section Dc

open AdvancedEncryption.ExpLUT.Params EncConf

theorem eFl_lt_Dc : eFl < Dc.K := by show eFl < Kc; rw [eFl_def, Kc_def]; norm_num

/-- **The law of the setup component at `Dc`** (the `law_setup` field of `RawComps Dc kb L impl
χfl`). -/
theorem law_setupRX_Dc {R : ℕ} (hR : 38 ≤ R) (w : List Bool) (x : Attribute w8) (hw : IWR Dc w) :
    (setupRX Dc hR eFl).law (io2 (R := R) w (encAttribute w8 x) []) =
      (setupR Dc (rawSetup Dc χfl) (instR Dc) w x).map
        fun σ => io2 (R := R) ((rawEnc Dc).enc σ) [] [] :=
  law_setupRX hR eFl_lt_Dc w x hw

/-- **The time of the setup component at `Dc`**: at most `2^205` steps. -/
theorem time_setupRX_Dc {R : ℕ} (hR : 38 ≤ R) :
    XProg.timeBoundT (setupRX Dc hR eFl)
      (io2 (R := R) (stateBound (w8Codes (rawEnc Dc)) (WR Dc)) (w8Codes (rawEnc Dc)).nA 0) ≤
      2 ^ 205 :=
  time_setupRX_conf Dc rfl EncConf.Dc_K rfl EncConf.Dc_mb eFl_def hR

/-- **The output of the setup component at `Dc`**: at most `2^101` bits, the other tapes blank
(the `len_setup` field with `Ssig = 2^101`). -/
theorem len_setupRX_Dc {R : ℕ} (hR : 38 ≤ R) :
    XProg.lenBoundT (setupRX Dc hR eFl)
      (io2 (R := R) (stateBound (w8Codes (rawEnc Dc)) (WR Dc)) (w8Codes (rawEnc Dc)).nA 0) ≤
      io2 (R := R) (2 ^ 101) 0 0 :=
  len_setupRX_conf Dc rfl EncConf.Dc_K rfl EncConf.Dc_mb eFl_def hR

end Dc

end AdvancedEncryption.ExpLUT.Prog
