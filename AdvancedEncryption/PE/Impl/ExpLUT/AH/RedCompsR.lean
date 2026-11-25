import PE.Impl.ExpLUT.AH.RedConst
import PE.Impl.ExpLUT.AH.RedSecret
import PE.Impl.ExpLUT.Prog.RedDecode
/-!
# The reduction's data with the decoder and the raw secret fixed (package G2)

`RedComps` with the decoder of `Prog/RedDecode` (`decR D n`, state words `dwR D w`, instances
`instR D`) and the raw secret of `AH/RedSecret` (`RawSec D`, `rawF`, `rawSetup`, `rawEnc`): what is
left are the five component programs and their bounds (`RawComps`).

* `IWR D w`: the state words of instance words (`w = dwR D (enc D i)`), at most `WR D` bits;
* **`RawComps.toRedComps`**: the components and their bounds give a `RedComps`;
* **`attributeHiding_Dc_raw`**: attribute hiding at `Dc` from the registered circular Ring-LWE
  assumption given `RawComps` at `Dc` whose constant satisfies `64 · 2^256 · const ≤ 2^1155`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open SigabaNeo.Lattices.RingLWEWord (encLen)

variable (D : Dims) (kb : KeyBoxes D) (L : ℕ)

/-- The state words of instance words. -/
def IWR (w : List Bool) : Prop := ∃ i : CInst D, w = dwR D (enc D i)

/-- The length of the state words. -/
noncomputable def WR : ℕ := 1 + 2 * (rowsD D * (D.N * D.K))

/-- **The components of the reduction with the raw secret**: the five programs on `R + 2` tapes
(`setupP`: state word and attribute to `rawEnc` of a `rawSetup` sample, …) and their length
bounds, key queries cut at `L`. -/
structure RawComps (impl : Impl sig) (χfl : PMF (Rg D)) where
  /-- The scratch tapes. -/
  R : ℕ
  /-- The admissible raw secrets. -/
  Ok : RawSec D → Prop
  /-- The components. -/
  cs : Comps R (w8Codes (rawEnc D)) (spS D kb L (rawF D) (rawSetup D χfl) impl χfl
    (instR D [])) (setupR D (rawSetup D χfl) (instR D)) (IWR D) Ok
  /-- Their bounds. -/
  cb : CompBoundsP cs L (WR D)

variable {D kb L}

/-- **The `RedComps` of raw components**, with the decoder `decR D n` for instance words of at
most `n ≥ encLen rows N K` bits. -/
noncomputable def RawComps.toRedComps {impl : Impl sig} {χfl : PMF (Rg D)}
    (rc : RawComps D kb L impl χfl) (n : ℕ) (hn : encLen (rowsD D) D.N D.K ≤ n) :
    RedComps D kb L impl χfl where
  R := rc.R
  Sig := RawSec D
  f := rawF D
  setupS := rawSetup D χfl
  map_setupS i x := map_rawSetup D χfl i x
  nS := _
  senc := rawEnc D
  IW := IWR D
  Ok := rc.Ok
  W := WR D
  instOf := instR D
  cs := rc.cs
  cb := rc.cb
  P := decR D n
  dw := dwR D
  run_P i := run_decR D n hn i
  instOf_dw i := instR_dwR D i
  iw i := ⟨⟨i, rfl⟩, le_of_eq (length_dwR_enc D i), by rw [head_dwR_enc]; simp⟩
  La := (mpkEnc D).len + (skEnc D).len + (ctEnc D).len
  pubL := by omega
  keyL := by omega
  chalL := by omega

open AdvancedEncryption.ExpLUT.Params in
/-- **Attribute hiding at the concrete parameters from raw components**: given the five component
programs of the reduction (on the raw secret, with the decoder `decR Dc nDc`) whose constant
satisfies `64 · 2^256 · const ≤ 2^1155`. -/
theorem attributeHiding_Dc_raw (hR : CircularRingLWE.decision.Holds) {impl : Impl sig}
    {kb : KeyBoxes Dc} {L : ℕ} (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound)
    (hL : predLen ≤ L) (rc : RawComps Dc kb L impl χfl)
    (hC : 64 * ((2 : ℝ) ^ 128) ^ 2 * ((rc.toRedComps nDc encLen_le_nDc).const : ℝ) ≤ (2 : ℝ) ^ 1155) :
    AttributeHiding (univ w8) params impl :=
  attributeHiding_Dc_comps hR hI hkb hL (rc.toRedComps nDc encLen_le_nDc) hC

end AdvancedEncryption.ExpLUT.Prog
