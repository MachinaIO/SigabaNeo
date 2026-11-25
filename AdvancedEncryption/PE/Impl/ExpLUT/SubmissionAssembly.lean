import PE.Impl.ExpLUT.SubmissionDec
import PE.Impl.ExpLUT.Prog.RedSetupPSize
import PE.Impl.ExpLUT.Prog.RedPubPComps
import PE.Impl.ExpLUT.Prog.RedChalDc
import PE.Impl.ExpLUT.Prog.AuthWX

/-!
# The reduction's components at `Dc`, with the key component as the only input

`KeyComp`: what the key component `keyP` must provide (on `247` tapes, `R = 245`): WF, the
`law_key` field against `spS`, an output bound `≤ 2^125`, a clock `≤ 2^450` and at most `2^200`
states. **`rawCompsOf kc`** assembles `setupRX`, `pubP`, `keyP`, `authWX`, `chalP`;
**`spec_of_keyComp`**: the final statement from a `KeyComp`.
-/

namespace AdvancedEncryption.ExpLUT.Sub

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.ExpLUT AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Params

/-- The codes of the raw secret. -/
noncomputable abbrev cdR : Codes (univ w8) (RawSec Dc) := w8Codes (rawEnc Dc)

/-- The specification served by the handlers. -/
noncomputable abbrev spR : Generic.Spec (univ w8) (RawSec Dc) :=
  spS Dc kbDc predLen (rawF Dc) (rawSetup Dc χfl) implX χfl (instR Dc [])

/-- **What the key component must provide.** -/
structure KeyComp where
  keyP : XProg 247
  wf : keyP.WF
  law : ∀ σ C, XProg.law keyP (io2 (R := 245) (cdR.sig.enc σ) C []) =
    (spR.key σ C).map fun sk => io2 (R := 245) sk [] []
  Lk : ℕ
  hLk : Lk ≤ 2 ^ 125
  len : XProg.lenBoundT keyP (io2 (R := 245) (sigBound cdR (WR Dc)) predLen 0) ≤
    io2 (R := 245) Lk 0 0
  time : XProg.timeBoundT keyP (io2 (R := 245) (sigBound cdR (WR Dc)) predLen 0) ≤ 2 ^ 450
  size : keyP.size ≤ 2 ^ 200

theorem h38 : 38 ≤ 245 := by norm_num
theorem h14 : 14 ≤ 245 := by norm_num

/-- The five components. -/
noncomputable def compsOf (kc : KeyComp) :
    Comps 245 cdR spR (setupR Dc (rawSetup Dc χfl) (instR Dc)) (IWR Dc) (fun _ => True) where
  setupP := setupRX Dc h38 eFl
  pubP := RedPubP.pubP Dc
  keyP := kc.keyP
  authP := authWX h14
  chalP := RedChal.chalP Dc
  wf_setup := wf_setupRX (D := Dc) h38 eFl
  wf_pub := RedPubP.pubP_Dc_spec.1
  wf_key := kc.wf
  wf_auth := wf_authWX h14
  wf_chal := (RedChal.chalP_Dc_spec kbDc predLen implX χfl (instR Dc [])).1
  law_setup w x hw := law_setupRX_Dc h38 w x hw
  ok_setup _ _ _ _ _ := trivial
  law_pub σ _ := RedPubP.law_pub_spS kbDc predLen (rawSetup Dc χfl) implX χfl (instR Dc []) σ trivial
  law_key σ C _ := kc.law σ C
  law_auth C x := law_authWX h14 rfl C x
  law_chal σ μ _ := (RedChal.chalP_Dc_spec kbDc predLen implX χfl (instR Dc [])).2.1 σ μ

/-- Their bounds. -/
noncomputable def boundsOf (kc : KeyComp) : CompBoundsP (compsOf kc) predLen (WR Dc) where
  Ssig := 2 ^ 101
  Lp := 2 ^ 102
  Lk := kc.Lk
  La := 1
  Lc := 2 ^ 110
  len_setup := len_setupRX_Dc h38
  len_pub := RedPubP.pubP_Dc_spec.2.2.1
  len_key := kc.len
  len_auth := len_authWX h14 _ _
  len_chal := (RedChal.chalP_Dc_spec kbDc predLen implX χfl (instR Dc [])).2.2.1

/-- **The reduction's raw components from the key component.** -/
noncomputable def rawCompsOf (kc : KeyComp) : RawComps Dc kbDc predLen implX χfl where
  R := 245
  Ok := fun _ => True
  cs := compsOf kc
  cb := boundsOf kc

set_option exponentiation.threshold 2000 in
theorem compTime_le (kc : KeyComp) : compTimeP (boundsOf kc) ≤ 2 ^ 500 := by
  have h1 := time_setupRX_Dc h38
  have h2 := RedPubP.pubP_Dc_spec.2.2.2.1
  have h3 := kc.time
  have h4 : XProg.timeBoundT (authWX h14) (io2 (R := 245) predLen cdR.nA 0) ≤ 2 ^ 109 :=
    time_authWX h14 (by norm_num [predLen]) le_rfl
  have h5 := (RedChal.chalP_Dc_spec kbDc predLen implX χfl (instR Dc [])).2.2.2.1
  show XProg.timeBoundT (setupRX Dc h38 eFl) _ + XProg.timeBoundT (RedPubP.pubP Dc) _ +
    XProg.timeBoundT kc.keyP _ + XProg.timeBoundT (authWX h14) _ +
    XProg.timeBoundT (RedChal.chalP Dc) _ ≤ _
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) ?_
  norm_num

set_option exponentiation.threshold 2000 in
theorem size_le (kc : KeyComp) :
    2 * ((setupRX Dc h38 eFl).size + (RedPubP.pubP Dc).size) + kc.keyP.size +
      (authWX h14).size + (RedChal.chalP Dc).size ≤ 2 ^ 240 := by
  have h1 := size_setupRX_Dc h38
  have h2 := RedPubP.pubP_Dc_spec.2.2.2.2
  have h3 := kc.size
  have h4 := size_authWX h14
  have h5 := (RedChal.chalP_Dc_spec kbDc predLen implX χfl (instR Dc [])).2.2.2.2
  refine le_trans (add_le_add (add_le_add (add_le_add (Nat.mul_le_mul_left 2
    (add_le_add h1 h2)) h3) h4) h5) ?_
  norm_num

set_option exponentiation.threshold 2000 in
/-- **The final statement from the key component.** -/
theorem spec_of_keyComp (kc : KeyComp) :
    Spec (BranchingProgram.primitive BranchingProgram.w8) registry
      (submissionOf TapeDec.decMachineP decMachine_det Ncost) :=
  spec_of_rawComps (rawCompsOf kc) (by norm_num [rawCompsOf]) (size_le kc) (compTime_le kc)
    (show (2 : ℕ) ^ 101 ≤ 2 ^ 125 from Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (show (2 : ℕ) ^ 102 ≤ 2 ^ 125 from Nat.pow_le_pow_right (by norm_num) (by norm_num)) kc.hLk
    (show (1 : ℕ) ≤ 2 ^ 125 from Nat.one_le_two_pow)
    (show (2 : ℕ) ^ 110 ≤ 2 ^ 125 from Nat.pow_le_pow_right (by norm_num) (by norm_num))

end AdvancedEncryption.ExpLUT.Sub
