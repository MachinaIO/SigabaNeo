import PE.Impl.ExpLUT.Prog.KeyTightTailY
import PE.Impl.ExpLUT.Prog.KeyTightEval2

/-!
# KeyGen: the tight clock of the machine

`validP = enterP ; keyPrepareC ; sampleP ; candidateTryC ; packKeyC ; post`, with F3's enter and
preparation of `KeyTightEval2` (tight chain, exact evaluator bounds) and the tight attempt `KeyTightY.ktTryCert` (cap `2^121`). The rest of
the machine (parser, length check, invalid branch, frame, length guard) is F3's
(`KeyTimeFront`), recomposed with the new branch bound.

* `KeyTight.cert_validP_tight : Cert (validP Dc Bk rSmall) a (outputBounds 2^121) TV`;
* **`KeyCore.time_keyMachine_tight : keyMachine.time ≤ 2^T1`**.
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2000
set_option maxRecDepth 100000

namespace AdvancedEncryption.ExpLUT.Prog.KeyTight

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.MVM Cslib
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime
open AdvancedEncryption.ExpLUT.Prog.KeyCore
open AdvancedEncryption.ExpLUT.Prog.EncW (XBound)
open AdvancedEncryption.ExpLUT.Params

/-- The time of the valid branch. -/
abbrev TV : ℕ := 2 ^ 384 + 2 ^ 382

theorem cert_validP_tight (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ 2 ^ 120) :
    Cert (KeyCore.validP Dc Bk rSmall) a (outputBounds (2 ^ 121)) TV := by
  have p0 := cert_enterP_Dc a ht
  have p1 := t2KeyPrepareC_Dc preparedBounds preparedBounds_inputs
  have p2 := KeyTightY.ktSampleCert.mono KeyTightY.prepared_le_inY le_rfl le_rfl
  have all := p0.seq ((p1.seq (p2.seq KeyTightY.ktTryCert)).seq KeyTightY.ktPackPostCert)
  exact all.mono le_rfl le_rfl (by norm_num)

theorem bounds_branches_tight :
    XBound (.ifBit 2 (validP Dc Bk rSmall) (invalidP Dc)) (2 ^ 120) (2 ^ 384 + 2 ^ 383)
      (2 ^ 121) := by
  have hv : XBound (validP Dc Bk rSmall) (2 ^ 120) TV (2 ^ 121) := fun ℓ hℓ => by
    have c := cert_validP_tight ℓ hℓ
    refine ⟨c.time, fun t => (c.len t).trans ?_⟩
    simp only [KeyTime.outputBounds]; split_ifs <;> norm_num
  have hi : XBound (invalidP Dc) (2 ^ 120) (2 ^ 254) (2 ^ 121) := fun ℓ hℓ => by
    have c := KeyTime.cert_invalidP_Dc ℓ hℓ
    refine ⟨c.time, fun t => (c.len t).trans ?_⟩
    simp only [KeyTime.outputBounds]; split_ifs <;> norm_num
  exact (xbound_ifBit hv hi).mono (by norm_num) le_rfl

theorem bounds_keyProgram_tight :
    XBound (keyProgram Dc Bk rSmall) (2 ^ 105) (2 ^ 384 + 2 ^ 383 + 2 ^ 252) (2 ^ 123) := by
  have hp : XBound (.prog parse) (2 ^ 105) (2 ^ 230) (2 ^ 120) :=
    (xbound_prog bounds_keyParse).mono le_rfl (by norm_num)
  have hc : XBound (.prog checkP) (2 ^ 120) (2 ^ 250) (2 ^ 120) :=
    (xbound_prog (bounds_checkP (by norm_num [predLen]) (by norm_num))).mono
      (by norm_num [predLen]) le_rfl
  have h := hp.seq ((hc.seq bounds_branches_tight).seq bounds_frameKeyP)
  exact h.mono (by norm_num) le_rfl

theorem bounds_keyGuardP_tight (n : ℕ) :
    XBound (keyGuardP Dc Bk rSmall n) (2 ^ 104) (leT n (2 ^ 104) + (2 ^ 384 + 2 ^ 383 + 2 ^ 253))
      (2 ^ 123) := by
  have hg : XBound (.prog (guardP n)) (2 ^ 104) (leT n (2 ^ 104)) (2 ^ 105) :=
    (xbound_prog (ubp_guardP n (2 ^ 104))).mono le_rfl (by norm_num)
  have hk : XBound (.seq (.prog (clr 103)) (keyProgram Dc Bk rSmall)) (2 ^ 105)
      (2 * (2 ^ 105 + 1) + 3 + (2 ^ 384 + 2 ^ 383 + 2 ^ 252)) (2 ^ 123) :=
    (xbound_prog (ubp_prim0 (.clear (103 : Fin 105)) rfl (2 ^ 105))).seq bounds_keyProgram_tight
  have hz : XBound (.prog (clr (0 : Fin 105))) (2 ^ 105) (2 * (2 ^ 105 + 1) + 3) (2 ^ 123) :=
    (xbound_prog (ubp_prim0 (.clear (0 : Fin 105)) rfl (2 ^ 105))).mono le_rfl (by norm_num)
  exact (hg.seq (xbound_ifBit hk hz)).mono (by
    have : max (2 * (2 ^ 105 + 1) + 3 + (2 ^ 384 + 2 ^ 383 + 2 ^ 252)) (2 * (2 ^ 105 + 1) + 3) + 1 ≤
        2 ^ 384 + 2 ^ 383 + 2 ^ 253 := by
      norm_num
    omega) le_rfl

theorem time_keyGuard_tight (n : ℕ) (hn : n ≤ 2 ^ 103) :
    XProg.totalTimeT (keyGuardP Dc Bk rSmall n) 0 0 (n + 1) ≤ 2 ^ 385 := by
  have h := (bounds_keyGuardP_tight n).total (0 : Fin 105) 0 (n := n + 1) (by omega)
  have hl : leT n (2 ^ 104) ≤ 2 ^ 300 := by
    simp only [leT]
    have : n + 5 ≤ 2 ^ 104 := by omega
    calc (n + 5) * (2 * (2 ^ 104 + 2) + 3) + 1
        ≤ 2 ^ 104 * (2 * (2 ^ 104 + 2) + 3) + 1 := by gcongr
      _ ≤ 2 ^ 300 := by norm_num
  refine h.trans ?_
  have : (2 * 2 ^ 104 + 2) + (2 ^ 300 + (2 ^ 384 + 2 ^ 383 + 2 ^ 253)) + (2 * 2 ^ 123 + 2) ≤
      (2 : ℕ) ^ 385 := by
    norm_num
  refine le_trans ?_ this
  gcongr

end AdvancedEncryption.ExpLUT.Prog.KeyTight

namespace AdvancedEncryption.ExpLUT.Prog.KeyCore

/-- **The tight clock of the KeyGen machine.** -/
theorem time_keyMachine_tight : keyMachine.time ≤ 2 ^ 385 := by
  rw [keyMachine_eq, time_toMachineB_eq]
  exact KeyTight.time_keyGuard_tight _ keyInputBound_Dc

end AdvancedEncryption.ExpLUT.Prog.KeyCore
