import PE.Impl.ExpLUT.Prog.AuthWCost
import PE.Impl.RingBTVW.Prog.AuthBPX
import PE.Impl.ExpLUT.AH.Games

/-!
# The authorization component of the reduction (package G2)

`authWX hR : XProg (R + 2)` (any `R ≥ 14`): the authorization program for ExpLUT's predicate
words (`AuthW.authW8`) followed by `RingBTVW.Prog.authFix` (the work tapes cleared, the output bit
rewritten), lifted to the handlers' width:

* **`law_authWX`**: from the predicate word `C` and the attribute bits `encAttribute w8 x`, the bit
  `authW impl C x` (the flag of the experiment), for every implementation whose `Eval` is
  `evalMachineX` (`authorized_iff`);
* `time_authWX`: at most `2^109` steps for queries of at most `2^49` bits and at most `128`
  attribute bits; `len_authWX`: one output bit; `size_authWX`: at most `2^18` states.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.PE
open AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.RingBTVW.Prog (authFix coinFree_authFix wf_authFix run_authFix ioS_inA
  lenBoundT_authFix time_authFix liftP law_liftP_pure wf_liftP timeBoundT_liftP lenBoundT_liftP_le)
open AdvancedEncryption.RingBTVW.BpComp (inA outA inBA)
open AdvancedEncryption.ExpLUT.AuthW

/-- The authorization program with its output normalized. -/
def authWN : SigabaNeo.Tape.Prog 16 := .seq authW8 authFix

/-- **The authorization component** at the width `R + 2`. -/
def authWX {R : ℕ} (hR : 14 ≤ R) : XProg (R + 2) := liftP hR (SigabaNeo.Tape.Prog.toX authWN)

theorem coinFree_authWN : authWN.CoinFree := by
  have h1 : authW8.coinFreeB = true := good_authW8.1
  have h2 : authFix.coinFreeB = true := coinFree_authFix
  show (SigabaNeo.Tape.Prog.seq authW8 authFix).coinFreeB = true
  simp [SigabaNeo.Tape.Prog.coinFreeB, h1, h2]

open Classical in
theorem authW_eq {impl : Impl sig} (hEval : impl.machine .eval = evalMachineX) (C : List Bool)
    (x : Attribute w8) : authW impl C x = authAW C (encAttribute w8 x) := by
  rw [authAW_encAttr, authW]
  by_cases h : Authorized (U := univ w8) params impl C x
  · simp only [decide_eq_true h]
    rw [authorized_iff impl hEval] at h
    simp [h.1, h.2]
  · simp only [decide_eq_false h]
    rw [authorized_iff impl hEval] at h
    by_cases hl : C.length = predLen
    · have : (progOf C).output x = true := by
        cases ho : (progOf C).output x
        · exact absurd ⟨hl, ho⟩ h
        · rfl
      simp [hl, this]
    · simp [hl]

/-- **The law of the authorization component.** -/
theorem law_authWX {R : ℕ} (hR : 14 ≤ R) {impl : Impl sig}
    (hEval : impl.machine .eval = evalMachineX) (C : List Bool) (x : Attribute w8) :
    (authWX hR).law (io2 (R := R) C (encAttribute w8 x) []) =
      PMF.pure (io2 (R := R) [authW impl C x] [] []) := by
  have hrun : SigabaNeo.Tape.Prog.run authW8 (inA C (encAttribute w8 x)) =
      outA (authAW C (encAttribute w8 x)) := run_authW8 _ _
  have hp : (SigabaNeo.Tape.Prog.toX authWN).law (ioS (R := 14) C (encAttribute w8 x) []) =
      PMF.pure (ioS (R := 14) [authW impl C x] [] []) := by
    rw [SigabaNeo.Tape.Prog.law_toX, SigabaNeo.Tape.Prog.law_eq_run_of_coinFree _ coinFree_authWN,
      ioS_inA, authWN, SigabaNeo.Tape.Prog.run_seq, hrun, run_authFix, authW_eq hEval]
  exact law_liftP_pure hR hp

theorem wf_authWX {R : ℕ} (hR : 14 ≤ R) : (authWX hR).WF :=
  SigabaNeo.Tape.Prog.wf_toX _ ⟨good_authW8.2, wf_authFix⟩

theorem io2_le_inBA' {a b : ℕ} (ha : a ≤ 2 ^ 49) (hb : b ≤ 128) :
    (io2 (R := 14) a b 0 : Fin 16 → ℕ) ≤ inBA (2 ^ 49) := fun t => by
  simp only [io2, inBA, Function.update_apply]
  fin_cases t <;> simp <;> omega

/-- **The time of the authorization component**: at most `2^109` steps. -/
theorem time_authWX {R : ℕ} (hR : 14 ≤ R) {a b : ℕ} (ha : a ≤ 2 ^ 49) (hb : b ≤ 128) :
    XProg.timeBoundT (authWX hR) (io2 (R := R) a b 0) ≤ 2 ^ 109 := by
  rw [authWX, timeBoundT_liftP, SigabaNeo.Tape.Prog.timeBoundT_toX, authWN]
  obtain ⟨t1, l1⟩ := bounds_authW8_49 (L := 2 ^ 49) le_rfl
  have m1 := SigabaNeo.Tape.Prog.timeBoundT_mono authW8 (io2_le_inBA' ha hb)
  have m2 : ∀ t, SigabaNeo.Tape.Prog.lenBoundT authW8 (io2 (R := 14) a b 0) t ≤ 2 ^ 49 := fun t =>
    (SigabaNeo.Tape.Prog.lenBoundT_mono authW8 (io2_le_inBA' ha hb) t).trans (l1 t)
  show SigabaNeo.Tape.Prog.timeBoundT authW8 _ + SigabaNeo.Tape.Prog.timeBoundT authFix _ ≤ _
  have := time_authFix m2
  have : (2 : ℕ) ^ 108 + 2 ^ 60 ≤ 2 ^ 109 := by norm_num
  omega

/-- **The output of the authorization component**: one bit. -/
theorem len_authWX {R : ℕ} (hR : 14 ≤ R) (a b : ℕ) :
    XProg.lenBoundT (authWX hR) (io2 (R := R) a b 0) ≤ io2 1 0 0 := by
  refine lenBoundT_liftP_le hR _ ?_
  rw [SigabaNeo.Tape.Prog.lenBoundT_toX, authWN]
  exact lenBoundT_authFix _

/-- **The size of the authorization component**: at most `2^18` states. -/
theorem size_authWX {R : ℕ} (hR : 14 ≤ R) : (authWX hR).size ≤ 2 ^ 18 := by
  rw [authWX, liftP, XProg.size_frame, SigabaNeo.Tape.Prog.size_toX, authWN]
  have h1 := size_authW8
  have h2 : SigabaNeo.Tape.Prog.size authFix ≤ 2 ^ 12 := by decide +kernel
  have e : SigabaNeo.Tape.Prog.size (SigabaNeo.Tape.Prog.seq authW8 authFix) =
      SigabaNeo.Tape.Prog.size authW8 + SigabaNeo.Tape.Prog.size authFix :=
    SigabaNeo.Tape.Prog.size.eq_3 _ _
  rw [e]
  have : (2 : ℕ) ^ 17 + 2 ^ 12 ≤ 2 ^ 18 := by norm_num
  omega

end AdvancedEncryption.ExpLUT.Prog
