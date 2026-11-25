import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMHandlerStash
import PE.Impl.ExpLUT.Prog.RedPubPDc
import PE.Impl.ExpLUT.Prog.RedChalLaw
open SigabaNeo.Tape.RingVM.Handler
/-!
# `mid` of the key component, phase M1 at `Dc`: the words of `mpk` and `ct`, with a stash

From the input `io2 (rawEnc σ) C []` of the key component, **`m1P`** computes

* `mpkW σ = mpkEnc (redView (rawF σ)).1` (`pubC`, in `ringIOS` with the stash `[], rawEnc σ, C`),
* `ctW σ = ctEnc (redView (rawF σ)).2` (`chalC` with `μ = false`, stash `mpkW, rawEnc σ, C`;
  `chalCT σ false = (redView …).2`, `chalCT_false`),

and leaves the **storage layout `m1Store`**: tape `243` = `ctW σ`, `244` = `mpkW σ`,
`245` = `rawEnc σ`, `246` = `C`, every other tape blank (**`law_m1P`**, **`wf_m1P`**).
The tapes `243 … 246` lie outside the MVM tapes `0 … 104` (`RedKeyM.rkE`) of the later phases.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyMid

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM Cslib
open SigabaNeo.Tape.RingVM.Handler
open scoped SigabaNeo.Tape.Prog

/-! ### The storage tapes -/

def tCt : Fin 247 := 243
def tMpk : Fin 247 := 244
def tSig : Fin 247 := 245
def tC : Fin 247 := 246

theorem tWd_sR1 : tWd sR1 = tMpk := rfl
theorem tWd_sR2 : tWd sR2 = tSig := rfl
theorem tWd_sR3 : tWd sR3 = tC := rfl

/-- The word of the public key. -/
noncomputable def mpkW (σ : RawSec Dc) : List Bool := (mpkEnc Dc).enc (redView Dc (rawF Dc σ)).1

/-- The word of the challenge ciphertext for `μ = 0`. -/
noncomputable def ctW (σ : RawSec Dc) : List Bool := (ctEnc Dc).enc (redView Dc (rawF Dc σ)).2

/-- **The storage after M1.** -/
noncomputable def m1Store (σ : RawSec Dc) (C : List Bool) : Store 247 :=
  Function.update (put3 tMpk tSig tC (fun _ => []) (mpkW σ) ((rawEnc Dc).enc σ) C) tCt (ctW σ)

theorem chalCT_false (σ : RawSec Dc) : chalCT Dc σ false = (redView Dc (rawF Dc σ)).2 := by
  simp [chalCT, shiftCT, msgR]

/-! ### The program -/

/-- Before the public key: stash `C` and the raw secret. -/
def m1InP : Tape.Prog 247 := Prog.cp tC 1 ⨾ Prog.clr 1 ⨾ Prog.cp tSig 0

/-- Between the two codes: `mpkW` to its tape, the challenger's inputs `rawEnc σ`, `[false]`. -/
def m1MidP : Tape.Prog 247 := Prog.cp tMpk 0 ⨾ Prog.cp 0 tSig ⨾ .prim (.cons 1 false)

/-- After the challenge: `ctW` to its tape. -/
def m1OutP : Tape.Prog 247 := Prog.cp tCt 0 ⨾ Prog.clr 0

/-- **Phase M1.** -/
noncomputable def m1P : XProg 247 :=
  .seq (.prog m1InP) <|
  .seq (ringIOS Dc.N Dc.K RedPubP.ra RedPubP.rb RedPubP.rOut RedPubP.r1 (RedPubP.tm Dc)
    (RedPubP.pubC Dc)) <|
  .seq (.prog m1MidP) <|
  .seq (ringIOS Dc.N Dc.K RedChal.ra RedChal.rb SigabaNeo.Tape.RingVM.Hash.xOut RedChal.r1 (RedChal.tm Dc)
    (RedChal.chalC Dc)) <|
  .prog m1OutP

theorem wf_m1P : m1P.WF :=
  ⟨⟨trivial, trivial, trivial⟩, wf_ringIOS _ _ _ _ _ _ _ _ (RedPubP.loopOkB_pubC Dc),
    ⟨trivial, trivial, trivial⟩, wf_ringIOS _ _ _ _ _ _ _ _ (RedChal.loopOkB_chalC Dc),
    ⟨trivial, trivial⟩⟩

theorem pub_uses1 : usesR sR1 (RedPubP.pubC Dc) = false := by decide
theorem pub_uses2 : usesR sR2 (RedPubP.pubC Dc) = false := by decide
theorem pub_uses3 : usesR sR3 (RedPubP.pubC Dc) = false := by decide
theorem chal_uses1 : usesR sR1 (RedChal.chalC Dc) = false := by decide
theorem chal_uses2 : usesR sR2 (RedChal.chalC Dc) = false := by decide
theorem chal_uses3 : usesR sR3 (RedChal.chalC Dc) = false := by decide

theorem run_m1InP (a C : List Bool) :
    m1InP.run (io2 (R := 245) a C []) = stash3 (io2 (R := 245) a [] []) [] a C := by
  simp only [m1InP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  funext t
  simp only [put3, Function.update_apply, io2]
  by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;> by_cases ha : t = tWd sR1 <;>
    by_cases hb : t = tWd sR2 <;> by_cases hc : t = tWd sR3 <;>
    simp_all [tC, tSig, tMpk, sR1, sR2, sR3, tWd] <;> omega

theorem run_m1MidP (m a C : List Bool) :
    m1MidP.run (stash3 (io2 (R := 245) m [] []) [] a C) =
      stash3 (io2 (R := 245) a [false] []) m a C := by
  simp only [m1MidP, Prog.run_seq, Prog.run_copy, Prog.run_prim, Prim.apply]
  funext t
  simp only [put3, Function.update_apply, io2]
  by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;> by_cases ha : t = tWd sR1 <;>
    by_cases hb : t = tWd sR2 <;> by_cases hc : t = tWd sR3 <;>
    simp_all [tC, tSig, tMpk, sR1, sR2, sR3, tWd] <;> omega

theorem run_m1OutP (c m a C : List Bool) :
    m1OutP.run (stash3 (io2 (R := 245) c [] []) m a C) =
      Function.update (put3 tMpk tSig tC (fun _ => []) m a C) tCt c := by
  simp only [m1OutP, Prog.run_seq, Prog.run_copy, Prog.run_clear]
  funext t
  simp only [put3, Function.update_apply, io2]
  by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;> by_cases ha : t = tWd sR1 <;>
    by_cases hb : t = tWd sR2 <;> by_cases hc : t = tWd sR3 <;> by_cases hd : t = tCt <;>
    simp_all [tC, tSig, tMpk, tCt, sR1, sR2, sR3, tWd] <;> omega

/-- **The law of phase M1.** -/
theorem law_m1P (σ : RawSec Dc) (C : List Bool) :
    m1P.law (io2 (R := 245) ((rawEnc Dc).enc σ) C []) = PMF.pure (m1Store σ C) := by
  obtain ⟨hN, hW, hb32⟩ := RedPubP.hyps_Dc
  obtain ⟨hb1, hb32', hN'⟩ := RedChal.Dc_hyps
  rw [m1P, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_m1InP,
    PMF.pure_bind, XProg.law_seq,
    law_ringIOS Dc.N_pos Dc.K_pos (by decide) _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) _ _ pub_uses1 pub_uses2 pub_uses3, PMF.pure_bind]
  have hp := RedPubP.exec_pubC hN hW hb32 σ
  rw [RedPubP.w0P] at hp
  rw [hp, XProg.law_seq, XProg.law_prog, Prog.law_eq_run_of_coinFree _ (by rfl), run_m1MidP,
    PMF.pure_bind, XProg.law_seq,
    law_ringIOS Dc.N_pos Dc.K_pos (by decide) _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) _ _ chal_uses1 chal_uses2 chal_uses3, PMF.pure_bind]
  have hc := RedChal.exec_chalC hb1 hb32' hN' σ false
  rw [show SigabaNeo.Tape.RingVM.Handler.initW1 RedChal.ra RedChal.rb RedChal.r1 (RedChal.tm Dc) ((rawEnc Dc).enc σ)
    [false] = RedChal.w0 σ false from rfl, hc, chalCT_false, XProg.law_prog,
    Prog.law_eq_run_of_coinFree _ (by rfl), run_m1OutP]
  rfl

end AdvancedEncryption.ExpLUT.Prog.RedKeyMid
