import PE.Impl.RingBTVW.Prog.EncP
import SigabaNeo.Lib.Machines.Prog.FrameSize

/-!
# Clocks and description lengths of the compiled `Setup` and `Enc`

`setupMP`, `encMP` are `XProg.toMachineT` of the tape programs `setupP` (96 tapes, input on tape
`94`, output `91`) and `encP` (124 tapes, input `120`, output `122`), clocked for their fixed input
lengths `nInS`, `nInE`:

* `time_setupMP`, `time_encMP`: the clock is the loader (`2 n + 2`), the per-tape time bound
  `XProg.timeBoundT` of the program from the input bound, and the emitter (`2 ℓ + 2`, `ℓ` the
  per-tape length bound of the output tape);
* `descLen_setupMP`, `descLen_encMP`: the description length from the number of states
  `XProg.size` of the program (`+ 4` for the loader and the emitter), `96` resp. `124` tapes;
* `timeBound_encCoreP_le`: the core `encCoreP` of `Enc` (a `NoGrow` program) runs within
  `tbC · (L + 1) ^ tbD` steps from tapes of at most `L` bits (`Prog.timeBound_le`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem time_setupMP (X : ChiSampler c) :
    (setupMP hk c X).time =
      (2 * nInS + 2) + XProg.timeBoundT (setupP hk c X) (Prog.inputBound 94 nInS) +
        (2 * XProg.lenBoundT (setupP hk c X) (Prog.inputBound 94 nInS) 91 + 2) := rfl

theorem descLen_setupMP (X : ChiSampler c) :
    (setupMP hk c X).descLen =
      6 * ((setupP hk c X).size + 4) * 3 ^ 96 * 3 ^ 0 *
        Machine.entryBits 96 ((setupP hk c X).size + 4) 0 := by
  rw [Machine.descLen, setupMP, XProg.states_toMachineT, XProg.card_state]
  rfl

theorem time_encMP (X : ChiSampler c) :
    (encMP hk c X).time =
      (2 * nInE hk c + 2) + XProg.timeBoundT (encP hk c X) (Prog.inputBound 120 (nInE hk c)) +
        (2 * XProg.lenBoundT (encP hk c X) (Prog.inputBound 120 (nInE hk c)) 122 + 2) := rfl

theorem descLen_encMP (X : ChiSampler c) :
    (encMP hk c X).descLen =
      6 * ((encP hk c X).size + 4) * 3 ^ 124 * 3 ^ 0 *
        Machine.entryBits 124 ((encP hk c X).size + 4) 0 := by
  rw [Machine.descLen, encMP, XProg.states_toMachineT, XProg.card_state]
  rfl

/-- The core of `Enc` from tapes of at most `L` bits. -/
theorem timeBound_encCoreP_le (L : ℕ) :
    Prog.timeBound encCoreP L ≤ Prog.tbC encCoreP * (L + 1) ^ Prog.tbD encCoreP :=
  Prog.timeBound_le encCoreP noGrow_encCoreP L

end AdvancedEncryption.RingBTVW.Prog

namespace AdvancedEncryption.RingBTVW.Prog

/-- **The explicit χ sampler of `confP`**: the centered binomial sampler `chiP` (width 16). -/
def chiSamplerP : ChiSampler Params.confP where
  P := chiP
  law := law_chiP
  wf := wf_chiP
  pres6 := preserves6_chiP
  B := bChi
  atb := atbb_chiP

end AdvancedEncryption.RingBTVW.Prog
