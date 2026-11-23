import PE.Impl.DualUse.Impl
import PE.Impl.DualUse.ImplCorrect
import PE.Impl.DualUse.Prog.ShellsBP
import SigabaNeo.Lib.Machines.Prog.FrameSize
import PE.Impl.DualUse.Prog.EncP

/-!
# The implementation with the compiled `KeyGen` and `Dec`

`machinesP`: the machines of `KeyGen` (`Prog.keyMachineP`) and `Dec` (`Prog.decMachineP`) compiled
from tape programs, with the key-row block `bfX` (`BfSpec`) and the `c_f̂` block `cfX` (`CfSpec`)
as parameters, for a configuration whose boxes and decomposition are the explicit ones
(`KeyCfg.Valid`) and `K ≥ 2`. `implP = impl hk c machinesP`: every theorem stated for
`impl hk c ms` (correctness `correct`, attribute hiding, `impl_keyGen`, …) applies to it.

The machines' clocks and description lengths are explicit (`time_keyMachineP`,
`descLen_keyMachineP`, `time_decMachineP`, `descLen_decMachineP`): the clock of the bounded loader,
the per-tape time bound `timeBoundT` of the program from the input bound, and the emitter; the
description length from the number of states `XProg.size` of the program.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Tape AdvancedEncryption.DualUse.Prog AdvancedEncryption.PE

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- **The compiled machines of `Setup`, `Enc`, `KeyGen` and `Dec`** (`X`: an explicit χ sampler,
`Prog.setupMP`, `Prog.encMP`). -/
noncomputable def machinesP [NeZero c.d] (X : ChiSampler c) {bfX cfX : XProg 256}
    (hbf : BfSpec hk c bfX 512) (hcfX : CfSpec hk c cfX 512) (cf : KeyCfg) (hcf : cf.Valid hk c)
    (hK2 : 2 ≤ K) : Machines hk c where
  setup := setupMP hk c X
  setup_law := run_setupMP hk c c.hN (by omega) X
  enc := encMP hk c X
  enc_law mpk x b := run_encMP hk c c.hN (by omega) X mpk x b
  key := keyMachineP hk c bfX cf
  key_short msk C hC := keyMachineP_short hbf cf hcf msk C hC
  key_long msk C hC := keyMachineP_long hbf cf hcf msk C hC
  dec := decMachineP hk c cfX
  dec_det := deterministic_decMachineP hcfX
  dec_law sk C ct hC := decMachineP_law hcfX hK2 sk C ct hC

/-- **The implementation with the compiled machines.** -/
noncomputable def implP [NeZero c.d] (X : ChiSampler c) {bfX cfX : XProg 256}
    (hbf : BfSpec hk c bfX 512) (hcfX : CfSpec hk c cfX 512) (cf : KeyCfg) (hcf : cf.Valid hk c)
    (hK2 : 2 ≤ K) : Impl PE.sig :=
  impl hk c (machinesP hk c X hbf hcfX cf hcf hK2)

/-! ### Explicit clocks and description lengths -/

theorem time_keyMachineP (bfX : XProg 256) (cf : KeyCfg) :
    (keyMachineP hk c bfX cf).time =
      (2 * (nKG hk c + 1) + 2) +
        XProg.timeBoundT (keyGenP hk c bfX cf) (Prog.inputBound 255 (nKG hk c + 1)) +
        (2 * XProg.lenBoundT (keyGenP hk c bfX cf) (Prog.inputBound 255 (nKG hk c + 1)) 0 + 2) :=
  rfl

theorem descLen_keyMachineP (bfX : XProg 256) (cf : KeyCfg) :
    (keyMachineP hk c bfX cf).descLen =
      6 * ((keyGenP hk c bfX cf).size + (nKG hk c + 3) + 2) * 3 ^ 256 * 3 ^ 0 *
        Machine.entryBits 256 ((keyGenP hk c bfX cf).size + (nKG hk c + 3) + 2) 0 := by
  rw [keyMachineP, keyMachineF, XProg.descLen_toMachineB, XProg.card_state]; rfl

theorem time_decMachineP (cfX : XProg 256) :
    (decMachineP hk c cfX).time =
      (2 * (nDec hk c + 1) + 2) +
        XProg.timeBoundT (decGenP hk c cfX) (Prog.inputBound 255 (nDec hk c + 1)) +
        (2 * XProg.lenBoundT (decGenP hk c cfX) (Prog.inputBound 255 (nDec hk c + 1)) 0 + 2) :=
  rfl

theorem descLen_decMachineP (cfX : XProg 256) :
    (decMachineP hk c cfX).descLen =
      6 * ((decGenP hk c cfX).size + (nDec hk c + 3) + 2) * 3 ^ 256 * 3 ^ 0 *
        Machine.entryBits 256 ((decGenP hk c cfX).size + (nDec hk c + 3) + 2) 0 := by
  rw [decMachineP, decMachineF, XProg.descLen_toMachineB, XProg.card_state]; rfl

end AdvancedEncryption.DualUse
