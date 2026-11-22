import PE.Impl.DualUse.Impl
import PE.Impl.DualUse.ImplCorrect
import PE.Impl.DualUse.Prog.KeyGenP
import PE.Impl.DualUse.Prog.DecGenP
import SigabaNeo.Lib.Machines.Prog.FrameSize

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

/-- **The compiled machines of `KeyGen` and `Dec`.** -/
noncomputable def machinesP {bfX cfX : XProg 256} {W W' : ℕ} (hbf : BfSpec hk c bfX W)
    (hcfX : CfSpec hk c cfX W') (cf : KeyCfg) (hcf : cf.Valid hk c) (hK2 : 2 ≤ K) : Machines hk c where
  key := keyMachineP hk c bfX W cf
  key_short msk C hC := keyMachineP_short hbf cf hcf msk C hC
  key_long msk C hC := keyMachineP_long hbf cf hcf msk C hC
  dec := decMachineP hk c cfX W'
  dec_det := deterministic_decMachineP hcfX
  dec_law sk C ct hC := decMachineP_law hcfX hK2 sk C ct hC

/-- **The implementation with the compiled machines.** -/
noncomputable def implP {bfX cfX : XProg 256} {W W' : ℕ} (hbf : BfSpec hk c bfX W)
    (hcfX : CfSpec hk c cfX W') (cf : KeyCfg) (hcf : cf.Valid hk c) (hK2 : 2 ≤ K) :
    Impl PE.sig :=
  impl hk c (machinesP hk c hbf hcfX cf hcf hK2)

/-! ### Explicit clocks and description lengths -/

theorem time_keyMachineP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) :
    (keyMachineP hk c bfX W cf).time =
      (2 * (nKG hk c + 1) + 2) +
        XProg.timeBoundT (keyGenP hk c bfX W cf) (Prog.inputBound 255 (nKG hk c + 1)) +
        (2 * XProg.lenBoundT (keyGenP hk c bfX W cf) (Prog.inputBound 255 (nKG hk c + 1)) 0 + 2) :=
  rfl

theorem descLen_keyMachineP (bfX : XProg 256) (W : ℕ) (cf : KeyCfg) :
    (keyMachineP hk c bfX W cf).descLen =
      6 * ((keyGenP hk c bfX W cf).size + (nKG hk c + 3) + 2) * 3 ^ 256 * 3 ^ 0 *
        Machine.entryBits 256 ((keyGenP hk c bfX W cf).size + (nKG hk c + 3) + 2) 0 := by
  rw [keyMachineP, XProg.descLen_toMachineB, XProg.card_state]

theorem time_decMachineP (cfX : XProg 256) (W : ℕ) :
    (decMachineP hk c cfX W).time =
      (2 * (nDec hk c + 1) + 2) +
        XProg.timeBoundT (decGenP hk c cfX W) (Prog.inputBound 255 (nDec hk c + 1)) +
        (2 * XProg.lenBoundT (decGenP hk c cfX W) (Prog.inputBound 255 (nDec hk c + 1)) 0 + 2) :=
  rfl

theorem descLen_decMachineP (cfX : XProg 256) (W : ℕ) :
    (decMachineP hk c cfX W).descLen =
      6 * ((decGenP hk c cfX W).size + (nDec hk c + 3) + 2) * 3 ^ 256 * 3 ^ 0 *
        Machine.entryBits 256 ((decGenP hk c cfX W).size + (nDec hk c + 3) + 2) 0 := by
  rw [decMachineP, XProg.descLen_toMachineB, XProg.card_state]

end AdvancedEncryption.DualUse
