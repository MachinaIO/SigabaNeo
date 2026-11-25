import PE.Impl.ExpLUT.Prog.DecMachineProg
import PE.Impl.ExpLUT.AH.Conf
/-!
# The concrete `Dec` machine (package F4)

`decMachine = decMP Dc predLen`: the `Dec` machine at the concrete dimensions `Dc` (package P),
for predicate words of at most `predLen` bits; **`decSpec_decMachine : DecSpec Dc predLen
decMachine`**.
-/

namespace AdvancedEncryption.ExpLUT.Prog.DecConf

open SigabaNeo

/-- **The concrete `Dec` machine.** -/
noncomputable def decMachine : Machine := DecM.decMP Dc predLen

/-- **The concrete `Dec` machine meets `DecSpec`.** -/
theorem decSpec_decMachine : DecSpec Dc predLen decMachine :=
  DecM.decSpec_decMP Dc Dc_b predLen

end AdvancedEncryption.ExpLUT.Prog.DecConf
