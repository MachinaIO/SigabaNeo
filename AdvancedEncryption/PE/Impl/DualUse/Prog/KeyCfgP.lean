import PE.Impl.DualUse.Prog.KeyP
import PE.Impl.DualUse.Algo.KeyTry

/-!
# The key-try configuration of the concrete parameters

`cfP`: the coefficient width `Bp`, the `mBp` coins and the radius word `SpW` of `confP`, with its
validity (`cfP_valid`), from the explicit layout of the big box (`big_eqE`) and the binary
decomposition `decp = decG`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo AdvancedEncryption.DualUse.Algo
open AdvancedEncryption.DualUse.Params AdvancedEncryption.DualUse.Algo.Params

/-- The key-try configuration of `confP`. -/
noncomputable def cfP : KeyCfg := ⟨Bp, mBp, SpW⟩

theorem cfP_valid : cfP.Valid hkp confP where
  h0 := Nat.succ_pos _
  hK0 := by rw [Kp_def]; positivity
  hB := hBp
  hm := hmE
  hBig := big_eqE
  hsl := length_SpW
  hSmall := by show confP.Small = keyBall (2 ^ Kp) dp (TrapCol kp) Np (val SpW); rw [val_SpW]; rfl
  hdec := decp_eq

end AdvancedEncryption.DualUse.Prog
