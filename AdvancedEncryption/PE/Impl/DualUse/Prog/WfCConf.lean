import PE.Impl.DualUse.ImplBP
import PE.Impl.DualUse.Prog.WfB2SConf
import PE.Impl.DualUse.Prog.WfB2SSize
import PE.Impl.DualUse.Prog.KeyCostConf

/-!
# The stream block of `implC` at `confA`

`wfC = wfB2S hkp confP Icn Wn` (`ImplBP`) with the hypotheses of `time_wfB2S_conf`,
`size_wfB2S_conf` discharged at `confP`:

* `offs_conf`: the offsets of the simulation data are below `Lbn = 2^260`;
* **`time_wfC`**: from simulation data of at most `2^260` bits and a stream of at most `2^64` bits,
  at most `2^628` steps, every tape at most `2^262` bits afterwards;
* **`size_wfC`**: at most `2^25` states.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.DualUse.Algo AdvancedEncryption.DualUse.Algo.Params
open AdvancedEncryption.DualUse.Sub
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

set_option maxRecDepth 100000
set_option exponentiation.threshold 3000

theorem offB_conf : offB confP ≤ 2 ^ 260 := by
  simp only [offB, fixLen]; comp_unfold; norm_num

theorem offW_conf : offW hkp confP ≤ 2 ^ 260 := by
  simp only [offW, fixLen]; comp_unfold; norm_num

theorem offR_conf : offR hkp confP ≤ 2 ^ 260 := by
  simp only [offR, fixLen]; comp_unfold; norm_num

theorem offPsi_conf : offPsi hkp confP ≤ 2 ^ 259 := by
  simp only [offPsi, fixLen]; comp_unfold; norm_num

theorem lenPsi_conf : lenPsi Np Kp kp ≤ 2 ^ 130 := by
  simp only [lenPsi, fixLen]; comp_unfold; norm_num

theorem offX_conf : offPsi hkp confP + nA * lenPsi Np Kp kp ≤ 2 ^ 260 := by
  have h1 := offPsi_conf
  have h2 := lenPsi_conf
  have hn : nA = 128 := rfl
  rw [hn]
  generalize offPsi hkp confP = a at *
  generalize lenPsi Np Kp kp = b at *
  omega

/-- **The stream block at `confA`.** -/
theorem time_wfC {Lsd Lg : ℕ} (hLsd : Lsd ≤ 2 ^ 260) (hLg : Lg ≤ 2 ^ 64) :
    XProg.timeBoundT wfC (io2 (R := 254) Lsd Lg 0) ≤ 2 ^ 628 ∧
      ∀ t, XProg.lenBoundT wfC (io2 (R := 254) Lsd Lg 0) t ≤ 2 ^ 262 :=
  WB2.time_wfB2S_conf hkp confP Np_def Kp_def confP_d rfl (treeHeight_le.trans (by norm_num [eTree])) offB_conf offW_conf
    (offPsi_conf.trans (by unfold WB2.Lbn; norm_num)) offR_conf offX_conf Lsd Lg hLsd hLg

/-- **The states of the stream block at `confA`.** -/
theorem size_wfC : wfC.size ≤ 2 ^ 25 :=
  WB2.size_wfB2S_conf hkp confP Np_def Kp_def confP_d rfl (treeHeight_le.trans (by norm_num [eTree])) offB_conf offW_conf
    (offPsi_conf.trans (by unfold WB2.Lbn; norm_num)) offR_conf offX_conf

end AdvancedEncryption.DualUse.Prog
