import PE.Impl.DualUse.AHConcrete
import PE.Impl.DualUse.Prog.WfB2Inst

/-!
# Attribute hiding of the concrete scheme from Ring-LWE alone

`AHConcrete` proves attribute hiding at `confP` given a `W_f` block `wfB` with its law
(`WfSpec`) and its cost (`WfCost wfB Wg T`, `T ≤ 2370`, `384 ≤ Wg ≤ 2^200`). Here the block is
the block-structured `wfB2 hkp confP 512` (`Prog/WfB2*.lean`), and `wfB2_confP` discharges both:
its law at `W = 512`, at most `2^25 ≤ 2^200` states, and on the input `wfIn (2^240)
(frontL confP.L 512)` at most `2^556` steps with every tape at most `2^250` bits
(`wfCost_wfB2`, `T = 556`).

* `attributeHiding_conf_rlwe`: from `HardAt (params3 …) kb` and `HardAt (params5 …) kb`,
  `2645 ≤ kb`;
* `attributeHiding_conf_registry'`: from the registry's assumption `RingLWE.decision.Holds` only;
* `attributeHiding_implP_registry'`: the same for the compiled implementation `implP`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params

/-- **The cost of the block-structured `W_f` block at `confP`**: at most `2^556` steps, every
tape at most `2^250` bits, at most `2^25` states (`wfB2_confP`). -/
theorem wfCost_wfB2 : WfCost (wfB2 hkp confP WB2.Wc) WB2.Wc 556 := by
  obtain ⟨-, hs, ht⟩ := WB2.wfB2_confP
  obtain ⟨h1, h2⟩ := ht (2 ^ 240) (frontL confP.L WB2.Wc) le_rfl
    (by rw [confP_L]; exact WB2.frontL_le)
  exact ⟨h1, h2, hs.trans (by norm_num)⟩

theorem wfSpec_wfB2_confP : WfSpec hkp confP (wfB2 hkp confP WB2.Wc) WB2.Wc :=
  WB2.wfB2_confP.1

theorem Wc_ge : 384 ≤ WB2.Wc := by simp only [WB2.Wc]; norm_num
theorem Wc_le : WB2.Wc ≤ 2 ^ 200 := by simp only [WB2.Wc]; norm_num

variable {ms : Machines hkp confP}

/-- **Attribute hiding of the concrete scheme** at `confP`, for every choice of the machines,
from the hardness of decision Ring-LWE at the parameters of hybrids 3 and 5 with `kb ≥ 2645`
bits: `attributeHiding_conf` with the `W_f` block `wfB2 hkp confP 512`. -/
theorem attributeHiding_conf_rlwe (kb : ℕ) (hkb : 2645 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding PUniv params (impl hkp confP ms) :=
  attributeHiding_conf wfSpec_wfB2_confP wfCost_wfB2 (by norm_num) Wc_ge Wc_le kb hkb hard3 hard5

/-- **Attribute hiding of the concrete scheme from the registry's decision Ring-LWE alone**:
the only hypothesis is the assumption `RingLWE.decision.Holds`. -/
theorem attributeHiding_conf_registry' (hR : RingLWE.decision.Holds) :
    AttributeHiding PUniv params (impl hkp confP ms) :=
  attributeHiding_conf_registry hR wfSpec_wfB2_confP wfCost_wfB2 (by norm_num) Wc_ge Wc_le

/-- **Attribute hiding of the compiled implementation** `implP` at `confP` from the registry's
decision Ring-LWE, with the `W_f` block `wfB2 hkp confP 512` in the reductions. -/
theorem attributeHiding_implP_registry' (hR : RingLWE.decision.Holds) (X : ChiSampler confP)
    {bfX cfX : XProg 256} {W W' : ℕ} (hbf : BfSpec hkp confP bfX W) (hcfX : CfSpec hkp confP cfX W')
    (hK2 : 2 ≤ Kp) :
    AttributeHiding PUniv params (implP hkp confP X hbf hcfX cfP cfP_valid hK2) :=
  attributeHiding_implP_registry hR X hbf hcfX hK2 wfSpec_wfB2_confP wfCost_wfB2 (by norm_num)
    Wc_ge Wc_le

end AdvancedEncryption.DualUse
