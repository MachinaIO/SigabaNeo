import PE.Impl.DualUse.AHFinal
import PE.Impl.DualUse.ReductionCompsBoundV
import PE.Impl.DualUse.Prog.KeyCostV

/-!
# Attribute hiding at `confP` from `952`-bit Ring-LWE

`AHConcrete` bounds the constant of each reduction by `2^2383`, hence asks `kb ≥ 2645` bits of
Ring-LWE: its envelope (`t = 2376`) is carried by the uniform bound `20000 (2M + 1)^8 ≈ 2^2045` of
the simulated key try in the reductions' key component. Here every piece is bounded per tape:

* **the key component** (`time_keyP_confV`): the `W_f` block (`2^T`, `T = 556` for `wfB2`), the
  simulated key try (`(2 · 2^251 + 3) · wKS`, `wKS ≤ 2^240` by evaluation) and the rest: at most
  `2^T + 2^520` steps; at most `264 · lenPK + 2^140 ≈ 2^182.4` states (`size_keyP_confV`);
* the other components keep their bounds (setup `2^403`, public key `2^425`, authorization
  `2^275`, challenge `2^440`, SimData `2^500`; states `≤ 2^25`);
* **the constant** (`compConst_le_explicit`, `compBound_conf`): with the sum of the components'
  states `Sz = 264 · lenPK + 2^142`, the decoder (`2^16` states, `2^350` steps, `14` tapes), the
  components' time `≤ 2^651` and the lengths `≤ 2^252`, every reduction's constant is at most
  **`2^690`**. It is dominated by the states and tapes of the chain:
  `60 · S · 3^298 · (5 + 4 · 298 + size S)` with `S ≈ 2^200.7` (the handlers' states, `≈ 335664 Sz`;
  the prefixes of the public key in the key component, `264 · lenPK ≈ 2^182.4`, dominate `Sz`) and
  `3^298 ≈ 2^472.3` (`298 = 14 + 254 + 30` tapes: decoder, components, chain); the time term
  (`11 · 11 · 2^651 ≈ 2^658`) is far below.
* `64 · 2^256 · 2^690 = 2^952`: **attribute hiding from `kb ≥ 952` bits**
  (`attributeHiding_conf'`), for any `W_f` block meeting its law and `WfCostV` with `T ≤ 650`
  (`wfB2`: `T = 556`); the registry's strength `2650 ≥ 952` covers it
  (`attributeHiding_conf_registry''`).

**The formula for `kb`** (any universe, any parameters): `kb ≥ 6 + 2 · secBits + log₂ C` with
`C = compBound sP tP p R Sz Lc Tc X t` (`ReductionCompsBoundV`):
`log₂ C ≈ log₂ (60 · S · 3^(p + R + 30) · (5 + 4 (p + R + 30) + log₂ S))` as long as the time
term `11 tP + 121 Tc + 11 · 898942 X²` stays below it, where
`S ≈ 55944 · 3 · (glue + 2 Sz)` (`glue = 10638 + 264 Lc` for the date-window codes).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.DualUse.Params
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 3000

/-! ### The cost of the `W_f` block, per tape -/

/-- **The cost of the `W_f` block, per tape**: as `WfCost`, and after the block only tapes `0`
and `2` are nonblank (at most `2^250` bits); at most `2^30` states. -/
structure WfCostV (wfB : XProg 256) (Wg T : ℕ) : Prop where
  time : timeBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ 2 ^ T
  len : lenBoundT wfB (wfIn (2 ^ 240) (frontL confP.L Wg)) ≤ v02 (2 ^ 250)
  size : wfB.size ≤ 2 ^ 30

theorem WfCostV.toWfCost {wfB : XProg 256} {Wg T : ℕ} (h : WfCostV wfB Wg T) : WfCost wfB Wg T :=
  ⟨h.time, fun i => (h.len i).trans (by simp only [v02]; split_ifs <;> simp),
    h.size.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))⟩

/-- **The block-structured `W_f` block at `confP`**: at most `2^556` steps, only tapes `0`, `2`
nonblank afterwards (`wfB2_clear`), at most `2^25` states. -/
theorem wfCostV_wfB2 : WfCostV (wfB2 hkp confP WB2.Wc) WB2.Wc 556 := by
  obtain ⟨-, hs, -⟩ := WB2.wfB2_confP
  refine ⟨wfCost_wfB2.time, fun t => ?_, hs.trans (by norm_num)⟩
  by_cases h : t.val = 0 ∨ t.val = 2
  · simp only [v02, h, ↓reduceIte]; exact wfCost_wfB2.len t
  · simp only [v02, h, ↓reduceIte]
    rw [wfB2_clear hkp confP WB2.Wc _ t (fun e => h (Or.inl e)) (fun e => h (Or.inr e))]

theorem Wc_le' : WB2.Wc ≤ 2 ^ 20 := by simp only [WB2.Wc]; norm_num

/-! ### The constant -/

/-- The sum of the components' states at `confP`. -/
abbrev SzP : ℕ := 264 * 29931556208626396671394777597180314650064272740057088 + 2 ^ 142

/-- **The explicit bound at `confP`** (decoder `2^16` states, `2^350` steps, `14` tapes; components
`R = 254` tapes, `SzP` states, `2^651` steps; lengths `2^252`; cut `2^20`): at most `2^690`. -/
theorem compBound_conf :
    compBound (2 ^ 16) (2 ^ 350) 14 254 SzP (2 ^ 20) (2 ^ 651) (2 ^ 252) 655 ≤ 2 ^ 690 := by
  have hz : Nat.size (compStatesB (2 ^ 16) SzP (2 ^ 20) 655) ≤ 201 :=
    Nat.size_le.mpr (by unfold compStatesB; norm_num)
  calc compBound (2 ^ 16) (2 ^ 350) 14 254 SzP (2 ^ 20) (2 ^ 651) (2 ^ 252) 655 ≤
        60 * compStatesB (2 ^ 16) SzP (2 ^ 20) 655 * 3 ^ (14 + 254 + 30) * (5 + 4 * (14 + 254 + 30) + 201) +
          11 * 2 ^ 350 + 11 * (11 * 2 ^ 651 + 898942 * (2 ^ 252 * 2 ^ 252)) + 24 := by
        unfold compBound; gcongr
    _ ≤ 2 ^ 690 := by unfold compStatesB; norm_num

/-! ### A step -/

section Step

variable {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} {ienc : FixedEnc Inst nI}
  {senc : FixedEnc Sec nσ} {setupI : Date → PMF Sec}
  {viewI : Inst → Sec → PK hkp confP × CT hkp confP} {sdI : Inst → Sec → SimData hkp confP}
variable (S : StepComps ienc senc setupI viewI sdI) {wfB : XProg 256} {Wg : ℕ}
  (hwf : WfSpec hkp confP wfB Wg)
variable {T : ℕ} (hcost : WfCostV wfB Wg T) (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 20)
include hcost hW1 hW2

theorem hW2' : Wg ≤ 2 ^ 200 := hW2.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- **The key component of a step, per tape**: at most `2^T + 2^520` steps. -/
theorem key_timeV :
    timeBoundT (keyP hkp confP S.sdP wfB Wg cfP)
        (io2 (R := 254) (sigBound (dateCodes (ienc.prod senc)) (2 ^ 180)) confP.L 0) ≤
      2 ^ T + 2 ^ 520 :=
  (time_keyP_confV (S.time_sd (sigBound_le S) (by positivity))
    (S.len_sd (sigBound_le S) (by positivity)) hW1 (hW2' hcost hW1 hW2) hcost.time hcost.len).1

/-- **The time of the components of a step**: at most `2^651` for `T ≤ 650`. -/
theorem compTime_leV (hT : T ≤ 650) :
    compTimeP (S.bounds hwf hcost.toWfCost hW1 (hW2' hcost hW1 hW2)) ≤ 2 ^ 651 := by
  have h1 := S.time_setup (stateBound_le S) le_rfl
  have h2 := S.time_pub (a := 2 ^ 182) (b := 0) le_rfl (by positivity)
  have h3 := key_timeV S hcost hW1 hW2
  have h4 := time_authL (a := confP.L) (b := 10) (confP_L_le.trans (by norm_num)) le_rfl
  have h5 := S.time_chal (a := sigBound (dateCodes (ienc.prod senc)) (2 ^ 180)) (b := 1)
    (sigBound_le S) (by show (1 : ℕ) ≤ 2 ^ 180; norm_num)
  have hT' : (2 : ℕ) ^ T ≤ 2 ^ 650 := Nat.pow_le_pow_right (by norm_num) hT
  have hk' := h3.trans (Nat.add_le_add_right hT' (2 ^ 520))
  exact le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) hk') h4) h5)
    (by norm_num)

/-- **The sum of the states of the components of a step.** -/
theorem sizes_leV :
    (S.comps wfB Wg hwf).setupP.size + (S.comps wfB Wg hwf).pubP.size +
      (S.comps wfB Wg hwf).keyP.size + (S.comps wfB Wg hwf).authP.size +
      (S.comps wfB Wg hwf).chalP.size ≤ SzP := by
  have hk := size_keyP_confV S.sdP S.size_sd wfB hcost.size hW1 hW2
  rw [lenPK_eq] at hk
  have h1 := S.size_setup
  have h2 := S.size_pub
  have h4 := size_authL
  have h5 := S.size_chal
  show S.setupP.size + S.pubP.size + (keyP hkp confP S.sdP wfB Wg cfP).size + authL.size +
    S.chalP.size ≤ SzP
  generalize S.setupP.size = a at *
  generalize S.pubP.size = b at *
  generalize (keyP hkp confP S.sdP wfB Wg cfP).size = d at *
  generalize authL.size = e at *
  generalize S.chalP.size = f at *
  have : (2 : ℕ) ^ 25 + 2 ^ 25 + 2 ^ 140 + 2 ^ 19 + 2 ^ 25 ≤ 2 ^ 142 := by norm_num
  unfold SzP
  omega

/-- **The constant of the reduction of a step**, for a decoder with at most `2^16` states,
`2^350` steps and `14` tapes: at most `2^690` when `T ≤ 650`. -/
theorem const_leV (hT : T ≤ 650) (P : Machine) (hsP : P.states ≤ 2 ^ 16)
    (htP : P.time ≤ 2 ^ 350) (hpP : P.tapes ≤ 14) :
    (S.bundle hwf hcost.toWfCost hW1 (hW2' hcost hW1 hW2)).const P ≤ 2 ^ 690 := by
  unfold Bundle.const
  have hnS : nI + nσ ≤ 2 ^ 252 := by
    have h := S.nS_le
    have : (2 : ℕ) ^ 180 ≤ 2 ^ 252 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    generalize (2 : ℕ) ^ 180 = Z at *
    generalize (2 : ℕ) ^ 252 = Y at *
    omega
  refine (compConst_le_explicit (S.comps wfB Wg hwf) (S.bounds hwf hcost.toWfCost hW1
    (hW2' hcost hW1 hW2)) P (2 ^ 200) (2 ^ 16) (2 ^ 350) 14 SzP (2 ^ 20) (2 ^ 651) (2 ^ 252) 655
    hsP htP hpP (sizes_leV S hwf hcost hW1 hW2) (compTime_leV S hwf hcost hW1 hW2 hT)
    Nat.one_le_two_pow
    (show (2 : ℕ) ^ 182 ≤ 2 ^ 252 by norm_num) (show (2 : ℕ) ^ 183 ≤ 2 ^ 252 by norm_num)
    (show (2 : ℕ) ^ 252 ≤ 2 ^ 252 from le_rfl) (show (1 : ℕ) ≤ 2 ^ 252 by norm_num)
    (show (2 : ℕ) ^ 182 ≤ 2 ^ 252 by norm_num) (show (2 : ℕ) ^ 180 ≤ 2 ^ 252 by norm_num) hnS
    (confP_L_le.trans (by norm_num)) (show (2 : ℕ) ^ 200 ≤ 2 ^ 252 by norm_num) confP_L_le
    (by norm_num) (by norm_num)).trans compBound_conf

end Step

/-! ### Attribute hiding -/

variable {ms : Machines hkp confP}

/-- **Attribute hiding of the concrete scheme** at `confP` from the hardness of decision Ring-LWE
at the parameters of hybrids 3 and 5 with **`kb ≥ 952`** bits, given a `W_f` block meeting its
specification at a window width `384 ≤ Wg ≤ 2^20` and costing at most `2^T` steps, `T ≤ 650`, with
only tapes `0`, `2` nonblank afterwards (`WfCostV`). Each reduction's constant is at most `2^690`;
`64 · 2^256 · 2^690 = 2^952`. -/
theorem attributeHiding_conf' {wfB : XProg 256} {Wg T : ℕ} (hwf : WfSpec hkp confP wfB Wg)
    (hcost : WfCostV wfB Wg T) (hT : T ≤ 650) (hW1 : 384 ≤ Wg) (hW2 : Wg ≤ 2 ^ 20)
    (kb : ℕ) (hkb : 952 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding dateUniverse params (impl hkp confP ms) := by
  have hW2' : Wg ≤ 2 ^ 200 := hW2.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hC : ∀ {Inst Sec : Type} [Nonempty Inst] {nI nσ : ℕ} {ienc : FixedEnc Inst nI}
      {senc : FixedEnc Sec nσ} {setupI : Date → PMF Sec}
      {viewI : Inst → Sec → PK hkp confP × CT hkp confP} {sdI : Inst → Sec → SimData hkp confP}
      (S : StepComps ienc senc setupI viewI sdI) (P : Machine), P.states ≤ 2 ^ 16 →
      P.time ≤ 2 ^ 350 → P.tapes ≤ 14 →
      ((S.bundle hwf hcost.toWfCost hW1 hW2').const P : ℝ) ≤ (2 : ℝ) ^ 690 := by
    intro _ _ _ _ _ _ _ _ _ _ S P h1 h2 h3
    exact_mod_cast const_leV S hwf hcost hW1 hW2 hT P h1 h2 h3
  refine attributeHiding_of_comps_rlwe (fun u => hdecp u) realCovered_conf hL_conf simCovered_conf
    flood_conf statTerm_conf_ne_top stat_conf (.cbd 16) hχ_conf
    (step3.bundle hwf hcost.toWfCost hW1 hW2') (step5.bundle hwf hcost.toWfCost hW1 hW2')
    (stepI.bundle hwf hcost.toWfCost hW1 hW2') kb ((2 : ℝ) ^ 690) (by positivity)
    (hC step3 _ states_dec3M_conf time_dec3M_conf (le_of_eq tapes_dec3M))
    (hC step5 _ states_dec5M_conf time_dec5M_conf (le_of_eq (tapes_dec5M _)))
    (hC stepI _ states_dec3M_conf time_dec3M_conf (le_of_eq tapes_dec3M)) ?_ hard3 hard5
  calc 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * 2 ^ 690 = 2 ^ 952 := by
        rw [show params.secBits = 128 from rfl]; norm_num
    _ ≤ 2 ^ kb := pow_le_pow_right₀ (by norm_num) hkb

/-- **Attribute hiding from `952`-bit Ring-LWE** with the `W_f` block `wfB2 hkp confP 512`. -/
theorem attributeHiding_conf_rlwe' (kb : ℕ) (hkb : 952 ≤ kb)
    (hard3 : RingLWE.decision.HardAt (params3 Np (2 ^ Kp) kp (.cbd 16)) kb)
    (hard5 : RingLWE.decision.HardAt (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) kb) :
    AttributeHiding dateUniverse params (impl hkp confP ms) :=
  attributeHiding_conf' wfSpec_wfB2_confP wfCostV_wfB2 (by norm_num) Wc_ge Wc_le' kb hkb hard3 hard5

/-- **The registry's strength covers the strength needed**: `952 ≤ 2650 ≤ RingLWE.H` at the
parameters of hybrids 3 and 5. -/
theorem registry_covers_kb :
    952 ≤ RingLWE.H (params3 Np (2 ^ Kp) kp (.cbd 16)) ∧
      952 ≤ RingLWE.H (params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) := by
  refine ⟨(show 952 ≤ 2650 by norm_num).trans ?_, (show 952 ≤ 2650 by norm_num).trans ?_⟩
  · rw [params3_conf]; exact Strength.ringLWE_H_registry3
  · rw [params5_conf]; exact Strength.ringLWE_H_registry5

/-- **Attribute hiding of the concrete scheme from the registry's decision Ring-LWE alone**, via
the `952`-bit reductions: `HardAt` at `952 ≤ 2650 ≤ RingLWE.H` bits. -/
theorem attributeHiding_conf_registry'' (hR : RingLWE.decision.Holds) :
    AttributeHiding dateUniverse params (impl hkp confP ms) :=
  attributeHiding_conf_rlwe' 952 le_rfl
    (hR.hardAt (p := params3 Np (2 ^ Kp) kp (.cbd 16)) registry_covers_kb.1)
    (hR.hardAt (p := params5 Np (2 ^ Kp) kp (Fin confP.d) (.cbd 16)) registry_covers_kb.2)

end AdvancedEncryption.DualUse
