import PE.Impl.ExpLUT.AH.RedChain
import PE.Impl.RingBTVW.ReductionCompsBound
import PE.Impl.ExpLUT.AH.Flood
/-!
# The constant of the reduction from components, explicitly (package G2)

The constant `rc.const` of the reduction machine of components (`RedComps`, `AH/RedChain`) keeps
the structure of `chainConst`; as for the dual-use reductions (`RingBTVW.compConst_le_bp`):

* `const_le_explicit`: `rc.const ≤ compBoundG 128 1 515 sP tP p R Sz2 L Sl t` from the decoder's
  states `≤ sP`, time `≤ tP ≤ 2^t`, tapes `≤ p`, the components' sizes
  `2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP| ≤ Sz2` and a bound `Sl ≤ 2^t` on the slope;
* `chainSlope_le`: the slope is at most `11 · compTimeP cb + 2^26 X²` when every length bound is at
  most `X ≥ 1`;
* **`const_le`**: both together;
* **`attributeHiding_Dc_comps`**: **attribute hiding at `Dc` from the registered circular Ring-LWE
  assumption**, given a `RedComps` at `Dc` whose constant satisfies `64 · 2^256 · const ≤ 2^1155`
  (i.e. `log₂ const ≤ 893`): no `RedMachine` hypothesis is left.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Generic
open AdvancedEncryption.RingBTVW (postStatesG glue3 compStatesG compBoundG compStatesG_mono
  postPc_bp postSlope_bp slope_arith_bp)
open SigabaNeo.Inline

theorem length_paramsWord_w8 : (paramsWord (univ w8) params).length = 515 := by
  rw [paramsWord, encodeTuple, Turing.MultiTapeTM.length_encList]
  simp [params, univ, Turing.MultiTapeTM.encBits]

section Bound

variable {D : Dims} {kb : KeyBoxes D} {L : ℕ} {impl : Impl sig} {χfl : PMF (Rg D)}

namespace RedComps

variable (rc : RedComps D kb L impl χfl)

theorem stateBound_le {X : ℕ} (hW : rc.W ≤ X) (hnS : rc.nS ≤ X) : rc.E ≤ X + 132 := by
  show stateBound (w8Codes rc.senc) rc.W ≤ _
  simp only [stateBound]
  show max rc.W (1 + 128 + rc.nS + 3) ≤ X + 132
  omega

/-- **The slope of the clock of the reduction of the components**: at most
`11 · compTimeP cb + 2^26 X²` when every length bound is at most `X ≥ 1`. -/
theorem chainSlope_le (X : ℕ) (hX : 1 ≤ X)
    (hSsig : rc.cb.Ssig ≤ X) (hLp : rc.cb.Lp ≤ X) (hLk : rc.cb.Lk ≤ X) (hLa : rc.cb.La ≤ X)
    (hLc : rc.cb.Lc ≤ X) (hW : rc.W ≤ X) (hnS : rc.nS ≤ X) (hL : L ≤ X) (hLa' : rc.La ≤ X) :
    chainSlope 3 (handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3) rc.La rc.E
        (postA rc.E 128 1 + postB rc.E 128 1) ≤
      11 * compTimeP rc.cb + 2 ^ 26 * (X * X) := by
  have hE := rc.stateBound_le hW hnS
  rw [show (128 : ℕ) = AdvancedEncryption.RingBTVW.nA from rfl, postSlope_bp]
  unfold chainSlope inlSlope handlerQ0 handlerQ1 glueNP glueMP glueN
  simp only [List.length_nil]
  have e1 : (w8Codes rc.senc).nA = 128 := rfl
  have e2 : (w8Codes rc.senc).nM = 1 := rfl
  have e3 : stateBound (w8Codes rc.senc) rc.W = rc.E := rfl
  rw [e1, e2, e3]
  refine slope_arith_bp _ _ _ _ _ _ hX ?_ ?_ hE hLa' <;> omega

/-- **The states of the three handlers together**: the glue, the selection's components twice,
the key, authorization and challenge components once. -/
theorem sum_states_H :
    (rc.H 0).states + (rc.H 1).states + (rc.H 2).states =
      glue3 128 1 L + (2 * (rc.cs.setupP.size + rc.cs.pubP.size) +
        rc.cs.keyP.size + rc.cs.authP.size + rc.cs.chalP.size) := by
  unfold H
  rw [states_handlersP, states_handlersP, states_handlersP]
  rw [show (0 : Fin 3) = selectOp from rfl, show (1 : Fin 3) = keyGenOp from rfl,
    show (2 : Fin 3) = challengeOp from rfl, handlerProgP_sel, handlerProgP_key, handlerProgP_chal,
    size_selH, size_keyHP, size_chalH]
  simp only [List.length_nil]
  unfold glue3
  show _ = 4479 + 1656 * 128 + 984 * 1 + 264 * L + _
  have e1 : (w8Codes rc.senc).nA = 128 := rfl
  have e2 : (w8Codes rc.senc).nM = 1 := rfl
  rw [e1, e2]
  ring

/-- **The explicit bound on the constant**: the decoder's states `≤ sP`, time `≤ tP ≤ 2^t`, tapes
`≤ p`, the components' sizes `≤ Sz2`, the slope `≤ Sl ≤ 2^t`. -/
theorem const_le_explicit (sP tP p Sz2 Sl t : ℕ)
    (hsP : rc.P.states ≤ sP) (htP : rc.P.time ≤ tP) (hpP : rc.P.tapes ≤ p)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ Sz2) (htt : tP ≤ 2 ^ t)
    (hsl : chainSlope 3 (handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3) rc.La rc.E
      (postA rc.E 128 1 + postB rc.E 128 1) ≤ Sl)
    (hSl : Sl ≤ 2 ^ t) :
    rc.const ≤ compBoundG 128 1 515 sP tP p rc.R Sz2 L Sl t := by
  have hH := rc.sum_states_H
  set Q := handlerQ0 rc.cb [] + handlerQ1 (w8Codes rc.senc) L [] * 3
  set E := rc.E
  set pt := postA E 128 1 + postB E 128 1
  have hS : chainStates rc.P (Post 0 0 128 1) rc.H Q rc.La E pt
      (paramsWord (univ w8) params).length ≤ compStatesG 128 1 515 sP Sz2 L t := by
    unfold chainStates compStatesG
    rw [length_paramsWord_w8, Fin.sum_univ_three, states_post_eq]
    have hP := (clockDigits_length_le_size rc.P.tapes rc.P.time).trans
      (size_le_of_le_two_pow (htP.trans htt))
    have hcI : inlSlope 3 Q rc.La E ≤ 2 ^ t := by
      have := hsl.trans hSl; unfold chainSlope at this; omega
    have hzI := size_le_of_le_two_pow hcI
    have hzM := size_le_of_le_two_pow (hsl.trans hSl)
    have e : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [e]
    have hps : postStatesG 128 1 = 1546 + 288 * (128 + 1) := rfl
    rw [hps]
    generalize (rc.H 0).states = a at *
    generalize (rc.H 1).states = b at *
    generalize (rc.H 2).states = d at *
    generalize glue3 128 1 L = g at *
    have : 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (515 + 3) ≤
        4 * 27 * (515 + 3) * (28 + g + Sz2) := by
      have : 1 + (9 + a + (9 + b) + (9 + d)) ≤ 28 + g + Sz2 := by omega
      calc 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (515 + 3)
          = 4 * 27 * (515 + 3) * (1 + (9 + a + (9 + b) + (9 + d))) := by ring
        _ ≤ 4 * 27 * (515 + 3) * (28 + g + Sz2) := Nat.mul_le_mul_left _ this
    omega
  have hk : chainTapes rc.P (Post 0 0 128 1) 3 (rc.R + 5) ≤ p + rc.R + 30 := by
    unfold chainTapes; rw [tapes_post_eq]; omega
  unfold const chainConst
  unfold compBoundG
  have hsz := Nat.size_le_size hS
  have h3 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk
  have hm : 60 * chainStates rc.P (Post 0 0 128 1) rc.H Q rc.La E pt
        (paramsWord (univ w8) params).length * 3 ^ chainTapes rc.P (Post 0 0 128 1) 3 (rc.R + 5) *
      (5 + 4 * chainTapes rc.P (Post 0 0 128 1) 3 (rc.R + 5) + Nat.size (chainStates rc.P
        (Post 0 0 128 1) rc.H Q rc.La E pt (paramsWord (univ w8) params).length)) ≤
      60 * compStatesG 128 1 515 sP Sz2 L t * 3 ^ (p + rc.R + 30) *
        (5 + 4 * (p + rc.R + 30) + Nat.size (compStatesG 128 1 515 sP Sz2 L t)) := by
    gcongr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hm (Nat.mul_le_mul_left 11 htP))
    (Nat.mul_le_mul_left 11 hsl)) le_rfl

/-- **The explicit bound on the constant of the reduction of the components**: every length
bound at most `X ≥ 1`, the components' time at most `Tc`. -/
theorem const_le (sP tP p Sz2 Tc X t : ℕ)
    (hsP : rc.P.states ≤ sP) (htP : rc.P.time ≤ tP) (hpP : rc.P.tapes ≤ p)
    (hSz : 2 * (rc.cs.setupP.size + rc.cs.pubP.size) + rc.cs.keyP.size + rc.cs.authP.size +
      rc.cs.chalP.size ≤ Sz2)
    (hT : compTimeP rc.cb ≤ Tc) (hX : 1 ≤ X)
    (hSsig : rc.cb.Ssig ≤ X) (hLp : rc.cb.Lp ≤ X) (hLk : rc.cb.Lk ≤ X) (hLa : rc.cb.La ≤ X)
    (hLc : rc.cb.Lc ≤ X) (hW : rc.W ≤ X) (hnS : rc.nS ≤ X) (hL : L ≤ X) (hLa' : rc.La ≤ X)
    (htt : tP ≤ 2 ^ t) (hst : 11 * Tc + 2 ^ 26 * (X * X) ≤ 2 ^ t) :
    rc.const ≤ compBoundG 128 1 515 sP tP p rc.R Sz2 L (11 * Tc + 2 ^ 26 * (X * X)) t := by
  have hc := rc.chainSlope_le X hX hSsig hLp hLk hLa hLc hW hnS hL hLa'
  exact rc.const_le_explicit sP tP p Sz2 _ t hsP htP hpP hSz htt (hc.trans (by omega)) hst

end RedComps

end Bound

/-! ### Attribute hiding at `Dc` from components -/

open AdvancedEncryption.ExpLUT.Params in

/-- **Attribute hiding at the concrete parameters from the registered circular Ring-LWE
assumption, given the reduction's components**: no `RedMachine` hypothesis is left; the
components' constant must satisfy `64 · 2^256 · const ≤ 2^1155` (`log₂ const ≤ 893`). -/
theorem attributeHiding_Dc_comps (hR : CircularRingLWE.decision.Holds) {impl : Impl sig}
    {kb : KeyBoxes Dc} {L : ℕ} (hI : ImplSpec Dc kb L impl χc χc χfl) (hkb : KbCover kb coverBound)
    (hL : predLen ≤ L) (rc : RedComps Dc kb L impl χfl)
    (hC : 64 * ((2 : ℝ) ^ 128) ^ 2 * (rc.const : ℝ) ≤ (2 : ℝ) ^ 1155) :
    AttributeHiding (univ w8) params impl := by
  have hpos : (0 : ℝ) < rc.const := by
    have : 0 < rc.const := by unfold RedComps.const chainConst; omega
    exact_mod_cast this
  exact attributeHiding_Dc_registry' hR hI hkb rc.const hpos hC fun A Dm _ =>
    redMachine_of_comps rc hI.eval hL le_rfl A Dm

end AdvancedEncryption.ExpLUT.Prog
