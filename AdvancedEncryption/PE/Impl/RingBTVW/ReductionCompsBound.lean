import PE.Impl.RingBTVW.ReductionComps
import PE.Impl.RingBTVW.Prog.PostSize
import PE.Impl.Game.HandlersPSize

/-!
# An explicit bound on the constant of the reduction from components

The constant `compConst cs cb P L` of the reduction from component programs
(`PE.Impl.RingBTVW.ReductionComps`) keeps the structure of `chainConst`:

  `compConst ≤ compBoundG nA nM pw sP tP p R Sz2 Lc Sl t`
  `          = 60 · S · 3 ^ (p + R + 30) · (5 + 4 (p + R + 30) + size S) + 11 tP + 11 Sl + 24`,

  `S = compStatesG nA nM pw sP Sz2 Lc t`
  `  = (t + 1) + 2 sP + 2 · postStatesG nA nM + 108 (pw + 3) · (28 + glue3 nA nM Lc + Sz2) + 3 (t + 1) + 108`,

(`compConst_le_explicitG`) from: the decoder's states `≤ sP`, time `≤ tP ≤ 2 ^ t`, tapes `≤ p`;
`2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP| ≤ Sz2` (the selection's components twice, the
key, authorization and challenge components once, `sum_states_compHandlersG`); the cut `c.L ≤ Lc`;
any bound `Sl ≤ 2 ^ t` on the slope of the chain's clock (`chainSlope`). Here

* `postStatesG nA nM = 1546 + 288 (nA + nM)`: the post-processing's states (`states_post_eq`);
* `glue3 nA nM Lc = 4479 + 1656 nA + 984 nM + 264 Lc`: the glue of the three handlers
  (`size_selH`, `size_keyHP`, `size_chalH`);
* `pw`: the length of the parameter word (`515`, `length_paramsWord_pu`);
* `108 (pw + 3) = 4 · 3³ · (pw + 3)` (three operations);
* `p + R + 30`: the tapes of the chain (`8` of the post-processing, `2 · 3 + 11`, the handlers'
  `R + 5`).

**The slope** for the codes of the branching-program universe (`nA = 128`, `nM = 1`,
`postPc nA 1 = 802`, `chainSlope_comp_le`): at most `11 · compTimeP cb + 2^26 X²` when every
length bound is at most `X ≥ 1`.

**The strength it asks of Ring-LWE**: with `C = compBoundG …`, attribute hiding follows from `kb`
bits as soon as `64 · 2 ^ 256 · C ≤ 2 ^ kb` (`attributeHiding_of_comps_rlwe`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.PE.Generic
open SigabaNeo.Inline

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {Sec Inst : Type} {nS : ℕ}
set_option linter.unusedSectionVars false

/-! ### The slope of the chain's clock for the branching-program codes -/

theorem postPc_bp : postPc nA 1 = 802 := by decide +kernel

/-- The slope of the post-processing of the branching-program codes. -/
theorem postSlope_bp (E : ℕ) :
    postA E nA 1 + postB E nA 1 = 1304959 + 8278 * E + 70 * (E * E) := by
  simp only [postA, postB, postClock, postProgTime, postM, postPc_bp]
  ring

/-- The bound on the encoded states, for the branching-program codes. -/
theorem stateBound_bp_le {Sig : Type} (sig : FixedEnc Sig nS) {W X : ℕ} (hW : W ≤ X)
    (hnS : nS ≤ X) : stateBound (puCodes sig) W ≤ X + 132 := by
  simp only [stateBound, nA_puCodes, nM_puCodes, nS_puCodes]
  rw [show nA = 128 from rfl]
  omega

/-- The arithmetic of `chainSlope_comp_le`. -/
theorem slope_arith_bp (N M E L T X : ℕ) (hX : 1 ≤ X) (hN : N ≤ 1357 * X) (hM : M ≤ 3259 * X)
    (hE : E ≤ X + 132) (hL : L ≤ X) :
    11 * (N * M + T + 20 + 2 * N * 3 + 2 * L + 4 * 3 + 4 * E + 38) + 10 +
      (1304959 + 8278 * E + 70 * (E * E)) ≤ 11 * T + 2 ^ 26 * (X * X) := by
  have hNM : N * M ≤ 4422463 * (X * X) := by
    calc N * M ≤ (1357 * X) * (3259 * X) := Nat.mul_le_mul hN hM
      _ = 4422463 * (X * X) := by ring
  have hEE : E * E ≤ 17689 * (X * X) := by
    calc E * E ≤ (133 * X) * (133 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 17689 * (X * X) := by ring
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
  have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
  rw [h26]
  generalize N * M = Z at *
  generalize E * E = F at *
  generalize X * X = Y at *
  omega

/-- **The slope of the clock of the reduction from components**, branching-program codes: at most
`11 · compTimeP cb + 2^26 X²` when every length bound is at most `X ≥ 1`. -/
theorem chainSlope_comp_le {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (L X : ℕ) (hX : 1 ≤ X)
    (hSsig : cb.Ssig ≤ X) (hLp : cb.Lp ≤ X) (hLk : cb.Lk ≤ X) (hLa : cb.La ≤ X) (hLc : cb.Lc ≤ X)
    (hW : W ≤ X) (hnS : nS ≤ X) (hcL : c.L ≤ X) (hL : L ≤ X) :
    chainSlope 3 (handlerQ0 cb [] + handlerQ1 (puCodes sig) c.L [] * 3) L
        (stateBound (puCodes sig) W)
        (postA (stateBound (puCodes sig) W) nA 1 + postB (stateBound (puCodes sig) W) nA 1) ≤
      11 * compTimeP cb + 2 ^ 26 * (X * X) := by
  have hE := stateBound_bp_le sig hW hnS
  rw [postSlope_bp]
  unfold chainSlope inlSlope handlerQ0 handlerQ1 glueNP glueMP glueN
  simp only [nA_puCodes, nM_puCodes, List.length_nil]
  rw [show nA = 128 from rfl]
  refine slope_arith_bp _ _ _ _ _ _ hX ?_ ?_ hE hL <;> omega

/-! ### The explicit bound, generic in the codes -/

/-- The states of the post-processing for `nA` attribute and `nM` message bits. -/
def postStatesG (nA nM : ℕ) : ℕ := 1546 + 288 * (nA + nM)

/-- The glue of the three handlers (besides their components), with the cut `Lc`. -/
def glue3 (nA nM Lc : ℕ) : ℕ := 4479 + 1656 * nA + 984 * nM + 264 * Lc

/-- **The states of the chain**, generic in the codes (`nA`, `nM`) and the parameter word (`pw`). -/
def compStatesG (nA nM pw sP Sz2 Lc t : ℕ) : ℕ :=
  (t + 1) + 2 * sP + 2 * postStatesG nA nM + 4 * 27 * (pw + 3) * (28 + glue3 nA nM Lc + Sz2) +
    3 * (t + 1) + 108

/-- **The explicit bound on the constant**, generic in the codes, with a slope bound `Sl`. -/
def compBoundG (nA nM pw sP tP p R Sz2 Lc Sl t : ℕ) : ℕ :=
  60 * compStatesG nA nM pw sP Sz2 Lc t * 3 ^ (p + R + 30) *
      (5 + 4 * (p + R + 30) + Nat.size (compStatesG nA nM pw sP Sz2 Lc t)) +
    11 * tP + 11 * Sl + 24

theorem compStatesG_mono {nA nM pw sP Sz2 Lc t sP' Sz2' Lc' : ℕ} (h1 : sP ≤ sP') (h2 : Sz2 ≤ Sz2')
    (h3 : Lc ≤ Lc') : compStatesG nA nM pw sP Sz2 Lc t ≤ compStatesG nA nM pw sP' Sz2' Lc' t := by
  unfold compStatesG glue3; gcongr

theorem compBoundG_mono {nA nM pw sP tP p R Sz2 Lc Sl t sP' tP' Sz2' Lc' Sl' : ℕ} (h1 : sP ≤ sP')
    (h2 : tP ≤ tP') (h3 : Sz2 ≤ Sz2') (h4 : Lc ≤ Lc') (h5 : Sl ≤ Sl') :
    compBoundG nA nM pw sP tP p R Sz2 Lc Sl t ≤ compBoundG nA nM pw sP' tP' p R Sz2' Lc' Sl' t := by
  have hS := compStatesG_mono (nA := nA) (nM := nM) (pw := pw) (t := t) h1 h3 h4
  have hz := Nat.size_le_size hS
  unfold compBoundG
  gcongr

/-- **The states of the three handlers together**, generic in the codes: the glue `glue3 nA 1 c.L`,
the selection's components twice, the key, authorization and challenge components once. -/
theorem sum_states_compHandlersG {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) (W : ℕ) :
    (compHandlers (c := c) cs W 0).states + (compHandlers (c := c) cs W 1).states +
        (compHandlers (c := c) cs W 2).states =
      glue3 (puCodes sig).nA (puCodes sig).nM c.L + (2 * (cs.setupP.size + cs.pubP.size) +
        cs.keyP.size + cs.authP.size + cs.chalP.size) := by
  unfold compHandlers
  rw [states_handlersP, states_handlersP, states_handlersP]
  rw [show (0 : Fin 3) = selectOp from rfl, show (1 : Fin 3) = keyGenOp from rfl,
    show (2 : Fin 3) = challengeOp from rfl, handlerProgP_sel, handlerProgP_key, handlerProgP_chal,
    size_selH, size_keyHP, size_chalH]
  simp only [List.length_nil]
  unfold glue3
  ring

/-- **The explicit bound on the constant of the reduction from components, generic in the
codes**: with `pw` the length of the parameter word, the decoder's states `≤ sP`, time
`≤ tP ≤ 2 ^ t`, tapes `≤ p`, `2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP| ≤ Sz2`, the cut
`c.L ≤ Lc` and the chain's slope `≤ Sl ≤ 2 ^ t`. -/
theorem compConst_le_explicitG {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (pw sP tP p Sz2 Lc Sl t : ℕ)
    (hpw : (paramsWord PUniv params).length = pw)
    (hsP : P.states ≤ sP) (htP : P.time ≤ tP) (hpP : P.tapes ≤ p)
    (hSz : 2 * (cs.setupP.size + cs.pubP.size) + cs.keyP.size + cs.authP.size + cs.chalP.size ≤ Sz2)
    (hcL' : c.L ≤ Lc) (htt : tP ≤ 2 ^ t)
    (hsl : chainSlope 3 (handlerQ0 cb [] + handlerQ1 (puCodes sig) c.L [] * 3) L
      (stateBound (puCodes sig) W)
      (postA (stateBound (puCodes sig) W) nA 1 + postB (stateBound (puCodes sig) W) nA 1) ≤ Sl)
    (hSl : Sl ≤ 2 ^ t) :
    compConst cs cb P L ≤
      compBoundG (puCodes sig).nA (puCodes sig).nM pw sP tP p R Sz2 Lc Sl t := by
  have hH := sum_states_compHandlersG (c := c) cs W
  set Q := handlerQ0 cb [] + handlerQ1 (puCodes sig) c.L [] * 3
  set E := stateBound (puCodes sig) W
  set pt := postA E nA 1 + postB E nA 1
  have hS : chainStates P (Post 0 0 nA 1) (compHandlers (c := c) cs W) Q L E pt
      (paramsWord PUniv params).length ≤
        compStatesG (puCodes sig).nA (puCodes sig).nM pw sP Sz2 Lc t := by
    unfold chainStates compStatesG
    rw [hpw, Fin.sum_univ_three, states_post_eq]
    have hP := (clockDigits_length_le_size P.tapes P.time).trans
      (size_le_of_le_two_pow (htP.trans htt))
    have hcI : inlSlope 3 Q L E ≤ 2 ^ t := by
      have := hsl.trans hSl; unfold chainSlope at this; omega
    have hzI := size_le_of_le_two_pow hcI
    have hzM := size_le_of_le_two_pow (hsl.trans hSl)
    have e : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [e]
    have hg : glue3 (puCodes sig).nA (puCodes sig).nM c.L ≤
        glue3 (puCodes sig).nA (puCodes sig).nM Lc := by
      unfold glue3; gcongr
    have hps : postStatesG (puCodes sig).nA (puCodes sig).nM = 1546 + 288 * (nA + 1) := rfl
    rw [hps]
    generalize nA = na at *
    generalize (compHandlers (c := c) cs W 0).states = a at *
    generalize (compHandlers (c := c) cs W 1).states = b at *
    generalize (compHandlers (c := c) cs W 2).states = d at *
    generalize glue3 (puCodes sig).nA (puCodes sig).nM c.L = g at *
    generalize glue3 (puCodes sig).nA (puCodes sig).nM Lc = g' at *
    have hab : a + b + d ≤ g' + Sz2 := by omega
    have : 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (pw + 3) ≤
        4 * 27 * (pw + 3) * (28 + g' + Sz2) := by
      have : 1 + (9 + a + (9 + b) + (9 + d)) ≤ 28 + g' + Sz2 := by omega
      calc 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (pw + 3)
          = 4 * 27 * (pw + 3) * (1 + (9 + a + (9 + b) + (9 + d))) := by ring
        _ ≤ 4 * 27 * (pw + 3) * (28 + g' + Sz2) := Nat.mul_le_mul_left _ this
    omega
  have hk : chainTapes P (Post 0 0 nA 1) 3 (R + 5) ≤ p + R + 30 := by
    unfold chainTapes; rw [tapes_post_eq]; omega
  unfold compConst redConstP chainConst
  unfold compBoundG
  have hsz := Nat.size_le_size hS
  have h3 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk
  have hm : 60 * chainStates P (Post 0 0 nA 1) (compHandlers (c := c) cs W) Q L E pt
        (paramsWord PUniv params).length * 3 ^ chainTapes P (Post 0 0 nA 1) 3 (R + 5) *
      (5 + 4 * chainTapes P (Post 0 0 nA 1) 3 (R + 5) + Nat.size (chainStates P (Post 0 0 nA 1)
        (compHandlers (c := c) cs W) Q L E pt (paramsWord PUniv params).length)) ≤
      60 * compStatesG (puCodes sig).nA (puCodes sig).nM pw sP Sz2 Lc t * 3 ^ (p + R + 30) *
        (5 + 4 * (p + R + 30) + Nat.size (compStatesG (puCodes sig).nA (puCodes sig).nM pw sP Sz2 Lc t)) := by
    gcongr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hm (Nat.mul_le_mul_left 11 htP))
    (Nat.mul_le_mul_left 11 hsl)) le_rfl

/-- **The explicit bound for the branching-program codes**: `compConst_le_explicitG` with the
slope of `chainSlope_comp_le` (every length bound at most `X ≥ 1`, the components' time at most
`Tc`). -/
theorem compConst_le_bp {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (sP tP p Sz2 Lc Tc X t : ℕ)
    (hsP : P.states ≤ sP) (htP : P.time ≤ tP) (hpP : P.tapes ≤ p)
    (hSz : 2 * (cs.setupP.size + cs.pubP.size) + cs.keyP.size + cs.authP.size + cs.chalP.size ≤ Sz2)
    (hT : compTimeP cb ≤ Tc) (hX : 1 ≤ X)
    (hSsig : cb.Ssig ≤ X) (hLp : cb.Lp ≤ X) (hLk : cb.Lk ≤ X) (hLa : cb.La ≤ X)
    (hLc : cb.Lc ≤ X) (hW : W ≤ X) (hnS : nS ≤ X) (hcL : c.L ≤ X) (hL : L ≤ X)
    (hcL' : c.L ≤ Lc) (htt : tP ≤ 2 ^ t) (hst : 11 * Tc + 2 ^ 26 * (X * X) ≤ 2 ^ t) :
    compConst cs cb P L ≤
      compBoundG 128 1 515 sP tP p R Sz2 Lc (11 * Tc + 2 ^ 26 * (X * X)) t := by
  have hc := chainSlope_comp_le (c := c) cs cb L X hX hSsig hLp hLk hLa hLc hW hnS hcL hL
  exact compConst_le_explicitG cs cb P L 515 sP tP p Sz2 Lc _ t length_paramsWord_pu hsP htP hpP
    hSz hcL' htt (hc.trans (by omega)) hst

end AdvancedEncryption.RingBTVW
