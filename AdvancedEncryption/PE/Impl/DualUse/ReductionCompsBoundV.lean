import PE.Impl.DualUse.ReductionCompsBound

/-!
# An explicit bound on the constant of the reduction from components

`compConst_le_two_pow` (`ReductionCompsBound`) bounds `compConst cs cb P L` by
`2 ^ (r + g + 11 + 65 k / 41) + 2 ^ (t + 6)`, each component's states charged the largest
(`10 · 2 ^ s`) and every factor rounded to a power of two. Here **`compConst_le_explicit`** keeps
the structure of `chainConst`:

  `compConst ≤ compBound sP tP p R Sz Lc Tc X t`
  `          = 60 · S · 3 ^ (p + R + 30) · (5 + 4 (p + R + 30) + size S) + 11 tP + 11 (11 Tc + 898942 X²) + 24`

with the **states of the chain**

  `S = (t + 1) + 2 sP + 9428 + 55944 · (28 + 3 · (10638 + 264 Lc + 2 Sz)) + 3 (t + 1) + 108`,

from: the decoder's states `≤ sP`, time `≤ tP ≤ 2 ^ t`, tapes `≤ p`; the **sum** of the
components' sizes `≤ Sz`; their time `compTimeP cb ≤ Tc`; every length bound `≤ X`; the cut
`c.L ≤ Lc`; the slope `11 Tc + 898942 X² ≤ 2 ^ t`.

Where the numbers come from (date-window codes `nA = 10`, `nM = 1`, the parameter word of `515`
bits; for another universe only these change): `9428 = 2 · 4714` (the post-processing's states),
`55944 = 4 · 3³ · (515 + 3)`, `28 = 1 + 3 · 9`, `10638 + 264 Lc` the glue of a handler
(`glueSize`), `2 Sz` its components (`size_handlerProgP_le`), `p + R + 30` the tapes of the chain
(`8` of the post-processing, `2 · 3 + 11`, the handlers' `R + 5`).

**`compConst_le_explicit2`** (`compBound2`) charges each handler its own components
(`sum_states_compHandlers`: the selection's twice, the key, authorization and challenge components
once): `S` with `55944 · (28 + 22023 + 264 Lc + Sz2)`, `Sz2 ≥ 2 (|setupP| + |pubP|) + |keyP| +
|authP| + |chalP|` — about six times smaller when the key component dominates.

**The strength it asks of Ring-LWE**: with `C = compBound …`, attribute hiding follows from
`kb` bits as soon as `64 · 2 ^ 256 · C ≤ 2 ^ kb` (`attributeHiding_of_comps_rlwe`). The first
term dominates when the component times are moderate: `log₂ C ≈ log₂ S + 1.585 (p + R + 30) +
log₂ (60 (5 + 4 (p + R + 30) + log₂ S))`, `log₂ S ≈ 18.4 + log₂ Sz`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open SigabaNeo.Inline

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {Sec Inst : Type} {nS : ℕ}
set_option linter.unusedSectionVars false

/-- The states of the chain, from the bounds. -/
def compStatesB (sP Sz Lc t : ℕ) : ℕ :=
  (t + 1) + 2 * sP + 9428 + 55944 * (28 + 3 * (10638 + 264 * Lc + 2 * Sz)) + 3 * (t + 1) + 108

/-- **The explicit bound on the constant of the reduction from components.** -/
def compBound (sP tP p R Sz Lc Tc X t : ℕ) : ℕ :=
  60 * compStatesB sP Sz Lc t * 3 ^ (p + R + 30) *
      (5 + 4 * (p + R + 30) + Nat.size (compStatesB sP Sz Lc t)) +
    11 * tP + 11 * (11 * Tc + 898942 * (X * X)) + 24

theorem compBound_mono {sP tP p R Sz Lc Tc X t sP' tP' Sz' Lc' Tc' X' : ℕ} (h1 : sP ≤ sP')
    (h2 : tP ≤ tP') (h3 : Sz ≤ Sz') (h4 : Lc ≤ Lc') (h5 : Tc ≤ Tc') (h6 : X ≤ X') :
    compBound sP tP p R Sz Lc Tc X t ≤ compBound sP' tP' p R Sz' Lc' Tc' X' t := by
  have hS : compStatesB sP Sz Lc t ≤ compStatesB sP' Sz' Lc' t := by
    unfold compStatesB; gcongr
  have hz := Nat.size_le_size hS
  unfold compBound
  gcongr

/-- **An explicit bound on the constant of the reduction from components**: the structure of
`chainConst`, with the handlers' states bounded by the glue and twice the sum of the components'
sizes. -/
theorem compConst_le_explicit {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (sP tP p Sz Lc Tc X t : ℕ)
    (hsP : P.states ≤ sP) (htP : P.time ≤ tP) (hpP : P.tapes ≤ p)
    (hSz : cs.setupP.size + cs.pubP.size + cs.keyP.size + cs.authP.size + cs.chalP.size ≤ Sz)
    (hT : compTimeP cb ≤ Tc) (hX : 1 ≤ X)
    (hSsig : cb.Ssig ≤ X) (hLp : cb.Lp ≤ X) (hLk : cb.Lk ≤ X) (hLa : cb.La ≤ X)
    (hLc : cb.Lc ≤ X) (hW : W ≤ X) (hnS : nS ≤ X) (hcL : c.L ≤ X) (hL : L ≤ X)
    (hcL' : c.L ≤ Lc) (htt : tP ≤ 2 ^ t) (hst : 11 * Tc + 898942 * (X * X) ≤ 2 ^ t) :
    compConst cs cb P L ≤ compBound sP tP p R Sz Lc Tc X t := by
  -- the slope
  have hc := chainSlope_comp_le (c := c) cs cb L X hX hSsig hLp hLk hLa hLc hW hnS hcL hL
  have hc' : chainSlope 3 (handlerQ0 cb [] + handlerQ1 (dateCodes sig) c.L [] * 3) L
      (stateBound (dateCodes sig) W)
      (postA (stateBound (dateCodes sig) W) 10 1 + postB (stateBound (dateCodes sig) W) 10 1) ≤
      11 * Tc + 898942 * (X * X) := hc.trans (by omega)
  -- the handlers
  have hH : ∀ o, (compHandlers (c := c) cs W o).states ≤ 10638 + 264 * Lc + 2 * Sz := by
    intro o
    unfold compHandlers
    rw [states_handlersP]
    have h := size_handlerProgP_le (dateCodes sig) cs c.L [] o
    simp only [glueSize, nA_dateCodes, nM_dateCodes, List.length_nil] at h
    omega
  -- the states of the chain
  set Q := handlerQ0 cb [] + handlerQ1 (dateCodes sig) c.L [] * 3
  set E := stateBound (dateCodes sig) W
  set pt := postA E 10 1 + postB E 10 1
  have hS : chainStates P (Post 0 0 10 1) (compHandlers (c := c) cs W) Q L E pt
      (paramsWord dateUniverse params).length ≤ compStatesB sP Sz Lc t := by
    unfold chainStates compStatesB
    rw [length_paramsWord_date, Fin.sum_univ_three, states_post_date]
    have hP := (clockDigits_length_le_size P.tapes P.time).trans
      (size_le_of_le_two_pow (htP.trans htt))
    have hcI : inlSlope 3 Q L E ≤ 2 ^ t := by
      have := hc'.trans hst; unfold chainSlope at this; omega
    have hzI := size_le_of_le_two_pow hcI
    have hzM := size_le_of_le_two_pow (hc'.trans hst)
    have h0 := hH 0; have h1 := hH 1; have h2 := hH 2
    have e : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [e]
    generalize (compHandlers (c := c) cs W 0).states = a at *
    generalize (compHandlers (c := c) cs W 1).states = b at *
    generalize (compHandlers (c := c) cs W 2).states = d at *
    generalize 10638 + 264 * Lc + 2 * Sz = Y at *
    have : 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (515 + 3) ≤ 55944 * (28 + 3 * Y) := by
      omega
    omega
  have hk : chainTapes P (Post 0 0 10 1) 3 (R + 5) ≤ p + R + 30 := by
    unfold chainTapes; rw [tapes_post_eq]; omega
  unfold compConst redConstP chainConst
  unfold compBound
  have hsz := Nat.size_le_size hS
  have h3 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk
  have hm : 60 * chainStates P (Post 0 0 10 1) (compHandlers (c := c) cs W) Q L E pt
        (paramsWord dateUniverse params).length * 3 ^ chainTapes P (Post 0 0 10 1) 3 (R + 5) *
      (5 + 4 * chainTapes P (Post 0 0 10 1) 3 (R + 5) + Nat.size (chainStates P (Post 0 0 10 1)
        (compHandlers (c := c) cs W) Q L E pt (paramsWord dateUniverse params).length)) ≤
      60 * compStatesB sP Sz Lc t * 3 ^ (p + R + 30) *
        (5 + 4 * (p + R + 30) + Nat.size (compStatesB sP Sz Lc t)) := by
    gcongr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hm (Nat.mul_le_mul_left 11 htP))
    (Nat.mul_le_mul_left 11 hc')) le_rfl

/-! ### Each handler with its own components -/

/-- **The states of the three handlers together**: the glue, the selection's components twice
(both branches of its state test), the key, authorization and challenge components once. -/
theorem sum_states_compHandlers {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) (W : ℕ) :
    (compHandlers (c := c) cs W 0).states + (compHandlers (c := c) cs W 1).states +
        (compHandlers (c := c) cs W 2).states =
      22023 + 264 * c.L + (2 * (cs.setupP.size + cs.pubP.size) + cs.keyP.size + cs.authP.size +
        cs.chalP.size) := by
  unfold compHandlers
  rw [states_handlersP, states_handlersP, states_handlersP]
  rw [show (0 : Fin 3) = selectOp from rfl, show (1 : Fin 3) = keyGenOp from rfl,
    show (2 : Fin 3) = challengeOp from rfl, handlerProgP_sel, handlerProgP_key, handlerProgP_chal,
    size_selH, size_keyHP, size_chalH]
  simp only [nA_dateCodes, nM_dateCodes, List.length_nil]
  ring

/-- The states of the chain, each handler charged its own components (`Sz2` bounds
`2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP|`). -/
def compStatesB2 (sP Sz2 Lc t : ℕ) : ℕ :=
  (t + 1) + 2 * sP + 9428 + 55944 * (28 + 22023 + 264 * Lc + Sz2) + 3 * (t + 1) + 108

/-- **The explicit bound**, each handler charged its own components. -/
def compBound2 (sP tP p R Sz2 Lc Tc X t : ℕ) : ℕ :=
  60 * compStatesB2 sP Sz2 Lc t * 3 ^ (p + R + 30) *
      (5 + 4 * (p + R + 30) + Nat.size (compStatesB2 sP Sz2 Lc t)) +
    11 * tP + 11 * (11 * Tc + 898942 * (X * X)) + 24

/-- **The explicit bound on the constant of the reduction from components**, each handler
charged its own components: as `compConst_le_explicit` with
`2 (|setupP| + |pubP|) + |keyP| + |authP| + |chalP| ≤ Sz2` (the key component counted once). -/
theorem compConst_le_explicit2 {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (sP tP p Sz2 Lc Tc X t : ℕ)
    (hsP : P.states ≤ sP) (htP : P.time ≤ tP) (hpP : P.tapes ≤ p)
    (hSz : 2 * (cs.setupP.size + cs.pubP.size) + cs.keyP.size + cs.authP.size + cs.chalP.size ≤ Sz2)
    (hT : compTimeP cb ≤ Tc) (hX : 1 ≤ X)
    (hSsig : cb.Ssig ≤ X) (hLp : cb.Lp ≤ X) (hLk : cb.Lk ≤ X) (hLa : cb.La ≤ X)
    (hLc : cb.Lc ≤ X) (hW : W ≤ X) (hnS : nS ≤ X) (hcL : c.L ≤ X) (hL : L ≤ X)
    (hcL' : c.L ≤ Lc) (htt : tP ≤ 2 ^ t) (hst : 11 * Tc + 898942 * (X * X) ≤ 2 ^ t) :
    compConst cs cb P L ≤ compBound2 sP tP p R Sz2 Lc Tc X t := by
  have hc := chainSlope_comp_le (c := c) cs cb L X hX hSsig hLp hLk hLa hLc hW hnS hcL hL
  have hc' : chainSlope 3 (handlerQ0 cb [] + handlerQ1 (dateCodes sig) c.L [] * 3) L
      (stateBound (dateCodes sig) W)
      (postA (stateBound (dateCodes sig) W) 10 1 + postB (stateBound (dateCodes sig) W) 10 1) ≤
      11 * Tc + 898942 * (X * X) := hc.trans (by omega)
  have hH := sum_states_compHandlers (c := c) cs W
  set Q := handlerQ0 cb [] + handlerQ1 (dateCodes sig) c.L [] * 3
  set E := stateBound (dateCodes sig) W
  set pt := postA E 10 1 + postB E 10 1
  have hS : chainStates P (Post 0 0 10 1) (compHandlers (c := c) cs W) Q L E pt
      (paramsWord dateUniverse params).length ≤ compStatesB2 sP Sz2 Lc t := by
    unfold chainStates compStatesB2
    rw [length_paramsWord_date, Fin.sum_univ_three, states_post_date]
    have hP := (clockDigits_length_le_size P.tapes P.time).trans
      (size_le_of_le_two_pow (htP.trans htt))
    have hcI : inlSlope 3 Q L E ≤ 2 ^ t := by
      have := hc'.trans hst; unfold chainSlope at this; omega
    have hzI := size_le_of_le_two_pow hcI
    have hzM := size_le_of_le_two_pow (hc'.trans hst)
    have e : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [e]
    generalize (compHandlers (c := c) cs W 0).states = a at *
    generalize (compHandlers (c := c) cs W 1).states = b at *
    generalize (compHandlers (c := c) cs W 2).states = d at *
    have hab : a + b + d ≤ 22023 + 264 * Lc + Sz2 := by
      rw [hH]; have := Nat.mul_le_mul_left 264 hcL'; omega
    have : 4 * (27 * (1 + (9 + a + (9 + b) + (9 + d)))) * (515 + 3) ≤
        55944 * (28 + 22023 + 264 * Lc + Sz2) := by omega
    omega
  have hk : chainTapes P (Post 0 0 10 1) 3 (R + 5) ≤ p + R + 30 := by
    unfold chainTapes; rw [tapes_post_eq]; omega
  unfold compConst redConstP chainConst
  unfold compBound2
  have hsz := Nat.size_le_size hS
  have h3 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hk
  have hm : 60 * chainStates P (Post 0 0 10 1) (compHandlers (c := c) cs W) Q L E pt
        (paramsWord dateUniverse params).length * 3 ^ chainTapes P (Post 0 0 10 1) 3 (R + 5) *
      (5 + 4 * chainTapes P (Post 0 0 10 1) 3 (R + 5) + Nat.size (chainStates P (Post 0 0 10 1)
        (compHandlers (c := c) cs W) Q L E pt (paramsWord dateUniverse params).length)) ≤
      60 * compStatesB2 sP Sz2 Lc t * 3 ^ (p + R + 30) *
        (5 + 4 * (p + R + 30) + Nat.size (compStatesB2 sP Sz2 Lc t)) := by
    gcongr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hm (Nat.mul_le_mul_left 11 htP))
    (Nat.mul_le_mul_left 11 hc')) le_rfl

end AdvancedEncryption.DualUse
