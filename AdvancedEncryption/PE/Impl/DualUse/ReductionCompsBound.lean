import PE.Impl.DualUse.ReductionComps
import PE.Impl.DualUse.Prog.PostSize
import PE.Impl.Game.HandlersPSize

/-!
# A power-of-two bound on the constant of the reduction from components

`compConst_le_two_pow`: the constant `compConst cs cb P L` of the cost of the reduction from
component programs (`PE.Impl.DualUse.ReductionComps`) is at most

  `2 ^ (r + g + 11 + 65 k / 41) + 2 ^ (t + 6)`

from abstract bounds only: the decoder's states `≤ 2 ^ r`, time `≤ 2 ^ t` and tapes `≤ p`; the
components' sizes `≤ 2 ^ s`; their time `compTimeP cb ≤ 2 ^ τ`; the length bounds `cb.Ssig`, `cb.Lp`,
`cb.Lk`, `cb.La`, `cb.Lc`, `W`, `nS`, `c.L` and `L` each `≤ 2 ^ ℓ`; and the exponent conditions
`ℓ + 30 ≤ r`, `s + 30 ≤ r`, `t + 28 ≤ 2 ^ r`, `τ + 5 ≤ t`, `2 ℓ + 21 ≤ t`, `p + R + 30 ≤ k` and
`4 k + r + 10 ≤ 2 ^ g` (all closable by `norm_num` for concrete numbers). It reduces to
`redConstP_le_two_pow` through:

* the handler states (`states_handlersP`, `size_handlerProgP_le`): each at most
  `10638 + 264 c.L + 10 · 2 ^ s`;
* the post-processing `Post 0 0 nA 1`: `4714` states and `8` tapes (`states_post_date`,
  `tapes_post_eq`);
* the parameter word: `515` bits (`length_paramsWord_date`);
* the slope of the clock (`chainSlope_comp_le`): at most `11 · compTimeP cb + 898942 · 4 ^ ℓ`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability SigabaNeo.Tape
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord AdvancedEncryption.PE.Generic
open SigabaNeo.Inline

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {Sec Inst : Type} {nS : ℕ}
set_option linter.unusedSectionVars false

/-- The parameter word of the date-window universe has `515` bits. -/
theorem length_paramsWord_date : (paramsWord PUniv params).length = 515 := length_paramsWord_pu

theorem nA_dateCodes {Sig : Type} (sig : FixedEnc Sig nS) : (puCodes sig).nA = 10 := rfl
theorem nM_dateCodes {Sig : Type} (sig : FixedEnc Sig nS) : (puCodes sig).nM = 1 := rfl
theorem nS_dateCodes {Sig : Type} (sig : FixedEnc Sig nS) : (puCodes sig).nS = nS := rfl

theorem postPc_date : postPc nA 1 = 94 := by decide

/-- The slope of the post-processing of the date-window codes. -/
theorem postSlope_date (E : ℕ) :
    postA E nA 1 + postB E nA 1 = 19939 + 1198 * E + 70 * (E * E) := by
  simp only [postA, postB, postClock, postProgTime, postM, postPc_date]
  ring

/-- The bound on the encoded states, for the date-window codes. -/
theorem stateBound_date_le {Sig : Type} (sig : FixedEnc Sig nS) {W X : ℕ} (hW : W ≤ X)
    (hnS : nS ≤ X) : stateBound (puCodes sig) W ≤ X + 14 := by
  simp only [stateBound, nA_dateCodes, nM_dateCodes, nS_dateCodes]
  omega

/-- **The handler states of the components**: each at most `10638 + 264 c.L + 10 · 2 ^ s`. -/
theorem states_compHandlers_le {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) (W s : ℕ)
    (hsetup : cs.setupP.size ≤ 2 ^ s) (hpub : cs.pubP.size ≤ 2 ^ s)
    (hkey : cs.keyP.size ≤ 2 ^ s) (hauth : cs.authP.size ≤ 2 ^ s) (hchal : cs.chalP.size ≤ 2 ^ s)
    (o : Fin 3) :
    (compHandlers (c := c) cs W o).states ≤ 10638 + 264 * c.L + 10 * 2 ^ s := by
  unfold compHandlers
  rw [states_handlersP]
  have h := size_handlerProgP_le (puCodes sig) cs c.L [] o
  simp only [glueSize, nA_dateCodes, nM_dateCodes, List.length_nil] at h
  omega

/-- The arithmetic of `chainSlope_comp_le`. -/
theorem slope_arith (N M E L T X : ℕ) (hX : 1 ≤ X) (hN : N ≤ 177 * X) (hM : M ≤ 427 * X)
    (hE : E ≤ X + 14) (hL : L ≤ X) :
    11 * (N * M + T + 20 + 2 * N * 3 + 2 * L + 4 * 3 + 4 * E + 38) + 10 +
      (19939 + 1198 * E + 70 * (E * E)) ≤ 11 * T + 898942 * (X * X) := by
  have hNM : N * M ≤ 75579 * (X * X) := by
    calc N * M ≤ (177 * X) * (427 * X) := Nat.mul_le_mul hN hM
      _ = 75579 * (X * X) := by ring
  have hEE : E * E ≤ 225 * (X * X) := by
    calc E * E ≤ (15 * X) * (15 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 225 * (X * X) := by ring
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
  generalize N * M = Z at *
  generalize E * E = F at *
  generalize X * X = Y at *
  omega

/-- **The slope of the clock of the reduction from components**: at most
`11 · compTimeP cb + 898942 X²` when every length bound is at most `X ≥ 1`. -/
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
      11 * compTimeP cb + 898942 * (X * X) := by
  have hE := stateBound_date_le sig hW hnS
  rw [postSlope_date]
  unfold chainSlope inlSlope handlerQ0 handlerQ1 glueNP glueMP glueN
  simp only [nA_dateCodes, nM_dateCodes, List.length_nil]
  refine slope_arith _ _ _ _ _ _ hX ?_ ?_ hE hL <;> omega

/-- **A power-of-two bound on the constant of the reduction from components**, from abstract
bounds on the decoder `P` (states `≤ 2 ^ r`, time `≤ 2 ^ t`, tapes `≤ p`), on the components
(sizes `≤ 2 ^ s`, time `compTimeP cb ≤ 2 ^ τ`), on the lengths (`≤ 2 ^ ℓ`) and on the cut `c.L ≤ 2 ^ lc`
(which alone enters the states of the handlers, so `ℓ` need not be below `r`). -/
theorem compConst_le_two_pow {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : PUniv.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → PUniv.Attr → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (puCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (r t p s τ ℓ lc k' g : ℕ)
    (hsP : P.states ≤ 2 ^ r) (htP : P.time ≤ 2 ^ t) (hpP : P.tapes ≤ p)
    (hsetup : cs.setupP.size ≤ 2 ^ s) (hpub : cs.pubP.size ≤ 2 ^ s)
    (hkey : cs.keyP.size ≤ 2 ^ s) (hauth : cs.authP.size ≤ 2 ^ s) (hchal : cs.chalP.size ≤ 2 ^ s)
    (hT : compTimeP cb ≤ 2 ^ τ)
    (hSsig : cb.Ssig ≤ 2 ^ ℓ) (hLp : cb.Lp ≤ 2 ^ ℓ) (hLk : cb.Lk ≤ 2 ^ ℓ) (hLa : cb.La ≤ 2 ^ ℓ)
    (hLc : cb.Lc ≤ 2 ^ ℓ) (hW : W ≤ 2 ^ ℓ) (hnS : nS ≤ 2 ^ ℓ) (hcL : c.L ≤ 2 ^ ℓ)
    (hL : L ≤ 2 ^ ℓ) (hcLs : c.L ≤ 2 ^ lc)
    (hlr : lc + 30 ≤ r) (hsr : s + 30 ≤ r) (htr : t + 28 ≤ 2 ^ r)
    (hτt : τ + 5 ≤ t) (hℓt : 2 * ℓ + 21 ≤ t)
    (hk : p + R + 30 ≤ k') (hg : 4 * k' + r + 10 ≤ 2 ^ g) :
    compConst cs cb P L ≤ 2 ^ (r + g + 11 + 65 * k' / 41) + 2 ^ (t + 6) := by
  have hX : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hr30 : 2 ^ 30 * 2 ^ lc ≤ 2 ^ r := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs30 : 2 ^ 30 * 2 ^ s ≤ 2 ^ r := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr13 : 2 ^ 13 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the handler term
  have hZ : 27 * (1 + ∑ o, (9 + (compHandlers (c := c) cs W o).states)) *
      ((paramsWord PUniv params).length + 3) ≤ 2 ^ r := by
    rw [length_paramsWord_pu, Fin.sum_univ_three]
    have h0 := states_compHandlers_le (c := c) cs W s hsetup hpub hkey hauth hchal 0
    have h1 := states_compHandlers_le (c := c) cs W s hsetup hpub hkey hauth hchal 1
    have h2 := states_compHandlers_le (c := c) cs W s hsetup hpub hkey hauth hchal 2
    have hX' : 1 ≤ 2 ^ lc := Nat.one_le_two_pow
    clear hcL hL hW hnS hSsig hLp hLk hLa hLc
    generalize 2 ^ r = Z at *
    generalize 2 ^ lc = X at *
    generalize 2 ^ s = S at *
    omega
  -- the slope
  have hc := chainSlope_comp_le (c := c) cs cb L (2 ^ ℓ) hX hSsig hLp hLk hLa hLc hW hnS hcL hL
  have hXX : 2 ^ ℓ * 2 ^ ℓ * 2 ^ 21 ≤ 2 ^ t := by
    rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hτ : 2 ^ τ * 2 ^ 5 ≤ 2 ^ t := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold compConst
  refine redConstP_le_two_pow P (Post 0 0 nA 1) (compHandlers (c := c) cs W) _ _ _ L _ r t k' g
    hsP (by rw [states_post_date]; exact le_trans (by norm_num) hr13) hZ htP ?_ (by omega)
    (by rw [tapes_post_eq]; omega) hg
  refine hc.trans ?_
  generalize 2 ^ ℓ * 2 ^ ℓ = Y at *
  generalize 2 ^ t = Z at *
  generalize 2 ^ τ = U at *
  omega

end AdvancedEncryption.DualUse
