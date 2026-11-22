import PE.Impl.DualUse.ReductionPerQuery
import PE.Impl.DualUse.ReductionOracle
import PE.Impl.Game.HandlersPCost
import PE.Impl.Game.HandlersDate

/-!
# A reduction from component programs

For a step of the hybrid chain whose challenger is `specSim (setupI i) (viewI i) (sdI i)` on the
instance `i`, the component programs `cs : Comps R (dateCodes sig) (spPack st viewI sdI)
(setupPack inst setupI) IW Ok` (with length bounds `cb`) and a decoder `P` turning the instance
words of the decision problem into admissible state words give a reduction (`Reduces`):

* the machine is `reductionP P (Post A.time E 10 1) A (handlersP …) E q₀ q₁ L D`;
* it accepts the real and the uniform words with `accOn A D Ir F` and `accOn A D Iu F`
  (`acceptProb_reductionP_accOn`, `handlesP`, `hgame_oracleW`, `hPost_post`);
* its cost is at most `redConstP … · cost A · cost D ≤ C · (cost A + cost D)²`
  (`cost_reductionP_post_struct`).

The constant `redConstP` depends on the components only (through the handlers' states, the
per-query clock and the bounds), not on `A` nor `D`.
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

/-- The handlers of the components, with the cut `c.L` of the key queries. -/
noncomputable def compHandlers {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) (W : ℕ) :
    Fin 3 → Routine (R + 5 + 3) :=
  handlersP (dateCodes sig) cs c.L [] W

/-- The reduction machine of the components. -/
noncomputable def compReduction {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (A : Machine 3) (D : Machine) : Machine :=
  reductionP P (Post A.time (stateBound (dateCodes sig) W) 10 1) A (compHandlers (c := c) cs W)
    (stateBound (dateCodes sig) W) (handlerQ0 cb []) (handlerQ1 (dateCodes sig) c.L []) L D

/-- The constant of the cost of the reduction of the components. -/
noncomputable def compConst {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) : ℕ :=
  redConstP P (Post 0 0 10 1) (compHandlers (c := c) cs W) (stateBound (dateCodes sig) W)
    (handlerQ0 cb []) (handlerQ1 (dateCodes sig) c.L []) L
    (postA (stateBound (dateCodes sig) W) 10 1 + postB (stateBound (dateCodes sig) W) 10 1)

/-- **Acceptance of the reduction of the components**: on a law `μ` of words that the decoder
maps to admissible state words `dw w` whose instances have the law `instLaw`, it accepts with
`accOn A D instLaw F`. -/
theorem acceptProb_compReduction {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → ((spPack st viewI sdI).pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L → ∀ sk ∈ ((spPack st viewI sdI).key σ C).support,
      sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st viewI sdI).chal σ μ).support, ct.length ≤ L)
    (A : Machine 3) (D : Machine) (μ : PMF (List Bool)) (dw : List Bool → List Bool)
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (dw w))
    (hIW : ∀ w ∈ μ.support, IW (dw w) ∧ (dw w).length ≤ W ∧ (dw w).head? ≠ some false)
    (instLaw : PMF Inst) (hinst : μ.map (inst ∘ dw) = instLaw)
    (F : Date → Inst → PMF (PK hk c × CT hk c))
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (hF : ∀ x i, F x i = (setupI i x).map (viewI i))
    (hmpk : ∀ i σ, (sdI i σ).mpk = (viewI i σ).1)
    (hx : ∀ i x, ∀ σ ∈ (setupI i x).support, (sdI i σ).x = x)
    (hvalid : ∀ i x, ∀ σ ∈ (setupI i x).support, SimValid (sdI i σ)) :
    (compReduction cs cb P L A D).acceptProb μ = accOn A D instLaw F := by
  have hH := handlesP cs c.L [] (longKeys_spPack st viewI sdI Ok) cb A L hpubL
    hkeyL (by simp) hchalL
  have hE : ∀ s, InvS IW W Ok s → ((dateCodes sig).encState s).length ≤
      stateBound (dateCodes sig) W := fun s h => length_encState_le h
  unfold compReduction compHandlers
  refine acceptProb_reductionP_accOn P _ A _ _ _ _ _ _ _ L hH hE
    (fun o s => Generic.obs (o, s.2)) D μ (fun w => (dw w, {}))
    (fun w hw => ⟨(hIW w hw).1, (hIW w hw).2.1, (hIW w hw).2.2, Or.inl rfl⟩)
    (fun w hw => by rw [hP w hw]; rfl)
    (hPost_post sig IW W Ok A.time _ hE)
    (inst ∘ dw) instLaw hinst F setupI viewI sdI
    (fun w _ => hgame_oracleW st inst setupI viewI sdI _ (dw w))
    hdec hL hcov hF hmpk hx hvalid

/-- **Cost of the reduction of the components.** -/
theorem cost_compReduction {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ) (A : Machine 3) (D : Machine) :
    ((compReduction cs cb P L A D).cost : ℝ) ≤
      (compConst cs cb P L : ℝ) * ((A.cost + D.cost : ℕ) : ℝ) ^ 2 := by
  have h := cost_reductionP_post_struct P A (compHandlers (c := c) cs W)
    (stateBound (dateCodes sig) W) (handlerQ0 cb []) (handlerQ1 (dateCodes sig) c.L []) L D
  have h' : (compReduction cs cb P L A D).cost ≤ compConst cs cb P L * (A.cost * D.cost) := by
    rw [← mul_assoc]; exact h
  have hq : A.cost * D.cost ≤ (A.cost + D.cost) ^ 2 := by nlinarith
  have := h'.trans (Nat.mul_le_mul_left _ hq)
  exact_mod_cast this

/-- **A reduction from components**: one machine accepting the real and the uniform words with
`accOn A D Ir F` and `accOn A D Iu F`, at cost at most `C · (cost A + cost D)²` for any
`C ≥ compConst`. -/
theorem reduces_of_comps {R : ℕ} {sig : FixedEnc (Inst × Sec) nS}
    {st : dateUniverse.Attr → PMF (Inst × Sec)} {viewI : Inst → Sec → PK hk c × CT hk c}
    {sdI : Inst → Sec → SimData hk c} {inst : List Bool → Inst} {setupI : Inst → Date → PMF Sec}
    {IW : List Bool → Prop} {Ok : Inst × Sec → Prop}
    (cs : Comps R (dateCodes sig) (spPack st viewI sdI) (setupPack inst setupI) IW Ok) {W : ℕ}
    (cb : CompBoundsP cs c.L W) (P : Machine) (L : ℕ)
    (hpubL : ∀ σ, Ok σ → ((spPack st viewI sdI).pub σ).length ≤ L)
    (hkeyL : ∀ σ C, Ok σ → C.length ≤ c.L → ∀ sk ∈ ((spPack st viewI sdI).key σ C).support,
      sk.length ≤ L)
    (hchalL : ∀ σ μ, Ok σ → ∀ ct ∈ ((spPack st viewI sdI).chal σ μ).support, ct.length ≤ L)
    (dw : List Bool → List Bool)
    (μr μu : PMF (List Bool)) (Ir Iu : PMF Inst)
    (hPr : ∀ w ∈ μr.support, P.run w = PMF.pure (dw w))
    (hPu : ∀ w ∈ μu.support, P.run w = PMF.pure (dw w))
    (hIWr : ∀ w ∈ μr.support, IW (dw w) ∧ (dw w).length ≤ W ∧ (dw w).head? ≠ some false)
    (hIWu : ∀ w ∈ μu.support, IW (dw w) ∧ (dw w).length ≤ W ∧ (dw w).head? ≠ some false)
    (hir : μr.map (inst ∘ dw) = Ir) (hiu : μu.map (inst ∘ dw) = Iu)
    (F : Date → Inst → PMF (PK hk c × CT hk c))
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (hF : ∀ x i, F x i = (setupI i x).map (viewI i))
    (hmpk : ∀ i σ, (sdI i σ).mpk = (viewI i σ).1)
    (hx : ∀ i x, ∀ σ ∈ (setupI i x).support, (sdI i σ).x = x)
    (hvalid : ∀ i x, ∀ σ ∈ (setupI i x).support, SimValid (sdI i σ))
    (C : ℝ) (hC : (compConst cs cb P L : ℝ) ≤ C) (A : Machine 3) (D : Machine) :
    Reduces (accOn A D Ir F) (accOn A D Iu F) μr μu C (A.cost + D.cost) := by
  refine ⟨compReduction cs cb P L A D,
    acceptProb_compReduction cs cb P L hpubL hkeyL hchalL A D μr dw hPr hIWr Ir hir F hdec hL hcov
      hF hmpk hx hvalid,
    acceptProb_compReduction cs cb P L hpubL hkeyL hchalL A D μu dw hPu hIWu Iu hiu F hdec hL hcov
      hF hmpk hx hvalid, ?_⟩
  refine (cost_compReduction cs cb P L A D).trans ?_
  exact mul_le_mul_of_nonneg_right hC (by positivity)

end AdvancedEncryption.DualUse
