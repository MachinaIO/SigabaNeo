import PE.Impl.DualUse.Prog.Post
import SigabaNeo.Lib.Machines.Inline.InitPerQuery

/-!
# The reduction machine with per-query handlers

`reductionP P Post A H E q₀ q₁ L D` is the reduction machine (`reduction`) whose inlined machine
serves handlers with per-query halting bounds (`HandlesP A H orc enc InvS q₀ q₁ L`: the handler of a
query `b` halts within `q₀ + q₁ |b|` steps): it is `reduction P Post A H E (q₀ + 3 q₁) L D`
(`Machine.run_inlineOracleInitP`).

* `acceptProb_reductionP`, `acceptProb_reductionP_accOn`: its acceptance, as for `reduction`;
* `cost_reductionP_le`, `cost_reductionP_post`: `cost ≤ redFactorP · cost A · cost D`, where
  `redFactorP` depends on the handlers only through their numbers of states, `q₀`, `q₁`, `L` and
  `E` — not on `A` (in particular not on `A.time`, which bounds the query lengths), nor on `D`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow AdvancedEncryption.PE.Generic
open SigabaNeo.Inline
open scoped ENNReal

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {m : ℕ} {σ : Type}

/-- **The reduction machine for per-query handlers**: the inlined machine has the clock of the
uniform bound `q₀ + 3 q₁`. -/
noncomputable def reductionP (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E q₀ q₁ L : ℕ) (D : Machine) : Machine :=
  reduction P Post A H E (q₀ + q₁ * 3) L D

/-- **Acceptance of the reduction machine for per-query handlers.** -/
theorem acceptProb_reductionP {Sec Inst : Type} (P Post : Machine) (A : Machine 3)
    (H : Fin 3 → Routine (m + 3)) (orc : Fin 3 × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E q₀ q₁ L : ℕ)
    (hH : HandlesP A H orc enc InvS q₀ q₁ L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (obsOf : List Bool → σ → Ob) (D : Machine) (μ : PMF (List Bool)) (s₀ : List Bool → σ)
    (hs₀ : ∀ w ∈ μ.support, InvS (s₀ w))
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (enc (s₀ w)))
    (hPost : ∀ o s, o.length ≤ A.time → InvS s →
      Post.run (pairOut o (enc s)) = PMF.pure (postW (obsOf o s)))
    (inst : List Bool → Inst) (setupI : Inst → Date → PMF Sec)
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c)
    (hgame : ∀ w ∈ μ.support,
      (A.runWith orc (paramsWord dateUniverse params) (s₀ w)).map (fun r => obsOf r.1 r.2) =
        (A.runWith (Generic.oracle (specSim (setupI (inst w)) (viewI (inst w)) (sdI (inst w))))
          (paramsWord dateUniverse params) {}).map Generic.obs) :
    (reductionP P Post A H E q₀ q₁ L D).acceptProb μ =
      (((μ.map inst).bind fun i =>
        ((A.runWith (Generic.oracle (specSim (setupI i) (viewI i) (sdI i)))
          (paramsWord dateUniverse params) {}).map Generic.obs).bind (DcB D)) true).toReal := by
  unfold reductionP reduction
  rw [Machine.acceptProb_andThenLin_andThenGuard]
  congr 1
  rw [PMF.bind_bind, PMF.bind_bind, PMF.bind_map, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ μ.support
  · congr 1
    rw [hP w hw, PMF.pure_bind, Machine.run_andThenLin,
      Machine.run_inlineOracleInitP A H _ orc enc InvS E q₀ q₁ L hH hE (s₀ w) (hs₀ w hw) _ rfl,
      PMF.bind_map, PMF.bind_bind]
    have h1 : ((A.runWith orc (paramsWord dateUniverse params) (s₀ w)).bind
        fun r => (Post.run (pairOut r.1 (enc r.2))).bind D.guardK) =
        (((A.runWith orc (paramsWord dateUniverse params) (s₀ w)).map
          (fun r => obsOf r.1 r.2))).bind (fun ob => D.guardK (postW ob)) := by
      rw [PMF.bind_map]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ (fun r hr => ?_)
      obtain ⟨hlen, hinv⟩ := A.runWith_support_inv orc InvS
        (fun o b s hb hs r hr => (hH.inv o b s hb hs r hr).1) _ (s₀ w) (hs₀ w hw) r hr
      simp only [Function.comp_apply, hPost r.1 r.2 hlen hinv, PMF.pure_bind]
    rw [Function.comp_def] at *
    rw [h1, hgame w hw, PMF.bind_apply, Function.comp_apply, PMF.bind_apply]
    refine tsum_congr fun ob => ?_
    rw [guardK_postW]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hw, zero_mul, zero_mul]

/-- **The reduction for per-query handlers accepts with `accOn`.** -/
theorem acceptProb_reductionP_accOn {Sec Inst : Type} (P Post : Machine) (A : Machine 3)
    (H : Fin 3 → Routine (m + 3)) (orc : Fin 3 × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E q₀ q₁ L : ℕ)
    (hH : HandlesP A H orc enc InvS q₀ q₁ L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (obsOf : List Bool → σ → Ob) (D : Machine) (μ : PMF (List Bool)) (s₀ : List Bool → σ)
    (hs₀ : ∀ w ∈ μ.support, InvS (s₀ w))
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (enc (s₀ w)))
    (hPost : ∀ o s, o.length ≤ A.time → InvS s →
      Post.run (pairOut o (enc s)) = PMF.pure (postW (obsOf o s)))
    (inst : List Bool → Inst) (instLaw : PMF Inst) (hinst : μ.map inst = instLaw)
    (F : Date → Inst → PMF (PK hk c × CT hk c))
    (setupI : Inst → Date → PMF Sec)
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c)
    (hgame : ∀ w ∈ μ.support,
      (A.runWith orc (paramsWord dateUniverse params) (s₀ w)).map (fun r => obsOf r.1 r.2) =
        (A.runWith (Generic.oracle (specSim (setupI (inst w)) (viewI (inst w)) (sdI (inst w))))
          (paramsWord dateUniverse params) {}).map Generic.obs)
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c)
    (hF : ∀ x i, F x i = (setupI i x).map (viewI i))
    (hmpk : ∀ i σ, (sdI i σ).mpk = (viewI i σ).1)
    (hx : ∀ i x, ∀ σ ∈ (setupI i x).support, (sdI i σ).x = x)
    (hvalid : ∀ i x, ∀ σ ∈ (setupI i x).support, SimValid (sdI i σ)) :
    (reductionP P Post A H E q₀ q₁ L D).acceptProb μ = accOn A D instLaw F := by
  rw [acceptProb_reductionP P Post A H orc enc InvS E q₀ q₁ L hH hE obsOf D μ s₀ hs₀ hP hPost inst
    setupI viewI sdI hgame, hinst,
    accOn_sim hdec hL hcov A D instLaw F setupI viewI sdI hF hmpk hx hvalid]

/-- The constant of the cost of the reduction for per-query handlers. -/
noncomputable def redFactorP (P Post : Machine) (H : Fin 3 → Routine (m + 3)) (E q₀ q₁ L pt : ℕ) :
    ℕ :=
  redFactor P Post H E (q₀ + q₁ * 3) L pt

/-- **Cost of the reduction for per-query handlers**: at most a constant (independent of `A` and
`D`) times `cost A · cost D`, when the post-processing takes time at most `pt · cost A`. -/
theorem cost_reductionP_le (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E q₀ q₁ L pt : ℕ) (D : Machine) (hPostT : Post.time ≤ pt * A.cost) :
    (reductionP P Post A H E q₀ q₁ L D).cost ≤
      redFactorP P Post H E q₀ q₁ L pt * A.cost * D.cost :=
  cost_reduction_le P Post A H E _ L pt D hPostT

/-- **Cost of the reduction for per-query handlers with the post-processing `Post`**: the factor
depends neither on `A` nor on `D`. -/
theorem cost_reductionP_post (P : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E q₀ q₁ L : ℕ) (D : Machine) :
    (reductionP P (Post A.time E 10 1) A H E q₀ q₁ L D).cost ≤
      redFactorP P (Post 0 E 10 1) H E q₀ q₁ L (postA E 10 1 + postB E 10 1) * A.cost * D.cost :=
  cost_reduction_post P A H E _ L D

end AdvancedEncryption.DualUse
