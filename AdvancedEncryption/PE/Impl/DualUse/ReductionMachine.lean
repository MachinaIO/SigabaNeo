import PE.Impl.DualUse.SimGame
import PE.Impl.DualUse.AHAssembly
import SigabaNeo.Lib.Machines.Inline.InitCost
import SigabaNeo.Lib.Machines.Compose.GuardCost

/-!
# The reduction machine, from its parts

A reduction for a Ring-LWE step is the machine

`P.andThenLin ((A.inlineOracleInit H w₀ E Q L).andThenLin Post).andThenGuard D`:

* `P` turns the instance word into the encoded initial state of the reduction's challenger;
* the inlined machine runs the adversary `A` on the parameter word `w₀` against the handlers `H`
  of an oracle `orc` on states `σ`, and outputs `A`'s output paired with the final state;
* `Post` turns this into `[false]` when the flag of the final state is up, and into
  `true :: viewObs o` otherwise;
* the guard runs the distinguisher `D` on `viewObs o` only after `true`.

If the oracle `orc` started from the state of the instance `i w` has the observations of the
reduction's challenger `specSim` for `i w` (`hgame`), the machine accepts with the probability of
the experiment-as-distinguisher (`acceptProb_reduction`), hence with `accOn` (`acceptProb_reduction_accOn`),
and it costs at most a constant times `cost A · cost D` (`cost_reduction_le`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open SigabaNeo.Inline
open scoped ENNReal

/-- The observations of a run. -/
abbrev Ob := List Bool × Option dateUniverse.Attr × Option dateUniverse.Msg × Bool

/-- The word `Post` writes for an observation. -/
def postW (ob : Ob) : List Bool := if ob.2.2.2 then [false] else true :: viewObs ob

theorem guardK_postW (D : Machine) (ob : Ob) :
    (D.guardK (postW ob)) [true] = DcB D ob true := by
  unfold postW DcB DcStar Dc
  rcases hb : ob.2.2.2
  · simp only [Bool.false_eq_true, if_false, Machine.guardK_true]
    rw [PMF.map_apply, tsum_eq_single [true]]
    · simp
    · intro b hb; simp [hb]
  · simp

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {m : ℕ} {σ : Type}

/-- **The reduction machine.** -/
noncomputable def reduction (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E Q L : ℕ) (D : Machine) : Machine :=
  P.andThenLin (((A.inlineOracleInit H (paramsWord dateUniverse params) E Q L).andThenLin Post).andThenGuard D)

/-- **Acceptance of the reduction machine.** -/
theorem acceptProb_reduction {Sec Inst : Type} (P Post : Machine) (A : Machine 3)
    (H : Fin 3 → Routine (m + 3)) (orc : Fin 3 × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E Q L : ℕ)
    (hH : Handles A H orc enc InvS Q L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (obsOf : List Bool → σ → Ob) (D : Machine) (μ : PMF (List Bool)) (s₀ : List Bool → σ)
    (hs₀ : ∀ w ∈ μ.support, InvS (s₀ w))
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (enc (s₀ w)))
    (hPost : ∀ o s, Post.run (pairOut o (enc s)) = PMF.pure (postW (obsOf o s)))
    (inst : List Bool → Inst) (setupI : Inst → Date → PMF Sec)
    (viewI : Inst → Sec → PK hk c × CT hk c) (sdI : Inst → Sec → SimData hk c)
    (hgame : ∀ w ∈ μ.support,
      (A.runWith orc (paramsWord dateUniverse params) (s₀ w)).map (fun r => obsOf r.1 r.2) =
        (A.runWith (Generic.oracle (specSim (setupI (inst w)) (viewI (inst w)) (sdI (inst w))))
          (paramsWord dateUniverse params) {}).map Generic.obs) :
    (reduction P Post A H E Q L D).acceptProb μ =
      (((μ.map inst).bind fun i =>
        ((A.runWith (Generic.oracle (specSim (setupI i) (viewI i) (sdI i)))
          (paramsWord dateUniverse params) {}).map Generic.obs).bind (DcB D)) true).toReal := by
  unfold reduction
  rw [Machine.acceptProb_andThenLin_andThenGuard]
  congr 1
  rw [PMF.bind_bind, PMF.bind_bind, PMF.bind_map, PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ μ.support
  · congr 1
    rw [hP w hw, PMF.pure_bind, Machine.run_andThenLin,
      Machine.run_inlineOracleInit A H _ orc enc InvS E Q L hH hE (s₀ w) (hs₀ w hw) _ rfl,
      PMF.bind_map, PMF.bind_bind]
    have h1 : ((A.runWith orc (paramsWord dateUniverse params) (s₀ w)).bind
        fun r => (Post.run (pairOut r.1 (enc r.2))).bind D.guardK) =
        (((A.runWith orc (paramsWord dateUniverse params) (s₀ w)).map
          (fun r => obsOf r.1 r.2))).bind (fun ob => D.guardK (postW ob)) := by
      rw [PMF.bind_map]
      congr 1
      funext r
      simp only [Function.comp_apply, hPost, PMF.pure_bind]
    rw [Function.comp_def] at *
    rw [h1, hgame w hw, PMF.bind_apply, Function.comp_apply, PMF.bind_apply]
    refine tsum_congr fun ob => ?_
    rw [guardK_postW]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hw, zero_mul, zero_mul]

/-- **The reduction accepts with `accOn`**: on instance words whose decoding has the law of the
instances, given the hypotheses of `accOn_sim` on the challenger's data. -/
theorem acceptProb_reduction_accOn {Sec Inst : Type} (P Post : Machine) (A : Machine 3)
    (H : Fin 3 → Routine (m + 3)) (orc : Fin 3 × List Bool → StateT σ PMF (List Bool))
    (enc : σ → List Bool) (InvS : σ → Prop) (E Q L : ℕ)
    (hH : Handles A H orc enc InvS Q L) (hE : ∀ s, InvS s → (enc s).length ≤ E)
    (obsOf : List Bool → σ → Ob) (D : Machine) (μ : PMF (List Bool)) (s₀ : List Bool → σ)
    (hs₀ : ∀ w ∈ μ.support, InvS (s₀ w))
    (hP : ∀ w ∈ μ.support, P.run w = PMF.pure (enc (s₀ w)))
    (hPost : ∀ o s, Post.run (pairOut o (enc s)) = PMF.pure (postW (obsOf o s)))
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
    (reduction P Post A H E Q L D).acceptProb μ = accOn A D instLaw F := by
  rw [acceptProb_reduction P Post A H orc enc InvS E Q L hH hE obsOf D μ s₀ hs₀ hP hPost inst
    setupI viewI sdI hgame, hinst,
    accOn_sim hdec hL hcov A D instLaw F setupI viewI sdI hF hmpk hx hvalid]

/-- The constant of the reduction's cost, for a post-processing machine `Post` of description
length `Post.descLen` and time at most `pt · cost A` (it reads `A`'s output). -/
noncomputable def redFactor (P Post : Machine) (H : Fin 3 → Routine (m + 3)) (E Q L pt : ℕ) : ℕ :=
  P.andThenLinFactor * 650000 *
    (initFactor H Q L (paramsWord dateUniverse params).length E * (11 + 498960 * Post.descLen) +
      pt + 10)

/-- **Cost of the reduction**: at most a constant (independent of `A` and `D`) times
`cost A · cost D`, when the post-processing takes time at most `pt · cost A`. -/
theorem cost_reduction_le (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E Q L pt : ℕ) (D : Machine) (hPostT : Post.time ≤ pt * A.cost) :
    (reduction P Post A H E Q L D).cost ≤ redFactor P Post H E Q L pt * A.cost * D.cost := by
  unfold reduction redFactor
  set Inl := A.inlineOracleInit H (paramsWord dateUniverse params) E Q L
  have h1 := Machine.cost_andThenLin_andThenGuard_le P (Inl.andThenLin Post) D
  have ht := Machine.time_andThenLin_le Inl Post
  have hd := Machine.descLen_andThenLin_le Inl Post
  have h3 := A.cost_inlineOracleInit_le H (paramsWord dateUniverse params) E Q L
  have hA := A.one_le_cost
  have hIt : Inl.time ≤ Inl.cost := by unfold Machine.cost; omega
  have hM : (Inl.andThenLin Post).cost ≤
      (initFactor H Q L (paramsWord dateUniverse params).length E * (11 + 498960 * Post.descLen) +
        pt + 10) * A.cost := by
    have e : (Inl.andThenLin Post).cost = (Inl.andThenLin Post).time + (Inl.andThenLin Post).descLen :=
      rfl
    rw [e]
    have h4 : 498960 * Inl.cost * Post.descLen ≤
        498960 * Post.descLen * (initFactor H Q L (paramsWord dateUniverse params).length E * A.cost) := by
      calc 498960 * Inl.cost * Post.descLen = 498960 * Post.descLen * Inl.cost := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h3
    have h5 : 11 * Inl.time ≤ 11 * (initFactor H Q L (paramsWord dateUniverse params).length E * A.cost) :=
      Nat.mul_le_mul_left _ (hIt.trans h3)
    nlinarith
  calc _ ≤ _ := h1
    _ ≤ P.andThenLinFactor * 650000 *
          ((initFactor H Q L (paramsWord dateUniverse params).length E * (11 + 498960 * Post.descLen) +
            pt + 10) * A.cost) * D.cost := by gcongr
    _ = _ := by ring

/-- **Cost of the reduction, quadratic form.** -/
theorem cost_reduction_le_sq (P Post : Machine) (A : Machine 3) (H : Fin 3 → Routine (m + 3))
    (E Q L pt : ℕ) (D : Machine) (hPostT : Post.time ≤ pt * A.cost) :
    ((reduction P Post A H E Q L D).cost : ℝ) ≤
      (redFactor P Post H E Q L pt : ℝ) * ((A.cost + D.cost : ℕ) : ℝ) ^ 2 := by
  have h := cost_reduction_le P Post A H E Q L pt D hPostT
  have h' : ((reduction P Post A H E Q L D).cost : ℝ) ≤
      (redFactor P Post H E Q L pt : ℝ) * (A.cost : ℝ) * (D.cost : ℝ) := by exact_mod_cast h
  refine h'.trans ?_
  push_cast
  have : (A.cost : ℝ) * D.cost ≤ ((A.cost : ℝ) + D.cost) ^ 2 := by
    nlinarith [sq_nonneg ((A.cost : ℝ)), sq_nonneg ((D.cost : ℝ)),
      (Nat.cast_nonneg A.cost : (0 : ℝ) ≤ A.cost), (Nat.cast_nonneg D.cost : (0 : ℝ) ≤ D.cost)]
  have h0 : (0 : ℝ) ≤ redFactor P Post H E Q L pt := Nat.cast_nonneg _
  calc (redFactor P Post H E Q L pt : ℝ) * A.cost * D.cost
      = (redFactor P Post H E Q L pt : ℝ) * (A.cost * D.cost) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this h0

end AdvancedEncryption.DualUse
