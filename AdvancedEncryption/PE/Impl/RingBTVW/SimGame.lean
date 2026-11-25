import PE.Impl.RingBTVW.SimKeyGame

/-!
# The experiment a reduction runs

A reduction draws its own secret `σ ← setupS x` for the selected attribute, gives the adversary
the public key and challenge of `view σ`, and answers key queries with the simulated trapdoor of
`sd σ` (`specSim`). When the data are valid on the support, the distinguisher rejecting runs whose
flag is up accepts with the same probability as in the hybrid of the view law
`x ↦ (setupS x).map view` (`accept_sim`): the two challengers differ only on authorized queries,
which raise the flag (`Generic.obs_until_bad`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]

/-- Acceptance at `true` only depends on the outcomes with the flag down. -/
theorem bind_true_eq {μ ν : PMF (List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool)}
    (h : ∀ o, o.2.2.2 = false → μ o = ν o)
    (f : List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool → PMF Bool)
    (hf : ∀ o, o.2.2.2 = true → f o true = 0) : (μ.bind f) true = (ν.bind f) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun o => ?_
  by_cases hb : o.2.2.2 = true
  · rw [hf o hb, mul_zero, mul_zero]
  · rw [h o (by simpa using hb)]

theorem DcB_bad (D : Machine) (o : List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool)
    (hb : o.2.2.2 = true) : DcB D o true = 0 := by
  simp [DcB, DcStar, hb]

variable {Sec : Type} (setupS : PUniv.Attr → PMF Sec) (view : Sec → PK hk c × CT hk c)
  (sd : Sec → SimData hk c)

/-- **The reduction's challenger.** -/
noncomputable def specSim : Generic.Spec PUniv Sec where
  setup := setupS
  pub σ := (pkEnc hk c).enc (view σ).1
  key σ := KGsim (sd σ)
  chal σ μ := PMF.pure ((ctEnc hk c).enc (shiftCT hk c μ (view σ).2))
  auth := authI hk c

/-- **The reduction runs the hybrid**, as far as the distinguisher rejecting runs whose flag is up
can tell. -/
theorem accept_sim (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : bpLen ≤ c.L) (hcov : SimCovered hk c)
    (hmpk : ∀ σ, (sd σ).mpk = (view σ).1)
    (hx : ∀ x, ∀ σ ∈ (setupS x).support, (sd σ).x = x)
    (hvalid : ∀ x, ∀ σ ∈ (setupS x).support, SimValid (sd σ)) (A : Machine 3) (D : Machine) :
    ((G A (fun x => (setupS x).map view)).bind (DcB D)) true =
      (((A.runWith (Generic.oracle (specSim setupS view sd)) (paramsWord PUniv params)
        {}).map Generic.obs).bind (DcB D)) true := by
  set prog := A.machine.runOracle A.time (paramsWord PUniv params)
  set spV := specV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c)
    (fun x => (setupS x).map view)
  have hcomap := Generic.runWith_comap spV view prog setupS (fun _ => rfl)
  have hG : G A (fun x => (setupS x).map view) =
      (ProbOracleComp.runWith (Generic.oracle (spV.comap view setupS)) prog {}).map Generic.obs := by
    show (ProbOracleComp.runWith (Generic.oracle spV) prog {}).map Generic.obs = _
    rw [← hcomap, PMF.map_comp]
    rfl
  rw [hG]
  unfold Machine.runWith
  refine bind_true_eq (fun o ho => ?_) (DcB D) (DcB_bad D)
  refine (Generic.obs_until_bad (spV.comap view setupS) (specSim setupS view sd) rfl rfl rfl rfl
    ?_ prog o ho).symm
  intro x σ hσ C hC
  show KGsim (sd σ) C = KGi hk c (view σ).1 C
  rw [← hmpk σ]
  exact KGsim_eq_KGi hdec hcov (sd σ) (hvalid x σ hσ) C (by rw [hx x σ hσ]; exact hC)

/-- **The acceptance of a Ring-LWE step is that of the reduction's experiment**, averaged over the
instance. -/
theorem accOn_sim {Inst : Type} (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : bpLen ≤ c.L) (hcov : SimCovered hk c) (A : Machine 3) (D : Machine)
    (inst : PMF Inst) (F : PUniv.Attr → Inst → PMF (PK hk c × CT hk c))
    (setupI : Inst → PUniv.Attr → PMF Sec) (viewI : Inst → Sec → PK hk c × CT hk c)
    (sdI : Inst → Sec → SimData hk c) (hF : ∀ x i, F x i = (setupI i x).map (viewI i))
    (hmpk : ∀ i σ, (sdI i σ).mpk = (viewI i σ).1)
    (hx : ∀ i x, ∀ σ ∈ (setupI i x).support, (sdI i σ).x = x)
    (hvalid : ∀ i x, ∀ σ ∈ (setupI i x).support, SimValid (sdI i σ)) :
    accOn A D inst F = ((inst.bind fun i =>
      ((A.runWith (Generic.oracle (specSim (setupI i) (viewI i) (sdI i)))
        (paramsWord PUniv params) {}).map Generic.obs).bind (DcB D)) true).toReal := by
  unfold accOn
  congr 1
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun i => ?_
  congr 1
  have hFi : (fun x => F x i) = fun x => (setupI i x).map (viewI i) := funext fun x => hF x i
  rw [hFi]
  exact accept_sim (setupI i) (viewI i) (sdI i) hdec hL hcov (hmpk i) (hx i) (hvalid i) A D

end AdvancedEncryption.RingBTVW
