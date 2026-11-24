import PE.Impl.ExpLUT.AH.RedGame
import PE.Impl.Game.Assembly
import SigabaNeo.Lib.Crypto.QuadLoss
import SigabaNeo.Lib.Lattices.CircularRingLWE

/-!
# Attribute hiding of the implementation from circular Ring-LWE (package G, assembly)

For an implementation meeting the specifications (`ImplSpec`), a simulator meeting `SimSpec`, the
boxes covering the real trapdoor and `T_sim` (`RealCovW`, `SimCovW`) and the flooding step within
`ε_fl` (`hflood`):

* `advantage_le`: for every admissible adversary `A` and distinguisher `Dm`, the advantage
  `|Pr[Dm accepts real] − Pr[Dm accepts ideal]|` is at most the statistical terms `statW ε_fl`
  (the near-uniform public matrices on both sides, H1, H2, H3′, H5, H6) plus `|r − u|`, where
  `r`, `u` are the probabilities that the reduction's experiment (`redGame`: keys from `T_sim`),
  followed by `Dm` rejecting the runs whose flag is up (`DcB`), accepts on a real and on a uniform
  circular instance (`rAcc`, `uAcc`);
* `attributeHiding_of_reduction`: **`AttributeHiding (univ w8) params impl`** from
  `CircularRingLWE.decision.HardAt p kb`, given a **reduction machine** `R` for every admissible
  `A` and `Dm` with `R.acceptProb (realLaw p) = rAcc`, `R.acceptProb (idealLaw p) = uAcc` and
  `cost R ≤ C (cost A + cost Dm)²` (`RedMachine`), `64 · (2^128)² · C ≤ 2^kb` and
  `4 · 2^128 · statW² ≤ 1` (`SimSpec`'s simulator is the one of the definition).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open scoped ENNReal

/-! ### The distinguisher on observable runs -/

/-- The input of the distinguisher from the observable part of a run. -/
def viewObs8 (o : List Bool × Option (univ w8).Attr × Option (univ w8).Msg × Bool) : List Bool :=
  encodeTuple [encOpt (univ w8).encAttr o.2.1, encOpt (univ w8).encMsg o.2.2.1, o.1]

/-- The distinguisher rejecting the runs whose flag is up, as a bit. -/
noncomputable def DcB (Dm : Machine) (o : List Bool × Option (univ w8).Attr × Option (univ w8).Msg × Bool) :
    PMF Bool :=
  if o.2.2.2 then PMF.pure false else (Dm.run (viewObs8 o)).map fun w => decide (w = [true])

theorem DcB_bad (Dm : Machine) (o : List Bool × Option (univ w8).Attr × Option (univ w8).Msg × Bool)
    (hb : o.2.2.2 = true) : DcB Dm o true = 0 := by
  simp [DcB, hb]

/-- With the flag down on the support, acceptance of `Dm` is acceptance of `DcB Dm`. -/
theorem bind_run_eq_DcB (Dm : Machine) (μ : PMF (List Bool × Option (univ w8).Attr × Option (univ w8).Msg × Bool))
    (h : ∀ o ∈ μ.support, o.2.2.2 = false) :
    (μ.bind fun o => Dm.run (viewObs8 o)) [true] = (μ.bind (DcB Dm)) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun o => ?_
  by_cases ho : o ∈ μ.support
  · congr 1
    simp only [DcB, h o ho, Bool.false_eq_true, if_false, PMF.map_apply]
    rw [tsum_eq_single [true]]
    · simp
    · intro w hw; simp [hw]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- Closeness bounds the difference of the probabilities of an outcome. -/
theorem abs_sub_le_of_closeTo' {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε)
    (hε : ε ≠ ⊤) (a : α) : |(μ a).toReal - (ν a).toReal| ≤ ε.toReal := by
  have h1 := h {a}
  have h2 := h.symm {a}
  simp only [PMF.toOuterMeasure_apply_singleton] at h1 h2
  have hμ : μ a ≠ ⊤ := PMF.apply_ne_top μ a
  have hν : ν a ≠ ⊤ := PMF.apply_ne_top ν a
  rw [abs_le]
  constructor
  · have := (ENNReal.toReal_le_toReal hν (ENNReal.add_ne_top.mpr ⟨hμ, hε⟩)).mpr h2
    rw [ENNReal.toReal_add hμ hε] at this
    linarith
  · have := (ENNReal.toReal_le_toReal hμ (ENNReal.add_ne_top.mpr ⟨hν, hε⟩)).mpr h1
    rw [ENNReal.toReal_add hν hε] at this
    linarith

variable (D : Dims) (kb : KeyBoxes D) (L : ℕ)

/-! ### The statistical terms and the reduction's acceptance -/

/-- **The statistical terms**: the machines' public matrices (real side), H1, H2 (flooding), H3′,
H5, H6, and the machines' public matrices and the simulator's ciphertext (ideal side). -/
noncomputable def statW (εfl : ℝ≥0∞) : ℝ≥0∞ :=
  Fintype.card (Attribute w8) * epsSetup D +
  (Fintype.card (Attribute w8) * delta1 (setting D) (Wb D) Pos +
    Fintype.card (Attribute w8) * εfl + Fintype.card (Attribute w8) * deltaT (setting D) (Wb D) +
    Fintype.card (Attribute w8) * delta5 (setting D) (Wb D) Pos +
    Fintype.card (Attribute w8) * deltaT (setting D) (Wb D)) +
  Fintype.card (Attribute w8) * (epsSetup D + epsCT D)

/-- The circular instances: real. -/
noncomputable abbrev circR (χs χ : PMF (Rg D)) : PMF (CInst D) :=
  circReal (setting D) (Wb D) (Jh D) (helperMap D) χs χ

/-- The circular instances: uniform. -/
noncomputable abbrev circU : PMF (CInst D) := circUnif (setting D) (Wb D) (Jh D)

/-- **The acceptance of the reduction's experiment on real instances.** -/
noncomputable def rAcc (impl : Impl sig) (χs χ χfl : PMF (Rg D)) (A : Machine 3) (Dm : Machine) : ℝ :=
  (((circR D χs χ).bind fun i => (redGame D kb L impl χfl A i).bind (DcB Dm)) true).toReal

/-- **The acceptance of the reduction's experiment on uniform instances.** -/
noncomputable def uAcc (impl : Impl sig) (χfl : PMF (Rg D)) (A : Machine 3) (Dm : Machine) : ℝ :=
  (((circU D).bind fun i => (redGame D kb L impl χfl A i).bind (DcB Dm)) true).toReal

variable {D kb L}

/-- The real experiment as seen by the distinguisher. -/
theorem real_accept [Nonempty (Wb D)] {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcov : RealCovW D kb) (A : Machine 3) (Dm : Machine)
    (hadm : ∀ r ∈ (PE.real (univ w8) params impl A).support, r.2.bad = false) :
    Dm.acceptProb ((PE.real (univ w8) params impl A).map view) =
      (((GV D kb L impl A (realVW D χs χ χfl)).bind (DcB Dm)) true).toReal := by
  have e := real_eq_gameV hI hcov A
  unfold Machine.acceptProb
  congr 1
  rw [← e, ← bind_run_eq_DcB Dm]
  · rw [PMF.bind_map, PMF.bind_map]; rfl
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    exact hadm r hr

/-- The ideal experiment as seen by the distinguisher. -/
theorem ideal_accept {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcov : RealCovW D kb) {Sim : Machine}
    (hSim : SimSpec D Sim) (A : Machine 3) (Dm : Machine)
    (hadm : ∀ r ∈ (PE.ideal (univ w8) params impl Sim A).support, r.2.bad = false) :
    Dm.acceptProb ((PE.ideal (univ w8) params impl Sim A).map view) =
      (((GV0 D kb L impl A (idealVW D)).bind (DcB Dm)) true).toReal := by
  have e := ideal_eq_gameV0 hI hcov hSim A
  unfold Machine.acceptProb
  congr 1
  rw [← e, ← bind_run_eq_DcB Dm]
  · rw [PMF.bind_map, PMF.bind_map]; rfl
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    exact hadm r hr

/-- **The advantage of any distinguisher against an admissible adversary.** -/
theorem advantage_le [Nonempty (Wb D)] {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcovR : RealCovW D kb) (hcovS : SimCovW D kb)
    (hb : 22 ≤ D.b) {Sim : Machine} (hSim : SimSpec D Sim) {εfl : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χ (BCol (Wb D) (setting D).τ)).support,
      ∀ zr : PrI (setting D) Pos → Wb D → Bool,
        CloseTo ((floodLaw (setting D) Pos χfl).map (· + floodShift eb zr))
          (floodLaw (setting D) Pos χfl) εfl)
    (hS : statW D εfl ≠ ⊤) (A : Machine 3) (Dm : Machine)
    (hadm : Admissible (univ w8) params impl Sim A) :
    |Dm.acceptProb ((PE.real (univ w8) params impl A).map view) -
        Dm.acceptProb ((PE.ideal (univ w8) params impl Sim A).map view)| ≤
      (statW D εfl).toReal + |rAcc D kb L impl χs χ χfl A Dm - uAcc D kb L impl χfl A Dm| := by
  rw [real_accept hI hcovR A Dm hadm.1, ideal_accept hI hcovR hSim A Dm hadm.2]
  -- real side: the machines' public matrices
  have g0 : CloseTo ((GV D kb L impl A (realVW D χs χ χfl)).bind (DcB Dm))
      ((GV D kb L impl A fun x =>
        hyb0 (Wb := Wb D) (helperMap D) wSt (half D) χs χ χfl (attrN x)).bind (DcB Dm))
      (Fintype.card (Attribute w8) * epsSetup D) :=
    (gameV_close (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L)
      (authW impl) _ fun x => realVW_close χs χ χfl x).bind_left (DcB Dm)
  -- the reduction's step
  have hr : ∀ inst : CInst D,
      ((GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind (DcB Dm)) true =
        ((redGame D kb L impl χfl A inst).bind (DcB Dm)) true :=
    fun inst => accept_red hI.eval hb hcovS χfl A inst (DcB Dm) (DcB_bad Dm)
  have h4 := Generic.closeTo_bool
    ((circR D χs χ).bind fun inst =>
      (GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind (DcB Dm))
    ((circU D).bind fun inst =>
      (GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind (DcB Dm))
  have er : ((circR D χs χ).bind fun inst =>
      (GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind (DcB Dm)) true =
      ((circR D χs χ).bind fun i => (redGame D kb L impl χfl A i).bind (DcB Dm)) true := by
    rw [PMF.bind_apply, PMF.bind_apply]; exact tsum_congr fun i => by rw [hr i]
  have eu : ((circU D).bind fun inst =>
      (GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind (DcB Dm)) true =
      ((circU D).bind fun i => (redGame D kb L impl χfl A i).bind (DcB Dm)) true := by
    rw [PMF.bind_apply, PMF.bind_apply]; exact tsum_congr fun i => by rw [hr i]
  rw [er, eu] at h4
  have hc := chain (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L)
    (authW impl) (helperMap D) wSt χs χ χfl (fun x => attrN x)
    (A.machine.runOracle A.time (paramsWord (univ w8) params)) (DcB Dm) hflood h4
  -- ideal side
  have gI : CloseTo ((GV D kb L impl A fun _ =>
        idealView (S := setting D) (Wb := Wb D) (J := Jh D) (Pos := Pos)).bind (DcB Dm))
      ((GV0 D kb L impl A (idealVW D)).bind (DcB Dm))
      (Fintype.card (Attribute w8) * (epsSetup D + epsCT D)) := by
    rw [← gameV0_idealView_eq]
    exact ((gameV0_close A fun x => idealVW_close x).symm).bind_left (DcB Dm)
  have htot := (g0.trans hc).trans gI
  have hfin : Fintype.card (Attribute w8) * epsSetup D +
      (Fintype.card (Attribute w8) * delta1 (setting D) (Wb D) Pos +
        Fintype.card (Attribute w8) * εfl + Fintype.card (Attribute w8) * deltaT (setting D) (Wb D) +
        ENNReal.ofReal |rAcc D kb L impl χs χ χfl A Dm - uAcc D kb L impl χfl A Dm| +
        Fintype.card (Attribute w8) * delta5 (setting D) (Wb D) Pos +
        Fintype.card (Attribute w8) * deltaT (setting D) (Wb D)) +
      Fintype.card (Attribute w8) * (epsSetup D + epsCT D) =
      statW D εfl + ENNReal.ofReal |rAcc D kb L impl χs χ χfl A Dm - uAcc D kb L impl χfl A Dm| := by
    unfold statW; ring
  have hcard : Fintype.card (univ w8).Attr = Fintype.card (Attribute w8) := rfl
  simp only [hcard] at htot
  unfold rAcc uAcc at hfin
  rw [hfin] at htot
  have hne : statW D εfl + ENNReal.ofReal |rAcc D kb L impl χs χ χfl A Dm -
      uAcc D kb L impl χfl A Dm| ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hS, ENNReal.ofReal_ne_top⟩
  have key := abs_sub_le_of_closeTo' htot (by unfold rAcc uAcc at hne; exact hne) true
  refine key.trans (le_of_eq ?_)
  rw [ENNReal.toReal_add hS ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

/-! ### Attribute hiding -/

variable (D kb L)

/-- **The reduction machine** for the adversary `A` and the distinguisher `Dm`: it accepts the
words of real and uniform circular Ring-LWE instances at `p` with the acceptance probabilities of
the reduction's experiment, at a cost at most `C (cost A + cost Dm)²`. -/
def RedMachine (p : CircularRingLWE.Params) (impl : Impl sig) (χs χ χfl : PMF (Rg D)) (C : ℝ)
    (A : Machine 3) (Dm : Machine) : Prop :=
  ∃ R : Machine, R.acceptProb (CircularRingLWE.realLaw p) = rAcc D kb L impl χs χ χfl A Dm ∧
    R.acceptProb (CircularRingLWE.idealLaw p) = uAcc D kb L impl χfl A Dm ∧
    (R.cost : ℝ) ≤ C * ((A.cost + Dm.cost : ℕ) : ℝ) ^ 2

variable {D kb L}

/-- **Attribute hiding of the implementation from circular Ring-LWE**, given the reduction machines.
-/
theorem attributeHiding_of_reduction [Nonempty (Wb D)] {impl : Impl sig} {χs χ χfl : PMF (Rg D)}
    (hI : ImplSpec D kb L impl χs χ χfl) (hcovR : RealCovW D kb) (hcovS : SimCovW D kb)
    (hb : 22 ≤ D.b) {Sim : Machine} (hSim : SimSpec D Sim) {εfl : ℝ≥0∞}
    (hflood : ∀ eb ∈ (iidLaw χ (BCol (Wb D) (setting D).τ)).support,
      ∀ zr : PrI (setting D) Pos → Wb D → Bool,
        CloseTo ((floodLaw (setting D) Pos χfl).map (· + floodShift eb zr))
          (floodLaw (setting D) Pos χfl) εfl)
    (hS : statW D εfl ≠ ⊤) (hstat : 4 * (2 : ℝ) ^ 128 * (statW D εfl).toReal ^ 2 ≤ 1)
    (p : CircularRingLWE.Params) (kb' : ℕ) (C : ℝ) (hC : 0 < C)
    (hkb : 64 * ((2 : ℝ) ^ 128) ^ 2 * C ≤ (2 : ℝ) ^ kb')
    (hard : CircularRingLWE.decision.HardAt p kb')
    (hred : ∀ (A : Machine 3) (Dm : Machine), Admissible (univ w8) params impl Sim A →
      RedMachine D kb L p impl χs χ χfl C A Dm) :
    AttributeHiding (univ w8) params impl := by
  refine ⟨Sim, fun A hadm Dm => ?_⟩
  obtain ⟨R, hr, hu, hcost⟩ := hred A Dm hadm
  have hadv := advantage_le hI hcovR hcovS hb hSim hflood hS A Dm hadm
  rw [← hr, ← hu] at hadv
  set g := Dm.acceptProb ((PE.real (univ w8) params impl A).map view) -
    Dm.acceptProb ((PE.ideal (univ w8) params impl Sim A).map view)
  have hgain : (Problem.decision ((PE.real (univ w8) params impl A).map view)
      ((PE.ideal (univ w8) params impl Sim A).map view)).gain Dm = g ^ 2 := rfl
  rw [hgain]
  have ha : (1 : ℝ) ≤ ((A.cost + Dm.cost : ℕ) : ℝ) := by
    have := A.one_le_cost; exact_mod_cast (by omega : 1 ≤ A.cost + Dm.cost)
  have hg1 : g ^ 2 ≤ 1 := by
    have h1 := Machine.acceptProb_nonneg Dm ((PE.real (univ w8) params impl A).map view)
    have h2 := Machine.acceptProb_le_one Dm ((PE.real (univ w8) params impl A).map view)
    have h3 := Machine.acceptProb_nonneg Dm ((PE.ideal (univ w8) params impl Sim A).map view)
    have h4 := Machine.acceptProb_le_one Dm ((PE.ideal (univ w8) params impl Sim A).map view)
    nlinarith
  have hR : (2 : ℝ) ^ kb' * (R.acceptProb (CircularRingLWE.realLaw p) -
      R.acceptProb (CircularRingLWE.idealLaw p)) ^ 2 ≤ C * ((A.cost + Dm.cost : ℕ) : ℝ) ^ 2 :=
    (hard R).trans hcost
  have h0 : (2 : ℝ) ^ kb' * (0 : ℝ) ^ 2 ≤ C * ((A.cost + Dm.cost : ℕ) : ℝ) ^ 2 := by
    rw [sq, mul_zero, mul_zero]; positivity
  have := quad_loss ((2 : ℝ) ^ 128) ((2 : ℝ) ^ kb') C ((A.cost + Dm.cost : ℕ) : ℝ)
    (statW D εfl).toReal _ 0 0 g (by positivity) hkb hC ha hstat ENNReal.toReal_nonneg
    hR h0 h0 (by simp only [abs_zero, add_zero]; exact hadv) hg1
  show (2 : ℝ) ^ params.secBits * g ^ 2 ≤ _
  exact_mod_cast this

end AdvancedEncryption.ExpLUT.Prog
