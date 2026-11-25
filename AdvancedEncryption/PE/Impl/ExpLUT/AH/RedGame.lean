import PE.Impl.ExpLUT.AH.Games

/-!
# The experiment the reduction runs (package G)

The reduction of the circular Ring-LWE step (H3′ → H4) draws, from an instance `inst`, its own
secret `σ ← redSec x inst` for the selected attribute (the public data computed from the instance,
the programming `zr`, the core values and the flooding errors, `PE.Impl.ExpLUT.Reduction`), gives
the adversary the public key and challenge of `view2` (`redView`), and answers key queries with
the simulated trapdoor `T_sim` of Lemma 11 computed from its own programming (`KGsim`, the box
sampler of `redKeyLaw`), without any trapdoor of `B⁽¹⁾` (`specRed`).

`accept_red`: **the reduction runs the hybrid**, as far as a continuation rejecting the runs whose
flag is up can tell: the two challengers differ only on key queries authorized for the selected
attribute (`KGsim_eq_KGiW`: on an unauthorized predicate word `F(x) = 1`, so `T_sim` is a trapdoor
and the reduction's keys have the ideal law, `redKeyLaw_eq_ideal`, when the boxes cover the shifts
of `T_sim`, `SimCovW`), and those raise the flag (`Generic.obs_until_bad`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open scoped ENNReal

variable (D : Dims) (kb : KeyBoxes D) (L : ℕ)

/-- The reduction's secret: the attribute, the public data, the programming, the core values and
the flooding errors. -/
abbrev RSec := (Pos → ℕ) × PubData (setting D) (Wb D) (Jh D) ×
  (PrI (setting D) Pos → Wb D → Bool) × Core (setting D) (Wb D) (Jh D) × FloodV (setting D) Pos

/-- The circular instances at the dimensions `D`. -/
abbrev CInst := CircInst (setting D) (Wb D) (Jh D)

/-- **The reduction's secret law** for the selected attribute and the instance. -/
noncomputable def redSec (χfl : PMF (Rg D)) (x : Attribute w8) (inst : CInst D) : PMF (RSec D) :=
  (PMF.uniformOfFintype (BCol (Wb D) D.K → Rg D)).bind fun B2 =>
  (PMF.uniformOfFintype (Jh D → Col D.K → Rg D)).bind fun H2 =>
  (PMF.uniformOfFintype (Rg D)).bind fun d2 =>
  (floodLaw (setting D) Pos χfl).bind fun fl =>
  (zrLaw (setting D) (Wb D) Pos).map fun zr =>
    (attrN x, redPub inst B2 H2 d2, zr, redCore inst B2 H2 d2, fl)

/-- The view of the reduction's secret: H2's view from `b`. -/
noncomputable def redView (σ : RSec D) : MPKt D × CTt D :=
  view2 (helperMap D) wSt σ.2.1 σ.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2

theorem red_eq (χfl : PMF (Rg D)) (x : Attribute w8) (inst : CInst D) :
    red (helperMap D) wSt χfl (attrN x) inst = (redSec D χfl x inst).map (redView D) := by
  unfold red redSec
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

theorem redSec_attr (χfl : PMF (Rg D)) (x : Attribute w8) (inst : CInst D) :
    ∀ σ ∈ (redSec D χfl x inst).support, σ.1 = attrN x := by
  intro σ hσ
  simp only [redSec, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hσ
  obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := hσ
  rfl

open Classical in
/-- **The reduction's key oracle**: one try of box rejection with the trapdoor `T_sim` of Lemma 11
computed from the reduction's own programming. -/
noncomputable def KGsim (σ : RSec D) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ L then
    if ValidC C then
      (redKeyLaw (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) wSt σ.2.1 σ.1
        σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2 (bpOf (progOf C))).map
        fun o => (skEnc D).enc ((redView D σ).1, keyOfOutput o)
    else PMF.pure ((skEnc D).enc ((redView D σ).1, 0))
  else PMF.pure []

/-- **The reduction's challenger** for the instance `inst`. -/
noncomputable def specRed (impl : Impl sig) (χfl : PMF (Rg D)) (inst : CInst D) :
    Generic.Spec (univ w8) (RSec D) where
  setup x := redSec D χfl x inst
  pub σ := (mpkEnc D).enc (redView D σ).1
  key := KGsim D kb L
  chal σ μ := PMF.pure ((ctEnc D).enc (shiftCT (half D) (msgR D μ) (redView D σ).2))
  auth := authW impl

/-- The observable experiment of the reduction for the instance `inst`. -/
noncomputable def redGame (impl : Impl sig) (χfl : PMF (Rg D)) (A : Machine 3) (inst : CInst D) :=
  (ProbOracleComp.runWith (Generic.oracle (specRed D kb L impl χfl inst))
    (A.machine.runOracle A.time (paramsWord (univ w8) params))
    ({} : Generic.GState (univ w8) (RSec D))).map Generic.obs

/-- The shifts of `T_sim` are covered by the boxes, for every programmed public key and every
predicate word. -/
def SimCovW : Prop :=
  ∀ (x : Pos → ℕ) (P : PubData (setting D) (Wb D) (Jh D)) (zr : PrI (setting D) Pos → Wb D → Bool)
    (core : Core (setting D) (Wb D) (Jh D)) (fl : FloodV (setting D) Pos) (C : List Bool), ValidC C →
    ∀ x' ∈ kb.Small, ∀ y, x' + (show PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D from
      simTrap (helperMap D) (view2 (helperMap D) wSt P x zr core fl).1 (bpOf (progOf C))
        (simKey (helperMap D) (view2 (helperMap D) wSt P x zr core fl).1 (bpOf (progOf C))
          (view2 (helperMap D) wSt P x zr core fl).2 x (ExpLUT.progOf zr)) (gadDec y)) ∈ kb.Big

variable {D kb L}

/-- **On unauthorized queries the reduction's keys are the ideal keys.** -/
theorem KGsim_eq_KGiW {impl : Impl sig} (hEval : impl.machine .eval = evalMachineX)
    (hb : 22 ≤ D.b) (hcov : SimCovW D kb) (x : Attribute w8) (σ : RSec D) (hσ : σ.1 = attrN x)
    (C : List Bool) (hC : authW impl C x = false) :
    KGsim D kb L σ C = KGiW D kb L (redView D σ).1 C := by
  unfold KGsim KGiW
  split_ifs with hL hw
  · have hna : ¬ Authorized (U := univ w8) params impl C x := by
      simpa [authW] using hC
    rw [authorized_iff impl hEval] at hna
    have hout : (progOf C).output x = true := by
      cases h : (progOf C).output x
      · exact absurd ⟨hw, h⟩ hna
      · rfl
    have hF1 : (bpOf (progOf C)).eval (attrN x) = 1 := by rw [eval_bpOf, hout]; rfl
    have hW : 2 ^ 22 ≤ (setting D).E.W := Nat.pow_le_pow_right (by norm_num) hb
    rcases σ with ⟨xs, P, zr, core, fl⟩
    simp only at hσ
    subst hσ
    have e := redKeyLaw_eq_ideal (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) wSt
      gadZ_gadDec (lemma8_canon _ rfl D.h2 _ _) (bpOf (progOf C)) (wf_bpOf _ hW) rfl P (attrN x)
      (attrN_lt _ x) hF1 zr core fl (hcov (attrN x) P zr core fl C hw)
    simp only [e]
    rfl
  · rfl
  · rfl

/-- Acceptance at `true` only depends on the outcomes with the flag down. -/
theorem bind_true_eq' {α : Type} {μ ν : PMF (α × Option (Attribute w8) × Option Bool × Bool)}
    (h : ∀ o, o.2.2.2 = false → μ o = ν o)
    (f : α × Option (Attribute w8) × Option Bool × Bool → PMF Bool)
    (hf : ∀ o, o.2.2.2 = true → f o true = 0) : (μ.bind f) true = (ν.bind f) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun o => ?_
  by_cases hb : o.2.2.2 = true
  · rw [hf o hb, mul_zero, mul_zero]
  · rw [h o (by simpa using hb)]

/-- **The reduction runs the hybrid** (H3′ on a real instance, H4 on a uniform one), as far as a
continuation rejecting the runs whose flag is up can tell. -/
theorem accept_red {impl : Impl sig} (hEval : impl.machine .eval = evalMachineX) (hb : 22 ≤ D.b)
    (hcov : SimCovW D kb) (χfl : PMF (Rg D)) (A : Machine 3) (inst : CInst D)
    (f : List Bool × Option (Attribute w8) × Option Bool × Bool → PMF Bool)
    (hf : ∀ o, o.2.2.2 = true → f o true = 0) :
    ((GV D kb L impl A fun x => red (helperMap D) wSt χfl (attrN x) inst).bind f) true =
      ((redGame D kb L impl χfl A inst).bind f) true := by
  set prog := A.machine.runOracle A.time (paramsWord (univ w8) params)
  set spV := specV (univ w8) (half D) (msgR D) (mpkEnc D).enc (ctEnc D).enc (KGiW D kb L)
    (authW impl) (fun x => (redSec D χfl x inst).map (redView D))
  have hcomap := Generic.runWith_comap spV (redView D) prog (fun x => redSec D χfl x inst)
    (fun _ => rfl)
  have hV : (fun x => red (helperMap D) wSt χfl (attrN x) inst) =
      fun x => (redSec D χfl x inst).map (redView D) := funext fun x => red_eq D χfl x inst
  have hG : GV D kb L impl A (fun x => red (helperMap D) wSt χfl (attrN x) inst) =
      (ProbOracleComp.runWith (Generic.oracle (spV.comap (redView D) fun x => redSec D χfl x inst))
        prog {}).map Generic.obs := by
    rw [hV]
    show (ProbOracleComp.runWith (Generic.oracle spV) prog {}).map Generic.obs = _
    rw [← hcomap, PMF.map_comp]
    rfl
  rw [hG]
  refine bind_true_eq' (fun o ho => ?_) f hf
  refine (Generic.obs_until_bad (spV.comap (redView D) fun x => redSec D χfl x inst)
    (specRed D kb L impl χfl inst) rfl rfl rfl rfl ?_ prog o ho).symm
  intro x σ hσ C hC
  exact KGsim_eq_KGiW hEval hb hcov x σ (redSec_attr D χfl x inst σ hσ) C hC


/-! ### The machines' reduction secret

A machine with fair coins and a bounded clock only produces dyadic probabilities, and
`2^K − 1` is odd: the uniform parts `B̄⁽²⁾`, `H⁽²⁾`, `d₂` of `redSec` cannot be drawn exactly.
The reduction machine draws them from `unifW` (`redSecW`); the secret is drawn once, so the
experiment moves by at most `epsRed = (|BCol| + |Jh| |Col| + 1) ε_U` (`closeTo_redGame`). -/

variable (D kb L)

/-- **The machines' reduction secret**: `redSec` with independent `unifW` entries for the uniform
parts. -/
noncomputable def redSecW (χfl : PMF (Rg D)) (x : Attribute w8) (inst : CInst D) : PMF (RSec D) :=
  (iidLaw (unifW D) (BCol (Wb D) D.K)).bind fun B2 =>
  (iidFam (unifW D) (Jh D) (Col D.K)).bind fun H2 =>
  (unifW D).bind fun d2 =>
  (floodLaw (setting D) Pos χfl).bind fun fl =>
  (zrLaw (setting D) (Wb D) Pos).map fun zr =>
    (attrN x, redPub inst B2 H2 d2, zr, redCore inst B2 H2 d2, fl)

/-- The distance of the machines' reduction secret: `ε_U` per uniform ring element. -/
noncomputable def epsRed : ℝ≥0∞ :=
  Fintype.card (BCol (Wb D) D.K) * epsU D +
    (Fintype.card (Jh D) * (Fintype.card (Col D.K) * epsU D) + (epsU D + 0))

theorem closeTo_redSec (χfl : PMF (Rg D)) (x : Attribute w8) (inst : CInst D) :
    CloseTo (redSec D χfl x inst) (redSecW D χfl x inst) (epsRed D) := by
  unfold redSec redSecW epsRed
  refine (closeTo_iid_unif D (BCol (Wb D) D.K)).bind fun B2 _ => ?_
  refine (closeTo_iidFam_unif D (Jh D) (Col D.K)).bind fun H2 _ => ?_
  exact (closeTo_unif_unifW D).bind fun d2 _ => CloseTo.refl _

/-- **The machines' reduction challenger**: `specRed` with the secret `redSecW`. -/
noncomputable def specRedW (impl : Impl sig) (χfl : PMF (Rg D)) (inst : CInst D) :
    Generic.Spec (univ w8) (RSec D) :=
  { specRed D kb L impl χfl inst with setup := fun x => redSecW D χfl x inst }

/-- The observable experiment of the machines' reduction for the instance `inst`. -/
noncomputable def redGameW (impl : Impl sig) (χfl : PMF (Rg D)) (A : Machine 3) (inst : CInst D) :=
  (ProbOracleComp.runWith (Generic.oracle (specRedW D kb L impl χfl inst))
    (A.machine.runOracle A.time (paramsWord (univ w8) params))
    ({} : Generic.GState (univ w8) (RSec D))).map Generic.obs

/-- **The machines' reduction runs the reduction's experiment up to `epsRed`.** -/
theorem closeTo_redGame (impl : Impl sig) (χfl : PMF (Rg D)) (A : Machine 3) (inst : CInst D) :
    CloseTo (redGame D kb L impl χfl A inst) (redGameW D kb L impl χfl A inst) (epsRed D) :=
  (Generic.closeTo_runWith_setup_one (specRed D kb L impl χfl inst)
    (fun x => redSecW D χfl x inst) (fun x => closeTo_redSec D χfl x inst) _ {}).map _

end AdvancedEncryption.ExpLUT.Prog
