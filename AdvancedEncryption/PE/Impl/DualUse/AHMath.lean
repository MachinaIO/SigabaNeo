import PE.Impl.DualUse.IdealBridge

/-!
# Attribute hiding of the implementation, against any distinguisher

For every adversary `A` (a machine with the three oracles) and every distinguisher `D` (a
machine), the probabilities that `D` accepts the outputs of the real and of the ideal experiment
differ by at most the statistical terms (`1024 (3 δ₁ + ε + δ₆)`) plus the advantages, on
Ring-LWE instances, of the three experiments-as-distinguishers of the reductions
(`advantage_le`). It remains to realize these by machines of bounded cost.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

/-- Closeness bounds the difference of the probabilities of an outcome. -/
theorem abs_sub_le_of_closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε)
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

/-- The input of the distinguisher from the observable part of a run. -/
def viewObs (o : List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool) : List Bool :=
  encodeTuple [encOpt PUniv.encAttr o.2.1, encOpt PUniv.encMsg o.2.2.1, o.1]

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]
variable {ms : Machines hk c}

/-- The experiment of `A` against the challenger of the view law `V`. -/
noncomputable abbrev G (A : Machine 3) (V : Date → PMF (PK hk c × CT hk c)) :=
  gameV hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A V

/-- The distinguisher on observable runs. -/
noncomputable def Dc (D : Machine) (o : List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool) :
    PMF (List Bool) := D.run (viewObs o)

theorem real_view_bind (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine) :
    ((PE.real PUniv params (impl hk c ms) A).map view).bind D.run = (G A (V0 hk c)).bind (Dc D) := by
  have e := real_eq_gameV (ms := ms) hdec hcov A
  calc ((PE.real PUniv params (impl hk c ms) A).map view).bind D.run
      = ((PE.real PUniv params (impl hk c ms) A).map
          (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad))).bind (Dc D) := by
        rw [PMF.bind_map, PMF.bind_map]; rfl
    _ = (G A (V0 hk c)).bind (Dc D) := congrArg (fun μ => PMF.bind μ (Dc D)) e

theorem ideal_view_bind (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine) :
    ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map view).bind D.run =
      (G A (VI0 hk c)).bind (Dc D) := by
  have e := ideal_eq_gameV (ms := ms) hdec hcov A
  calc ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map view).bind D.run
      = ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map
          (fun r => (r.1, r.2.attr, r.2.msg, r.2.bad))).bind (Dc D) := by
        rw [PMF.bind_map, PMF.bind_map]; rfl
    _ = (G A (VI0 hk c)).bind (Dc D) := congrArg (fun μ => PMF.bind μ (Dc D)) e

/-- **The advantage of any distinguisher** is at most the statistical terms plus the advantages of
the three experiments-as-distinguishers on Ring-LWE instances. -/
theorem advantage_le (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine) {ε δ₃ δ₅ δI : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (h₃ : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (G A fun x => F3 hk c x ab).bind (Dc D))
      (inst3Unif.bind fun ab => (G A fun x => F3 hk c x ab).bind (Dc D)) δ₃)
    (h₅ : CloseTo ((nfReal (χR c)).bind fun i => (G A fun x => F5 hk c x i).bind (Dc D))
      (nfUnif.bind fun i => (G A fun x => F5 hk c x i).bind (Dc D)) δ₅)
    (hI : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (G A fun x => FI hk c x ab).bind (Dc D))
      (inst3Unif.bind fun ab => (G A fun x => FI hk c x ab).bind (Dc D)) δI)
    (hfin : (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε + δ₃ +
        δ₅ + Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d)) +
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + δI +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d)) ≠ ⊤) :
    |D.acceptProb ((PE.real PUniv params (impl hk c ms) A).map view) -
        D.acceptProb ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map view)| ≤
      ((Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε + δ₃ +
        δ₅ + Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d)) +
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + δI +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d))).toReal := by
  have cr := chain_real hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A (Dc D)
    hflood h₃ h₅
  have ci := chain_ideal hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A (Dc D) hI
  have h := cr.trans ci.symm
  unfold Machine.acceptProb
  rw [real_view_bind hdec hcov A D, ideal_view_bind hdec hcov A D]
  exact abs_sub_le_of_closeTo h hfin [true]

/-- The distinguisher that rejects runs whose flag is up. -/
noncomputable def DcStar (D : Machine) (o : List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool) :
    PMF (List Bool) := if o.2.2.2 then PMF.pure [false] else Dc D o

/-- With an admissible adversary, rejecting the runs with the flag up changes nothing. -/
theorem bind_star {μ : PMF (List Bool × Option PUniv.Attr × Option PUniv.Msg × Bool)} (D : Machine)
    (h : ∀ o ∈ μ.support, o.2.2.2 = false) : μ.bind (DcStar D) = μ.bind (Dc D) :=
  PMF.bind_congr_on_support _ _ _ fun o ho => by simp [DcStar, h o ho]

theorem real_star (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine)
    (hadm : ∀ r ∈ (PE.real PUniv params (impl hk c ms) A).support, r.2.bad = false) :
    ((PE.real PUniv params (impl hk c ms) A).map view).bind D.run =
      (G A (V0 hk c)).bind (DcStar D) := by
  rw [real_view_bind hdec hcov A D]
  refine (bind_star D ?_).symm
  intro o ho
  have e := real_eq_gameV (ms := ms) hdec hcov A
  rw [show G A (V0 hk c) = _ from e.symm] at ho
  obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  exact hadm r hr

theorem ideal_star (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine)
    (hadm : ∀ r ∈ (PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).support,
      r.2.bad = false) :
    ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map view).bind D.run =
      (G A (VI0 hk c)).bind (DcStar D) := by
  rw [ideal_view_bind hdec hcov A D]
  refine (bind_star D ?_).symm
  intro o ho
  have e := ideal_eq_gameV (ms := ms) hdec hcov A
  rw [show G A (VI0 hk c) = _ from e.symm] at ho
  obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  exact hadm r hr

/-- **The advantage of any distinguisher against an admissible adversary**, with the
experiments-as-distinguishers rejecting the runs with the flag up. -/
theorem advantage_le_star (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine)
    (hadm : Admissible PUniv params (impl hk c ms) (simMachine hk c) A) {ε δ₃ δ₅ δI : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (h₃ : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (G A fun x => F3 hk c x ab).bind (DcStar D))
      (inst3Unif.bind fun ab => (G A fun x => F3 hk c x ab).bind (DcStar D)) δ₃)
    (h₅ : CloseTo ((nfReal (χR c)).bind fun i => (G A fun x => F5 hk c x i).bind (DcStar D))
      (nfUnif.bind fun i => (G A fun x => F5 hk c x i).bind (DcStar D)) δ₅)
    (hI : CloseTo ((inst3Real (k := k) (χR c)).bind fun ab =>
        (G A fun x => FI hk c x ab).bind (DcStar D))
      (inst3Unif.bind fun ab => (G A fun x => FI hk c x ab).bind (DcStar D)) δI)
    (hfin : (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε + δ₃ +
        δ₅ + Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d)) +
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + δI +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d)) ≠ ⊤) :
    |D.acceptProb ((PE.real PUniv params (impl hk c ms) A).map view) -
        D.acceptProb ((PE.ideal PUniv params (impl hk c ms) (simMachine hk c) A).map view)| ≤
      ((Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε + δ₃ +
        δ₅ + Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d)) +
      (Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + δI +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d))).toReal := by
  have cr := chain_real hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcStar D) hflood h₃ h₅
  have ci := chain_ideal hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcStar D) hI
  have h := cr.trans ci.symm
  unfold Machine.acceptProb
  rw [real_star hdec hcov A D hadm.1, ideal_star hdec hcov A D hadm.2]
  exact abs_sub_le_of_closeTo h hfin [true]

end AdvancedEncryption.DualUse
