import PE.Impl.DualUse.AHMath
import PE.Impl.Game.Assembly

/-!
# The advantage in terms of acceptance probabilities

For an admissible adversary `A` and a distinguisher `D`, the advantage of `D` is at most the
statistical terms plus `|r_i − u_i|` for the three Ring-LWE steps, where `r_i` and `u_i` are the
probabilities that the experiment-as-distinguisher (with `D` rejecting the runs whose flag is up)
accepts on a real and on a uniform instance (`advantage_le_acc`). A reduction machine for step `i`
has to accept with exactly these probabilities.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped ENNReal

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k} [NeZero c.d]

/-- Acceptance of the distinguisher rejecting runs with the flag up, as a bit. -/
noncomputable def DcB (D : Machine) (o : List Bool × Option dateUniverse.Attr × Option dateUniverse.Msg × Bool) : PMF Bool :=
  (DcStar D o).map fun w => decide (w = [true])

/-- The probability of acceptance of an experiment-as-distinguisher on a law of instances. -/
noncomputable def accOn {Inst : Type} (A : Machine 3) (D : Machine) (inst : PMF Inst)
    (F : Date → Inst → PMF (PK hk c × CT hk c)) : ℝ :=
  ((inst.bind fun i => (G A fun x => F x i).bind (DcB D)) true).toReal

theorem bind_DcB_true (μ : PMF (List Bool × Option dateUniverse.Attr × Option dateUniverse.Msg × Bool)) (D : Machine) :
    (μ.bind (DcB D)) true = (μ.bind (DcStar D)) [true] := by
  simp only [DcB, PMF.bind_apply, PMF.map_apply]
  refine tsum_congr fun o => ?_
  congr 1
  rw [tsum_eq_single [true]]
  · simp
  · intro w hw; simp [hw]

/-- The statistical part of the bound. -/
noncomputable def statTerm (c : Conf N K k) (hk : 2 ^ K < 2 ^ k) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε +
    Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d) +
    Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) +
    Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d)

/-- **The advantage in terms of acceptance probabilities.** -/
theorem advantage_le_acc (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine)
    (hadm : Admissible dateUniverse params (impl hk c) (simMachine hk c) A) {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (hS : statTerm c hk ε ≠ ⊤) :
    |D.acceptProb ((PE.real dateUniverse params (impl hk c) A).map view) -
        D.acceptProb ((PE.ideal dateUniverse params (impl hk c) (simMachine hk c) A).map view)| ≤
      (statTerm c hk ε).toReal +
        |accOn A D (inst3Real (k := k) (χR c)) (F3 hk c) - accOn A D inst3Unif (F3 hk c)| +
        |accOn A D (nfReal (χR c)) (F5 hk c) - accOn A D nfUnif (F5 hk c)| +
        |accOn A D (inst3Real (k := k) (χR c)) (FI hk c) - accOn A D inst3Unif (FI hk c)| := by
  have cr := chain_real hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcB D) hflood (Generic.closeTo_bool _ _) (Generic.closeTo_bool _ _)
  have ci := chain_ideal hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcB D) (Generic.closeTo_bool _ _)
  have h := cr.trans ci.symm
  have hR : D.acceptProb ((PE.real dateUniverse params (impl hk c) A).map view) =
      (((G A (V0 hk c)).bind (DcB D)) true).toReal := by
    unfold Machine.acceptProb
    rw [real_star hdec hcov A D hadm.1, bind_DcB_true]
  have hI : D.acceptProb ((PE.ideal dateUniverse params (impl hk c) (simMachine hk c) A).map view) =
      (((G A (VI0 hk c)).bind (DcB D)) true).toReal := by
    unfold Machine.acceptProb
    rw [ideal_star hdec hcov A D hadm.2, bind_DcB_true]
  rw [hR, hI]
  have hfin : ∀ x : ℝ, ENNReal.ofReal x ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hS' := hS
  unfold statTerm at hS'
  have key := abs_sub_le_of_closeTo h (by
    simp only [ne_eq, ENNReal.add_eq_top, not_or, ENNReal.ofReal_ne_top, not_false_eq_true,
      and_true] at hS' ⊢
    tauto) true
  refine key.trans (le_of_eq ?_)
  simp only [ne_eq, ENNReal.add_eq_top, not_or] at hS'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hS'
  simp only [statTerm, accOn, G, ENNReal.toReal_add, ne_eq, ENNReal.add_eq_top, h1, h2, h3, h4, h5,
    ENNReal.ofReal_ne_top, not_false_eq_true, or_self, ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

end AdvancedEncryption.DualUse
