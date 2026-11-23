import PE.Impl.DualUse.AHMath
import PE.Impl.Game.Assembly
import SigabaNeo.Lib.Crypto.QuadLoss

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
variable {ms : Machines hk c}

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
  Fintype.card PUniv.Attr * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card PUniv.Attr * ε +
    Fintype.card PUniv.Attr * delta6 (Sdw (N := N) hk) (Fin c.d) +
    Fintype.card PUniv.Attr * delta1 (Sdw (N := N) hk) (Fin c.d) +
    Fintype.card PUniv.Attr * delta1 (Sdw (N := N) hk) (Fin c.d)

/-- `statTerm` with the attributes of the game chain (`GameChain` counts `Date`, the universe's
attributes in Stage I). -/
theorem statTerm_eq_date (c : Conf N K k) (hk : 2 ^ K < 2 ^ k) (ε : ℝ≥0∞) :
    statTerm c hk ε =
      Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) + Fintype.card Date * ε +
        Fintype.card Date * delta6 (Sdw (N := N) hk) (Fin c.d) +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) +
        Fintype.card Date * delta1 (Sdw (N := N) hk) (Fin c.d) := rfl

/-- **The advantage in terms of acceptance probabilities.** -/
theorem advantage_le_acc (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hcov : RealCovered hk c) (A : Machine 3) (D : Machine)
    (hadm : Admissible dateUniverse params (impl hk c ms) (simMachine hk c) A) {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (hS : statTerm c hk ε ≠ ⊤) :
    |D.acceptProb ((PE.real dateUniverse params (impl hk c ms) A).map view) -
        D.acceptProb ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view)| ≤
      (statTerm c hk ε).toReal +
        |accOn A D (inst3Real (k := k) (χR c)) (F3 hk c) - accOn A D inst3Unif (F3 hk c)| +
        |accOn A D (nfReal (χR c)) (F5 hk c) - accOn A D nfUnif (F5 hk c)| +
        |accOn A D (inst3Real (k := k) (χR c)) (FI hk c) - accOn A D inst3Unif (FI hk c)| := by
  have cr := chain_real hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcB D) hflood (Generic.closeTo_bool _ _) (Generic.closeTo_bool _ _)
  have ci := chain_ideal hk c (pkEnc hk c).enc (ctEnc hk c).enc (KGi hk c) (authI hk c) A
    (DcB D) (Generic.closeTo_bool _ _)
  have h := cr.trans ci.symm
  have hR : D.acceptProb ((PE.real dateUniverse params (impl hk c ms) A).map view) =
      (((G A (V0 hk c)).bind (DcB D)) true).toReal := by
    unfold Machine.acceptProb
    rw [real_star hdec hcov A D hadm.1, bind_DcB_true]
  have hI : D.acceptProb ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view) =
      (((G A (VI0 hk c)).bind (DcB D)) true).toReal := by
    unfold Machine.acceptProb
    rw [ideal_star hdec hcov A D hadm.2, bind_DcB_true]
  rw [hR, hI]
  have hfin : ∀ x : ℝ, ENNReal.ofReal x ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hS' := hS
  rw [statTerm_eq_date] at hS'
  have key := abs_sub_le_of_closeTo h (by
    simp only [ne_eq, ENNReal.add_eq_top, not_or, ENNReal.ofReal_ne_top, not_false_eq_true,
      and_true] at hS' ⊢
    tauto) true
  refine key.trans (le_of_eq ?_)
  simp only [ne_eq, ENNReal.add_eq_top, not_or] at hS'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hS'
  simp only [statTerm_eq_date, accOn, G, ENNReal.toReal_add, ne_eq, ENNReal.add_eq_top, h1, h2, h3, h4, h5,
    ENNReal.ofReal_ne_top, not_false_eq_true, or_self, ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

/-- A reduction for one step: a machine accepting a real and a uniform instance word with the
probabilities of the experiment-as-distinguisher, at a cost quadratic in the adversary's (the reduction runs the adversary and the distinguisher in one
machine, whose description length has a cross term `states(D) · 3^tapes(A)`). -/
def Reduces (r u : ℝ) (real ideal : PMF (List Bool)) (C : ℝ) (a : ℕ) : Prop :=
  ∃ R : Machine, R.acceptProb real = r ∧ R.acceptProb ideal = u ∧ (R.cost : ℝ) ≤ C * (a : ℝ) ^ 2

/-- **Attribute hiding from three reductions.** If each Ring-LWE step has a reduction of cost at
most `C · (cost A + cost D)²` and the three decision problems have `k` bits with
`2^k ≥ 64 · 2^(2λ) · C`, and the statistical terms are below `2^{-λ/2}/2`, the implementation has
weak attribute hiding with `λ = params.secBits` bits. -/
theorem attributeHiding_of_reductions
    (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u) (hcov : RealCovered hk c)
    {ε : ℝ≥0∞}
    (hflood : ∀ rest ∈ (lawRestC hk c).support, ∀ w : JC (Sdw (N := N) hk) → (Fin c.d → Bool),
      CloseTo ((lawEc hk c).map fun e j => e j + rest.2.1 * wMat w j) (lawEc hk c) ε)
    (hS : statTerm c hk ε ≠ ⊤)
    (hstat : 4 * (2 : ℝ) ^ params.secBits * (statTerm c hk ε).toReal ^ 2 ≤ 1)
    (w3r w3u w5r w5u wIr wIu : PMF (List Bool)) (kb : ℕ) (C : ℝ) (hC : 0 < C)
    (hk64 : 64 * ((2 : ℝ) ^ params.secBits) ^ 2 * C ≤ (2 : ℝ) ^ kb)
    (hard3 : (Problem.decision w3r w3u).HardAt kb) (hard5 : (Problem.decision w5r w5u).HardAt kb)
    (hardI : (Problem.decision wIr wIu).HardAt kb)
    (hred : ∀ (A : Machine 3) (D : Machine),
      Admissible dateUniverse params (impl hk c ms) (simMachine hk c) A →
        Reduces (accOn A D (inst3Real (k := k) (χR c)) (F3 hk c)) (accOn A D inst3Unif (F3 hk c))
            w3r w3u C (A.cost + D.cost) ∧
          Reduces (accOn A D (nfReal (χR c)) (F5 hk c)) (accOn A D nfUnif (F5 hk c))
            w5r w5u C (A.cost + D.cost) ∧
          Reduces (accOn A D (inst3Real (k := k) (χR c)) (FI hk c)) (accOn A D inst3Unif (FI hk c))
            wIr wIu C (A.cost + D.cost)) :
    AttributeHiding dateUniverse params (impl hk c ms) := by
  refine ⟨simMachine hk c, fun A hadm D => ?_⟩
  obtain ⟨⟨R3, r3, u3, c3⟩, ⟨R5, r5, u5, c5⟩, ⟨RI, rI, uI, cI⟩⟩ := hred A D hadm
  have hadv := advantage_le_acc hdec hcov A D hadm hflood hS
  rw [← r3, ← u3, ← r5, ← u5, ← rI, ← uI] at hadv
  set g := D.acceptProb ((PE.real dateUniverse params (impl hk c ms) A).map view) -
    D.acceptProb ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view)
  have hgain : (Problem.decision ((PE.real dateUniverse params (impl hk c ms) A).map view)
      ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view)).gain D = g ^ 2 := rfl
  rw [hgain]
  have hd : ∀ (R : Machine) (real ideal : PMF (List Bool)), (Problem.decision real ideal).HardAt kb →
      (R.cost : ℝ) ≤ C * ((A.cost + D.cost : ℕ) : ℝ) ^ 2 →
      (2 : ℝ) ^ kb * (R.acceptProb real - R.acceptProb ideal) ^ 2 ≤ C * ((A.cost + D.cost : ℕ) : ℝ) ^ 2 :=
    fun R real ideal h hc => (h R).trans hc
  have ha : (1 : ℝ) ≤ ((A.cost + D.cost : ℕ) : ℝ) := by
    have := A.one_le_cost; exact_mod_cast (by omega : 1 ≤ A.cost + D.cost)
  have hg1 : g ^ 2 ≤ 1 := by
    have h1 := Machine.acceptProb_nonneg D ((PE.real dateUniverse params (impl hk c ms) A).map view)
    have h2 := Machine.acceptProb_le_one D ((PE.real dateUniverse params (impl hk c ms) A).map view)
    have h3 := Machine.acceptProb_nonneg D
      ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view)
    have h4 := Machine.acceptProb_le_one D
      ((PE.ideal dateUniverse params (impl hk c ms) (simMachine hk c) A).map view)
    nlinarith
  have := quad_loss ((2 : ℝ) ^ params.secBits) ((2 : ℝ) ^ kb) C ((A.cost + D.cost : ℕ) : ℝ)
    (statTerm c hk ε).toReal _ _ _ g (by positivity) hk64 hC ha hstat ENNReal.toReal_nonneg
    (hd R3 w3r w3u hard3 c3) (hd R5 w5r w5u hard5 c5) (hd RI wIr wIu hardI cI)
    (by linarith [hadv]) hg1
  exact_mod_cast this

end AdvancedEncryption.DualUse
