import PE.Impl.Game.Generic

/-!
# Identical until bad

Two challengers whose answers to a key query `C` may differ only when `C` is authorized for the
selected attribute — the query that raises the flag `bad` — give every run that ends with
`bad = false` the same probability (`runWith_until_bad`). The flag never goes down
(`bad_sticky`).
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib Cslib.Probability

variable {U : Universe} {Sig : Type}

/-- **The flag never goes down.** -/
theorem bad_sticky {α : Type} (sp : Spec U Sig)
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) (s : GState U Sig)
    (hs : s.bad = true) : ∀ r ∈ (ProbOracleComp.runWith (oracle sp) program s).support,
      r.2.bad = true := by
  intro r hr
  refine ProbOracleComp.runWith_invariant (oracle sp) (fun s => s.bad = true) ?_ program s hs
    r.1 r.2 hr
  intro q s hs a s' h
  rcases s with ⟨attr, sec, msg, bad⟩
  simp only at hs
  subst hs
  unfold oracle oracleWith at h
  split_ifs at h with hq hk
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨σ, -, he⟩ := h; cases he; rfl
    · rw [PMF.mem_support_pure_iff] at h; cases h; rfl
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨sk, -, he⟩ := h; cases he; simp
    · rw [PMF.mem_support_pure_iff] at h; cases h; rfl
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨ct, -, he⟩ := h; cases he; rfl
    · rw [PMF.mem_support_pure_iff] at h; cases h; rfl

/-- The answers keep the secret in the support of its law. -/
theorem inSupport_step (sp : Spec U Sig) (q : Fin 3 × List Bool) (s : GState U Sig)
    (hs : InSupport sp s) (a : List Bool) (s' : GState U Sig)
    (h : (a, s') ∈ (oracle sp q s).support) : InSupport sp s' := by
  rcases s with ⟨attr, sec, msg, bad⟩
  unfold oracle oracleWith at h
  split_ifs at h with hq hk
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨σ, hσ, he⟩ := h
      cases he
      rename_i x _ _
      intro σ' hσ'
      simp only [Option.some.injEq] at hσ'
      subst hσ'
      exact ⟨x, rfl, hσ⟩
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨sk, -, he⟩ := h; cases he; exact hs
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs
  · split at h
    · rw [PMF.mem_support_map_iff] at h
      obtain ⟨ct, -, he⟩ := h; cases he; exact hs
    · rw [PMF.mem_support_pure_iff] at h; cases h; exact hs

variable (sp sp' : Spec U Sig) (hsetup : sp'.setup = sp.setup) (hpub : sp'.pub = sp.pub)
  (hchal : sp'.chal = sp.chal) (hauth : sp'.auth = sp.auth)
  (hkey : ∀ x, ∀ σ ∈ (sp.setup x).support, ∀ C, sp.auth C x = false → sp'.key σ C = sp.key σ C)

include hsetup hpub hchal hauth hkey in
/-- One answer: the two challengers agree on the answers that keep `bad` down. -/
theorem until_bad_step (q : Fin 3 × List Bool) (s : GState U Sig) (hs : InSupport sp s)
    (b : List Bool) (s₁ : GState U Sig) (hb : s₁.bad = false) :
    oracle sp' q s (b, s₁) = oracle sp q s (b, s₁) := by
  rcases s with ⟨attr, sec, msg, bad⟩
  by_cases hq : q.1 = selectOp
  · simp only [oracle, oracleWith, hq, if_true, hsetup, hpub]
  · by_cases hk : q.1 = keyGenOp
    · rcases attr with _ | x
      · simp [oracle, oracleWith, hq, hk, selectOp, keyGenOp]
      · rcases sec with _ | σ
        · simp [oracle, oracleWith, hq, hk, selectOp, keyGenOp]
        · obtain ⟨y, hy, hσ⟩ := hs σ rfl
          simp only [Option.some.injEq] at hy
          subst hy
          simp only [oracle, oracleWith, hq, hk, if_false, if_true, hauth,
            show (keyGenOp : Fin 3) ≠ selectOp by decide, ite_false]
          by_cases ha : sp.auth q.2 x = true
          · -- the query raises the flag: no outcome keeps it down
            rw [PMF.map_apply, PMF.map_apply]
            rw [tsum_eq_zero_iff.mpr, tsum_eq_zero_iff.mpr]
            · intro sk; rw [if_neg]; intro h; simp only [Prod.mk.injEq] at h; rw [h.2] at hb; simp [ha] at hb
            · intro sk; rw [if_neg]; intro h; simp only [Prod.mk.injEq] at h; rw [h.2] at hb; simp [ha] at hb
          · rw [hkey x σ hσ q.2 (by simpa using ha)]
    · simp only [oracle, oracleWith, hq, hk, if_false, hchal]

include hsetup hpub hchal hauth hkey in
/-- **Identical until bad**: every run ending with `bad = false` has the same probability. -/
theorem runWith_until_bad {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ∀ (s : GState U Sig), InSupport sp s → ∀ (a : α) (s' : GState U Sig), s'.bad = false →
      ProbOracleComp.runWith (oracle sp') program s (a, s') =
        ProbOracleComp.runWith (oracle sp) program s (a, s') := by
  induction program using ProbOracleComp.induction with
  | pure b => intro s _ a s' _; rfl
  | sample_bind n cont ih =>
    intro s hs a s' hb
    simp only [ProbOracleComp.runWith_sample_bind, PMF.bind_apply]
    exact tsum_congr fun i => by rw [ih i s hs a s' hb]
  | query_bind q cont ih =>
    intro s hs a s' hb
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, PMF.bind_apply]
    refine tsum_congr fun r => ?_
    by_cases hr : r.2.bad = true
    · -- the flag is up: the run cannot end with it down
      have h0 : ∀ sp'' : Spec U Sig,
          ProbOracleComp.runWith (oracle sp'') (cont r.1) r.2 (a, s') = 0 := fun sp'' => by
        rw [PMF.apply_eq_zero_iff]
        intro hmem
        have := bad_sticky sp'' (cont r.1) r.2 hr _ hmem
        simp [hb] at this
      rw [h0 sp', h0 sp, mul_zero, mul_zero]
    · have hr' : r.2.bad = false := by simpa using hr
      rw [until_bad_step sp sp' hsetup hpub hchal hauth hkey q s hs r.1 r.2 hr']
      by_cases hpos : oracle sp q s r = 0
      · rw [hpos, zero_mul, zero_mul]
      · congr 1
        have hmem : r ∈ (oracle sp q s).support := (PMF.mem_support_iff _ _).mpr hpos
        have hinv : InSupport sp r.2 := inSupport_step sp q s hs r.1 r.2 hmem
        exact ih r.1 r.2 hinv a s' hb

include hsetup hpub hchal hauth hkey in
/-- The observable outcomes with the flag down have the same probability. -/
theorem obs_until_bad {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α)
    (o : α × Option U.Attr × Option U.Msg × Bool) (ho : o.2.2.2 = false) :
    (ProbOracleComp.runWith (oracle sp') program ({} : GState U Sig)).map obs o =
      (ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig)).map obs o := by
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun r => ?_
  split_ifs with h
  · have hb : r.2.bad = false := by rw [h] at ho; exact ho
    exact runWith_until_bad sp sp' hsetup hpub hchal hauth hkey program {}
      (fun σ hσ => by simp at hσ) r.1 r.2 hb
  · rfl

/-- The probability that the flag is up. -/
noncomputable def pBad {α : Type} (μ : PMF (α × Option U.Attr × Option U.Msg × Bool)) : ENNReal :=
  μ.toOuterMeasure {o | o.2.2.2 = true}

open scoped ENNReal in
/-- Two laws that agree on the outcomes with the flag down are within the probability of the flag. -/
theorem closeTo_of_agree_good {α : Type} {μ ν : PMF (α × Option U.Attr × Option U.Msg × Bool)}
    (h : ∀ o, o.2.2.2 = false → μ o = ν o) : CloseTo μ ν (pBad ν) := by
  intro E
  classical
  set good : Set (α × Option U.Attr × Option U.Msg × Bool) := {o | o.2.2.2 = false}
  set bad : Set (α × Option U.Attr × Option U.Msg × Bool) := {o | o.2.2.2 = true}
  -- the probabilities of the flag agree
  have hsum : ∀ ρ : PMF (α × Option U.Attr × Option U.Msg × Bool),
      ρ.toOuterMeasure good + ρ.toOuterMeasure bad = 1 := by
    intro ρ
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    rw [← ρ.tsum_coe]
    refine tsum_congr fun o => ?_
    by_cases hb : o.2.2.2 = true
    · simp [good, bad, Set.indicator, hb]
    · simp [good, bad, Set.indicator, hb]
  have hgood : μ.toOuterMeasure good = ν.toOuterMeasure good := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun o => ?_
    by_cases hb : o.2.2.2 = false
    · simp [good, Set.indicator, hb, h o hb]
    · simp [good, Set.indicator, hb]
  have hbad : μ.toOuterMeasure bad = ν.toOuterMeasure bad := by
    have h1 := hsum μ
    have h2 := hsum ν
    rw [hgood] at h1
    exact (ENNReal.add_right_inj (ne_top_of_le_ne_top ENNReal.one_ne_top
      (h2 ▸ le_self_add))).mp (h1.trans h2.symm)
  -- split the event
  have hE : μ.toOuterMeasure E ≤ μ.toOuterMeasure (E ∩ good) + μ.toOuterMeasure bad := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
      ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases hb : o.2.2.2 = true
    · by_cases hoE : o ∈ E <;> simp [good, bad, Set.indicator, hb, hoE]
    · have hb' : o.2.2.2 = false := by simpa using hb
      by_cases hoE : o ∈ E <;> simp [good, bad, Set.indicator, hb', hoE]
  have hEg : μ.toOuterMeasure (E ∩ good) = ν.toOuterMeasure (E ∩ good) := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun o => ?_
    by_cases hb : o.2.2.2 = false
    · simp [good, Set.indicator, hb, h o hb]
    · simp [good, Set.indicator, hb]
  calc μ.toOuterMeasure E ≤ μ.toOuterMeasure (E ∩ good) + μ.toOuterMeasure bad := hE
    _ = ν.toOuterMeasure (E ∩ good) + ν.toOuterMeasure bad := by rw [hEg, hbad]
    _ ≤ ν.toOuterMeasure E + pBad ν := by
      gcongr
      exact Set.inter_subset_left

include hsetup hpub hchal hauth hkey in
/-- **Identical until bad, observably**: the two experiments are within the probability of the
flag in the second. -/
theorem closeTo_until_bad {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    CloseTo ((ProbOracleComp.runWith (oracle sp') program ({} : GState U Sig)).map obs)
      ((ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig)).map obs)
      (pBad ((ProbOracleComp.runWith (oracle sp) program ({} : GState U Sig)).map obs)) :=
  closeTo_of_agree_good fun o ho => obs_until_bad sp sp' hsetup hpub hchal hauth hkey program o ho

end AdvancedEncryption.PE.Generic
