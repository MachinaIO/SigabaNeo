import PE.Impl.Game.Generic

/-!
# A statistical change of the secret, without the union over attributes

The secret is drawn once, at the selection of the attribute. If the law of the secret moves by at
most `ε` for every attribute, the experiment moves by at most `ε` (`closeTo_runWith_setup_one`):
before the selection the two experiments are identical, the selection is one draw `ε`-close, and
after it the two challengers answer identically (`runWith_eq_of_selected`). This improves
`Generic.closeTo_runWith_setup` (which pays `∑ x, ε x`, a union over all attributes) when the
attribute universe is large.
-/

namespace AdvancedEncryption.PE.Generic

open SigabaNeo Cslib Cslib.Probability
open scoped ENNReal

variable {U : Universe} {Sig : Type} (sp : Spec U Sig) (V' : U.Attr → PMF Sig)

/-- After the selection the two challengers answer identically. -/
theorem runWith_eq_of_selected {α : Type}
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ∀ s : GState U Sig, s.attr.isSome →
      ProbOracleComp.runWith (oracle sp) program s =
        ProbOracleComp.runWith (oracle { sp with setup := V' }) program s := by
  induction program using ProbOracleComp.induction with
  | pure a => intro s _; simp
  | sample_bind n cont ih =>
    intro s hs
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map]
    exact congrArg (PMF.bind _) (funext fun i => ih i s hs)
  | query_bind q cont ih =>
    intro s hs
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    have hq : oracle sp q s = oracle { sp with setup := V' } q s := by
      by_cases hsel : q.1 = selectOp
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
        rcases s with ⟨attr, sec, msg, bad⟩
        simp only at hx
        subst hx
        simp [oracle, oracleWith, hsel]
      · exact oracleWith_of_ne sp q hsel s
    rw [← hq]
    refine PMF.bind_congr_on_support _ _ _ fun r hr => ih r.1 r.2 ?_
    by_cases hsel : q.1 = selectOp
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
      rcases s with ⟨attr, sec, msg, bad⟩
      simp only at hx
      subst hx
      simp only [oracle, oracleWith, hsel, if_true, PMF.mem_support_pure_iff] at hr
      rw [hr]; rfl
    · rw [(oracleWith_keep sp q hsel s r hr).1]; exact hs

/-- **A statistical change of the secret costs its distance once.** -/
theorem closeTo_runWith_setup_one {α : Type} {ε : ℝ≥0∞} (h : ∀ x, CloseTo (sp.setup x) (V' x) ε)
    (program : ProbOracleComp (fun _ : Fin 3 × List Bool => List Bool) α) :
    ∀ s : GState U Sig, CloseTo (ProbOracleComp.runWith (oracle sp) program s)
      (ProbOracleComp.runWith (oracle { sp with setup := V' }) program s) ε := by
  induction program using ProbOracleComp.induction with
  | pure a => intro s; simpa using (CloseTo.refl (PMF.pure (a, s))).mono (zero_le (a := ε))
  | sample_bind n cont ih =>
    intro s
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map]
    exact CloseTo.bind_right _ fun i _ => ih i s
  | query_bind q cont ih =>
    intro s
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    by_cases hsel : q.1 = selectOp
    · rcases s with ⟨attr, sec, msg, bad⟩
      rcases attr with _ | x₀
      · rcases hd : decode U.encAttr q.2 with _ | x
        · simp only [oracle, oracleWith, hsel, if_true, hd, PMF.pure_bind]
          exact ih [] _
        · simp only [oracle, oracleWith, hsel, if_true, hd]
          have h2 := (h x).map fun σ => (sp.pub σ,
            ({ attr := some x, sec := some σ, msg := msg, bad := bad } : GState U Sig))
          have e := (h2.bind (g := fun r => ProbOracleComp.runWith
              (oracle { sp with setup := V' }) (cont r.1) r.2)
            (f := fun r => ProbOracleComp.runWith (oracle sp) (cont r.1) r.2)
            (δ := 0) fun r hr => by
              obtain ⟨σ, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
              rw [runWith_eq_of_selected sp V' (cont _) _ rfl]
              exact CloseTo.refl _)
          rw [add_zero] at e
          exact e
      · simp only [oracle, oracleWith, hsel, if_true, PMF.pure_bind]
        exact ih [] _
    · rw [show oracle { sp with setup := V' } q s = oracle sp q s from
        (oracleWith_of_ne sp q hsel s).symm]
      exact CloseTo.bind_right _ fun r _ => ih r.1 r.2

end AdvancedEncryption.PE.Generic
