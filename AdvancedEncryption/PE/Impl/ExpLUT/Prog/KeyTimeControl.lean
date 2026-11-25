import PE.Impl.ExpLUT.Prog.KeyTimeOpInvariant
/-! Remaining control and counted-move primitive certificates. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

theorem nopX_cert (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert nopX a a (2 * (M + 1) + 3) := by
  let e := mkE (f1 tX0) (f1_inj _)
  have h := (Cert.ofVB (XProg.VB.prim (.copy (0 : Fin 1) 0)
    (fun j ↦ hM (e j)))).frame e
  change Cert nopX a (embedF e a (Function.update (a ∘ e) 0 (a (e 0)))) _ at h
  rw [embedF_update_bound, Function.update_eq_self] at h
  exact h

theorem compile_eqb_cert (f s t : Fin 64) (hd : ¬(f = s ∨ f = t ∨ s = t))
    (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ j, a j ≤ M) :
    Cert (MVM.compile (.eqb f s t)) a (Function.update a (tR f) 1) (2 * (M + 1) + 3) := by
  let e := mkE (fEq f s t) (fEq_inj hd)
  have h := (Cert.ofVB (XProg.VB.prim (.eq (0 : Fin 3) 1 2)
    (fun j ↦ hM (e j)))).frame e
  change Cert (.frame e (.prog (.prim (.eq 0 1 2)))) a
    (embedF e a (Function.update (a ∘ e) 2 1)) _ at h
  rw [embedF_update_bound] at h
  have he : e 2 = tR f := by apply Fin.ext; rfl
  rw [he] at h
  simpa only [MVM.compile, dite_eq_right hd] using h

theorem compile_mv_cert (d s c : Fin 64) (hd : ¬(d = s ∨ d = c ∨ s = c))
    (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ t, a t ≤ M) (hz39 : a 39 = 0) (hz40 : a 40 = 0) :
    Cert (MVM.compile (.mv d s c)) a a ((2 * M + 3) * (20 + 10 * a (tR c))) := by
  have hds : d ≠ s := fun h ↦ hd (Or.inl h)
  have hdc : d ≠ c := fun h ↦ hd (Or.inr (Or.inl h))
  have hsc : s ≠ c := fun h ↦ hd (Or.inr (Or.inr h))
  have hc : 41 ≤ 41 + c.val ∧ 41 + c.val < 105 ∧
      41 + c.val ≠ 41 + d.val ∧ 41 + c.val ≠ 41 + s.val := by
    have := c.isLt
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro he; exact hdc (Fin.ext (by omega))
    · intro he; exact hsc (Fin.ext (by omega))
  let e := mkE (fMv d s (41 + c.val)) (fMv_inj hds (Or.inr hc))
  let ρ := [M, 0, 0, a (tR s), a (tR d), a (tR c)]
  have hmod : (41 + c.val) % 105 = 41 + c.val := Nat.mod_eq_of_lt hc.2.1
  have h := frame_checked RingVM.check_mvPc ρ e a a
  have hin : ∀ j : Fin 5,
      a (e j) ≤ pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, hz39, hz40, hmod]
  have hout : ∀ j : Fin 5,
      (if j.val < 5 then pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val)
        else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, hz39, hz40, hmod]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hd, ρ, top, List.headD_cons,
    RingVM.wMv, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

theorem compile_cp_any (d s : Fin 64) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.cp d s)) a (Function.update a (tR d) (a (tR s)))
      (2 * (M + 1) + 3) := by
  by_cases hds : d = s
  · subst s
    simpa only [MVM.compile, dite_eq_left rfl, ↓reduceDIte, Function.update_eq_self] using nopX_cert a M hM
  · exact compile_cp_cert d s hds a M hM

theorem compile_drop_self (d : Fin 64) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) : Cert (MVM.compile (.drop d d)) a a (2 * (M + 1) + 3) := by
  simpa only [MVM.compile, dite_eq_left rfl, ↓reduceDIte] using nopX_cert a M hM

theorem compile_mvR_self (d : Fin 64) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) : Cert (MVM.compile (.mvR d d)) a a (2 * (M + 1) + 3) := by
  simpa only [MVM.compile, dite_eq_left rfl, ↓reduceDIte] using nopX_cert a M hM

theorem compile_mv_overlap (d s c : Fin 64) (hd : d = s ∨ d = c ∨ s = c)
    (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.mv d s c)) a a (2 * (M + 1) + 3) := by
  simpa only [MVM.compile, dite_eq_left hd] using nopX_cert a M hM

theorem compile_eqb_overlap (f s t : Fin 64) (hd : f = s ∨ f = t ∨ s = t)
    (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ j, a j ≤ M) :
    Cert (MVM.compile (.eqb f s t)) a a (2 * (M + 1) + 3) := by
  simpa only [MVM.compile, dite_eq_left hd] using nopX_cert a M hM

theorem compile_nop (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile .nop) a a (2 * (M + 1) + 3) := nopX_cert a M hM

end AdvancedEncryption.ExpLUT.Prog.KeyTime
