import PE.Impl.ExpLUT.Prog.KeyTimeScratch
/-! Counted movement certificates tolerate the static scratch bounds of initialization. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

theorem check_mvPc_scratch :
    check 8 ValVM.mvPc [pm, RingVM.pn', pTop, pTop, RingVM.pl']
      [pm, RingVM.pn', [], [], RingVM.pl'] RingVM.wMv = true := by decide +kernel

theorem check_dropPc_scratch :
    check 8 ValVM.dropPc [pm, pTop, RingVM.pn']
      [pm, [], RingVM.pn'] RingVM.wDr = true := by decide +kernel

theorem compile_drop_scratch (d c : Fin 64) (hdc : d ≠ c) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.drop d c)) a a
      ((2 * M + 3) * (20 + 10 * a (tR c))) := by
  let e := mkE (fDr d c) (fDr_inj hdc)
  let ρ := [M, 0, 0, a (tR d), a (tR c), 0]
  have h := frame_checked check_dropPc_scratch ρ e a a
  have hin : ∀ j : Fin 3, a (e j) ≤ pEval ρ (aGet [pm, pTop, RingVM.pn'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fDr, ofV, tR, aGet, pm, RingVM.pn', mo, pEval, mEval, pTop, hM]
  have hout : ∀ j : Fin 3,
      (if j.val < 3 then pEval ρ (aGet [pm, [], RingVM.pn'] j.val) else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fDr, ofV, tR, aGet, pm, RingVM.pn', mo, pEval, mEval]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hdc, ρ, top, List.headD_cons,
    RingVM.wDr, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

theorem compile_mvR_scratch (d s : Fin 64) (hds : d ≠ s) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.mvR d s)) a a ((2 * M + 3) * (20 + 10 * a 37)) := by
  let e := mkE (fMv d s 37) (fMv_inj hds (Or.inl rfl))
  let ρ := [M, 0, 0, a (tR s), a (tR d), a 37]
  have h := frame_checked check_mvPc_scratch ρ e a a
  have hin : ∀ j : Fin 5,
      a (e j) ≤ pEval ρ (aGet [pm, RingVM.pn', pTop, pTop, RingVM.pl'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, pTop, hM]
  have hout : ∀ j : Fin 5,
      (if j.val < 5 then pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val)
        else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hds, ρ, top, List.headD_cons,
    RingVM.wMv, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

theorem compile_mv_scratch (d s c : Fin 64) (hd : ¬(d = s ∨ d = c ∨ s = c))
    (a : Fin 105 → ℕ) (M : ℕ) (hM : ∀ t, a t ≤ M) :
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
  have h := frame_checked check_mvPc_scratch ρ e a a
  have hin : ∀ j : Fin 5,
      a (e j) ≤ pEval ρ (aGet [pm, RingVM.pn', pTop, pTop, RingVM.pl'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, pTop, hM, hmod]
  have hout : ∀ j : Fin 5,
      (if j.val < 5 then pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val)
        else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, hmod]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hd, ρ, top, List.headD_cons,
    RingVM.wMv, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

end AdvancedEncryption.ExpLUT.Prog.KeyTime
