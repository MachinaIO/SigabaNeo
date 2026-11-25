import PE.Impl.ExpLUT.Prog.KeyTimeMoves
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMCert
/-! Apply existing primitive certificates to the actual MVM layouts. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym

/-- A checked primitive, with every framed and unframed output bound explicit. -/
theorem frame_checked {k n fuel : ℕ} {p : Tape.Prog n} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) (e : Fin n ↪ Fin k)
    (a b : Fin k → ℕ)
    (hin : ∀ j, a (e j) ≤ pEval ρ (aGet σ j.val)) (hM : ∀ j, a (e j) ≤ top ρ)
    (hout : ∀ j : Fin n, (if j.val < claim.length then pEval ρ (aGet claim j.val) else top ρ)
      ≤ b (e j)) (hrest : ∀ t, (∀ j, e j ≠ t) → a t ≤ b t) :
    Cert (.frame e (.prog p)) a b ((2 * top ρ + 3) * pEval ρ w) := by
  obtain ⟨ht, hc, hu, hr⟩ := RingVM.frame_of_check' h ρ e hin hM
  refine ⟨?_, ht⟩
  intro t
  by_cases he : ∃ j, e j = t
  · obtain ⟨j, rfl⟩ := he
    have ho := hout j
    split_ifs at ho with hj
    · exact (hc j hj).trans ho
    · exact (hu j).trans ho
  · push Not at he
    exact (hr t he).le.trans (hrest t he)

open Prog.SpecT

/-- Dropping a counted prefix preserves the register length upper bounds. -/
theorem compile_drop_cert (d c : Fin 64) (hdc : d ≠ c) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) (hz : a 39 = 0) :
    Cert (MVM.compile (.drop d c)) a a
      ((2 * M + 3) * (20 + 10 * a (tR c))) := by
  let e := mkE (fDr d c) (fDr_inj hdc)
  let ρ := [M, 0, 0, a (tR d), a (tR c), 0]
  have h := frame_checked RingVM.check_dropPc ρ e a a
  have hin : ∀ j : Fin 3, a (e j) ≤ pEval ρ (aGet [pm, [], RingVM.pn'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fDr, ofV, tR, aGet, pm, RingVM.pn', mo, pEval, mEval, hz]
  have hout : ∀ j : Fin 3,
      (if j.val < 3 then pEval ρ (aGet [pm, [], RingVM.pn'] j.val) else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fDr, ofV, tR, aGet, pm, RingVM.pn', mo, pEval, mEval, hz]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hdc, ρ, top, List.headD_cons,
    RingVM.wDr, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

/-- Moving one ring word uses the actual NK counter on tape37. -/
theorem compile_mvR_cert (d s : Fin 64) (hds : d ≠ s) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) (hz39 : a 39 = 0) (hz40 : a 40 = 0) :
    Cert (MVM.compile (.mvR d s)) a a ((2 * M + 3) * (20 + 10 * a 37)) := by
  let e := mkE (fMv d s 37) (fMv_inj hds (Or.inl rfl))
  let ρ := [M, 0, 0, a (tR s), a (tR d), a 37]
  have h := frame_checked RingVM.check_mvPc ρ e a a
  have hin : ∀ j : Fin 5,
      a (e j) ≤ pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, hz39, hz40]
  have hout : ∀ j : Fin 5,
      (if j.val < 5 then pEval ρ (aGet [pm, RingVM.pn', [], [], RingVM.pl'] j.val)
        else top ρ) ≤ a (e j) := by
    intro j
    fin_cases j <;> simp [e, ρ, mkE, fMv, ofV, tR, aGet, pm, RingVM.pn', RingVM.pl',
      mo, pEval, mEval, hz39, hz40]
  have hh := h hin (fun j ↦ hM (e j)) hout (fun _ _ ↦ le_rfl)
  simpa only [MVM.compile, dite_eq_right hds, ρ, top, List.headD_cons,
    RingVM.wMv, pEval, mEval, List.headD_nil, List.tail_cons, List.tail_nil,
    Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.mul_one, Nat.add_zero] using hh

end AdvancedEncryption.ExpLUT.Prog.KeyTime
