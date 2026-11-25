import PE.Impl.ExpLUT.Prog.KeyTimeAppend

/-! Operand loading tolerates nonzero static bounds on its scratch tapes. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

theorem check_inP_scratch :
    check 8 ValVM.inP [pTop, pNK, pm, pTop, pTop, pTop]
      [pNK, pNK, pm, [], [], []] RingVM.wIn = true := by decide +kernel

theorem inP_scratch_cert (N K M : ℕ) (a : Fin 6 → ℕ) (hM : ∀ j, a j ≤ M)
    (hNK : a 1 = N * K) :
    Cert (.prog ValVM.inP) a
      (fun j ↦ if j = 0 ∨ j = 1 then N * K else if j = 2 then a 2 else 0)
      ((2 * M + 3) * (30 + 10 * (N * K))) := by
  let ρ := [M, N, K, a 2]
  have hi : a ≤ bnd ρ [pTop, pNK, pm, pTop, pTop, pTop] := by
    intro j
    fin_cases j <;> simp [bnd, aGet, ρ, pTop, pNK, pm, mo, pEval, mEval, hNK, hM]
  have ho : ∀ j : Fin 6,
      (if j.val < 6 then pEval ρ (aGet [pNK, pNK, pm, [], [], []] j.val) else top ρ) ≤
        (if j = 0 ∨ j = 1 then N * K else if j = 2 then a 2 else 0) := by
    intro j
    fin_cases j <;> simp [aGet, ρ, pNK, pm, mo, pEval, mEval]
  have h := checked_local check_inP_scratch ρ a _ hi hM ho
  simpa [ρ, top, RingVM.wIn, pEval, mEval, Nat.mul_assoc] using h

/-- Actual operand-load frame, with no blank-scratch premise. -/
theorem load_scratch_cert (N K M : ℕ) (x : ℕ) (hx : x = 33 ∨ x = 34) (s : Fin 64)
    (a : Fin 105 → ℕ) (hM : ∀ t, a t ≤ M) (hNK : a 37 = N * K) :
    let e := mkE (fLd x s) (fLd_inj x hx s)
    Cert (.frame e (.prog ValVM.inP)) a
      (embedF e a (fun j ↦ if j = 0 ∨ j = 1 then N * K
        else if j = 2 then a (e 2) else 0))
      ((2 * M + 3) * (30 + 10 * (N * K))) := by
  dsimp only
  let e := mkE (fLd x s) (fLd_inj x hx s)
  exact (inP_scratch_cert N K M (a ∘ e) (fun j ↦ hM (e j)) hNK).frame e

end AdvancedEncryption.ExpLUT.Prog.KeyTime
