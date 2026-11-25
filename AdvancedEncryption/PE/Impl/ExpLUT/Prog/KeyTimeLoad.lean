import PE.Impl.ExpLUT.Prog.KeyTimeChecked

/-! Input/output movement around an actual compiled MVM ring operation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

theorem checked_local {n fuel : ℕ} {p : Tape.Prog n} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) (a b : Fin n → ℕ)
    (hin : a ≤ bnd ρ σ) (hM : ∀ j, a j ≤ top ρ)
    (hout : ∀ j : Fin n, (if j.val < claim.length then pEval ρ (aGet claim j.val) else top ρ)
      ≤ b j) : Cert (.prog p) a b ((2 * top ρ + 3) * pEval ρ w) := by
  obtain ⟨hc, hu, ht⟩ := bounds_of_check h ρ hin hM
  refine ⟨?_, ht⟩
  intro j
  have ho := hout j
  split_ifs at ho with hj
  · exact (hc j hj).trans ho
  · exact (hu j).trans ho

theorem inP_cert (N K M : ℕ) (a : Fin 6 → ℕ) (hM : ∀ j, a j ≤ M)
    (hNK : a 1 = N * K) (h3 : a 3 = 0) (h4 : a 4 = 0) (h5 : a 5 = 0) :
    Cert (.prog ValVM.inP) a (Function.update a 0 (N * K))
      ((2 * M + 3) * (30 + 10 * (N * K))) := by
  let ρ := [M, N, K, a 2]
  have hi : a ≤ bnd ρ [pTop, pNK, pm, [], [], []] := by
    intro j
    fin_cases j <;> simp [bnd, aGet, ρ, pTop, pNK, pm, mo, pEval, mEval, hNK, h3, h4, h5, hM]
  have ho : ∀ j : Fin 6,
      (if j.val < 6 then pEval ρ (aGet [pNK, pNK, pm, [], [], []] j.val) else top ρ) ≤
        Function.update a 0 (N * K) j := by
    intro j
    fin_cases j <;> simp [aGet, ρ, pNK, pm, mo, pEval, mEval, hNK, h3, h4, h5]
  have h := checked_local RingVM.check_inP ρ a _ hi hM ho
  simpa [ρ, top, RingVM.wIn, pEval, mEval, Nat.mul_assoc] using h

/-- Loading either operand resets only its operation-area tape to NK. -/
theorem load_cert (N K M : ℕ) (x : ℕ) (hx : x = 33 ∨ x = 34) (s : Fin 64)
    (a : Fin 105 → ℕ) (hM : ∀ t, a t ≤ M) (hNK : a 37 = N * K)
    (hz32 : a 32 = 0) (hz39 : a 39 = 0) (hz40 : a 40 = 0) :
    let e := mkE (fLd x s) (fLd_inj x hx s)
    Cert (.frame e (.prog ValVM.inP)) a (Function.update a (e 0) (N * K))
      ((2 * M + 3) * (30 + 10 * (N * K))) := by
  dsimp only
  let e := mkE (fLd x s) (fLd_inj x hx s)
  have h := (inP_cert N K M (a ∘ e) (fun j ↦ hM _) hNK hz32 hz39 hz40).frame e
  rw [embedF_update_bound] at h
  exact h

theorem check_outQ : check 8 outQ [pm, pTop, pNK, pTop] [pNK, [], [], []] (pC 20) = true := by
  decide +kernel

/-- The actual MVM output macro copies the canonical result and clears its work words. -/
theorem outQ_cert (N K M : ℕ) (a : Fin 4 → ℕ) (hM : ∀ j, a j ≤ M)
    (hNK : a 2 ≤ N * K) :
    Cert (.prog outQ) a (fun j ↦ if j = 0 then N * K else 0) ((2 * M + 3) * 20) := by
  let ρ := [M, N, K, a 0]
  have hi : a ≤ bnd ρ [pm, pTop, pNK, pTop] := by
    intro j
    fin_cases j <;> simp [bnd, aGet, ρ, pTop, pNK, pm, mo, pEval, mEval, hNK, hM]
  have ho : ∀ j : Fin 4,
      (if j.val < 4 then pEval ρ (aGet [pNK, [], [], []] j.val) else top ρ) ≤
        (if j = 0 then N * K else 0) := by
    intro j
    fin_cases j <;> simp [aGet, ρ, pNK, mo, pEval, mEval]
  have h := checked_local check_outQ ρ a _ hi hM ho
  simpa [ρ, top] using h

/-- The result is written using the actual destination/X0/X1/X2 tape embedding. -/
theorem store_cert (N K M : ℕ) (d : Fin 64) (a : Fin 105 → ℕ)
    (hM : ∀ t, a t ≤ M) (hNK : a 33 ≤ N * K) :
    let e := mkE (fOut d) (fOut_inj d)
    Cert (.frame e (.prog outQ)) a
      (embedF e a (fun j ↦ if j = 0 then N * K else 0)) ((2 * M + 3) * 20) := by
  dsimp only
  let e := mkE (fOut d) (fOut_inj d)
  exact (outQ_cert N K M (a ∘ e) (fun j ↦ hM _) hNK).frame e

end AdvancedEncryption.ExpLUT.Prog.KeyTime
