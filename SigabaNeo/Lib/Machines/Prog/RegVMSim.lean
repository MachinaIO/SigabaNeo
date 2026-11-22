import SigabaNeo.Lib.Machines.Prog.RegVMRun

/-!
# The register machine on tapes: the compiler

`compile c j : Prog K` compiles a code whose loops start at depth `j` (the counter of the loop at
depth `j` is the tape `tC j`). **`run_compile`**: from the encoding of a state satisfying the list
invariant `Inv`, with blank counters from depth `j` on, the compiled program ends in the encoding of
`exec E c σ`. **`law_compile`**: its law is the point mass there. The compiled programs are in the
fragment `NoGrow` (`noGrow_compile`) and well formed (`wf_compile`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Tape

namespace RegVM

open Prog
open scoped Prog

/-- The counter tape of depth `j`. -/
def tCd (j : ℕ) : Fin K := tC ⟨j % nD, Nat.mod_lt _ (by decide)⟩

/-- **The compiler.** -/
def compile : Code → ℕ → Prog K
  | .nand d a b, _ => nandP d a b
  | .one d, _ => oneP d
  | .zero d, _ => zeroP d
  | .mov d a, _ => movP d a
  | .inc d, _ => incP d
  | .add d a, _ => addP d a
  | .sub d a, _ => subP d a
  | .lnil l, _ => lnilP l
  | .lpush l a, _ => lpushP l a
  | .lpop d l, _ => lpopP d l
  | .lmov l l', _ => lmovP l l'
  | .rdsrc d, _ => rdsrcP d
  | .skip, _ => nop X0
  | .seq p q, j => compile p j ⨾ compile q j
  | .ifLt a b p q, j => ltTestP a b ⨾ ifBlank X0 (clr X0 ⨾ compile q j) (clr X0 ⨾ compile p j)
  | .rep a body, j => cp (tCd j) (tR a) ⨾ loop (tCd j) (compile body (j + 1))

variable (E : Env)

/-- **The invariant is kept.** -/
theorem inv_exec : ∀ (c : Code) (σ : St), Inv E σ → Inv E (exec E c σ)
  | .nand _ _ _, _, h | .one _, _, h | .zero _, _, h | .mov _ _, _, h | .inc _, _, h
  | .add _ _, _, h | .sub _ _, _, h | .skip, _, h => h
  | .lnil l, σ, h => ⟨fun l' => by
      by_cases hl : l' = l
      · subst hl; simp [exec]
      · simp only [exec, Function.update_of_ne hl]; exact h.1 l', h.2⟩
  | .lmov l l', σ, h => ⟨fun l'' => by
      by_cases hl : l'' = l
      · subst hl; simp only [exec, Function.update_self]; exact h.1 l'
      · simp only [exec, Function.update_of_ne hl]; exact h.1 l'', h.2⟩
  | .lpush l a, σ, h => ⟨fun l' => by
      by_cases hl : l' = l
      · subst hl
        simp only [exec, Function.update_self]
        split_ifs with hc
        · refine ⟨by simp; omega, fun x hx => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact (h.1 l').2 x hx
          · exact min_le_right _ _
        · exact h.1 l'
      · simp only [exec, Function.update_of_ne hl]; exact h.1 l', h.2⟩
  | .lpop d l, σ, h => ⟨fun l' => by
      by_cases hl : l' = l
      · subst hl
        simp only [exec, Function.update_self]
        exact ⟨by have := (h.1 l').1; simp; omega, fun x hx => (h.1 l').2 x (List.mem_of_mem_tail hx)⟩
      · simp only [exec, Function.update_of_ne hl]; exact h.1 l', h.2⟩
  | .rdsrc d, σ, h => ⟨h.1, fun x hx => h.2 x (List.mem_of_mem_tail hx)⟩
  | .seq p q, σ, h => inv_exec q _ (inv_exec p σ h)
  | .ifLt a b p q, σ, h => by
      simp only [exec]; split_ifs
      · exact inv_exec p σ h
      · exact inv_exec q σ h
  | .rep a body, σ, h => by
      simp only [exec]
      generalize σ.sc a = m
      induction m generalizing σ with
      | zero => exact h
      | succ m ih => rw [Function.iterate_succ_apply]; exact ih _ (inv_exec body σ h)

/-- **The compiled program computes the semantics.** -/
theorem run_compile (hWM : E.W ≤ E.M) : ∀ (c : Code) (j : ℕ), j + depth c ≤ nD → ∀ (σ : St),
    Inv E σ → ∀ (ctr : Fin nD → List Bool), (∀ i : Fin nD, j ≤ i.val → ctr i = []) →
      run (compile c j) (enc E σ ctr) = enc E (exec E c σ) ctr
  | .nand d a b, _, _, σ, _, ctr, _ => run_nandP E σ ctr d a b
  | .one d, _, _, σ, _, ctr, _ => run_oneP E σ ctr d
  | .zero d, _, _, σ, _, ctr, _ => run_zeroP E σ ctr d
  | .mov d a, _, _, σ, _, ctr, _ => run_movP E σ ctr d a
  | .inc d, _, _, σ, _, ctr, _ => run_incP E σ ctr d
  | .add d a, _, _, σ, _, ctr, _ => run_addP E σ ctr d a
  | .sub d a, _, _, σ, _, ctr, _ => run_subP E σ ctr d a
  | .lnil l, _, _, σ, hI, ctr, _ => run_lnilP E σ ctr hI l
  | .lpush l a, _, _, σ, hI, ctr, _ => run_lpushP E σ ctr hI l a
  | .lpop d l, _, _, σ, hI, ctr, _ => run_lpopP E σ ctr hI d l
  | .lmov l l', _, _, σ, _, ctr, _ => run_lmovP E σ ctr l l'
  | .rdsrc d, _, _, σ, hI, ctr, _ => run_rdsrcP E σ ctr hI hWM d
  | .skip, _, _, σ, _, ctr, _ => by simp [compile, exec]
  | .seq p q, j, hd, σ, hI, ctr, hc => by
      simp only [depth] at hd
      rw [compile, run_seq, run_compile hWM p j (by omega) σ hI ctr hc,
        run_compile hWM q j (by omega) _ (inv_exec E p σ hI) ctr hc]; rfl
  | .ifLt a b p q, j, hd, σ, hI, ctr, hc => by
      simp only [depth] at hd
      rw [compile, run_seq, run_ltTestP, run_ifBlank, Function.update_self]
      simp only [exec]
      by_cases hab : σ.sc a < σ.sc b
      · rw [if_neg (by simp; omega), if_pos hab, run_seq, run_clear, Function.update_idem,
          enc_upd_X, run_compile hWM p j (by omega) σ hI ctr hc]
      · rw [if_pos (by simp; omega), if_neg hab, run_seq, run_clear, Function.update_idem,
          enc_upd_X, run_compile hWM q j (by omega) σ hI ctr hc]
  | .rep a body, j, hd, σ, hI, ctr, hc => by
      simp only [depth] at hd
      have hj : j % nD = j := Nat.mod_eq_of_lt (by omega)
      set jj : Fin nD := ⟨j % nD, Nat.mod_lt _ (by decide)⟩ with hjj
      have hjj' : jj.val = j := hj
      have hcj : ctr jj = [] := hc jj (by omega)
      rw [compile, run_seq, run_copy, enc_R]
      have e0 : Function.update (enc E σ ctr) (tCd j) (List.replicate (σ.sc a) true) =
          Function.update (enc E σ ctr) (tCd j) (List.replicate (σ.sc a) true) := rfl
      have key := run_loop_iter (tCd j) (compile body (j + 1)) (fun τ => enc E τ ctr) (exec E body)
        (Inv E) (fun τ w hτ => by
          simp only [tCd]
          rw [← enc_ctr, run_compile hWM body (j + 1) (by omega) τ hτ _ (fun i hi => by
            rw [Function.update_of_ne (fun h => by subst h; omega)]; exact hc i (by omega)),
            enc_ctr])
        (fun τ hτ => inv_exec E body τ hτ) (List.replicate (σ.sc a) true) σ hI
      rw [key, List.length_replicate]
      simp only [exec, tCd]
      rw [Function.update_eq_self_iff, enc_C]
      exact hcj.symm

/-! ### The fragment -/

theorem noGrow_compile : ∀ (c : Code) (j : ℕ), (compile c j).NoGrow
  | .nand _ _ _, _ | .one _, _ | .zero _, _ | .mov _ _, _ | .inc _, _ | .add _ _, _
  | .sub _ _, _ | .lnil _, _ | .lpush _ _, _ | .lpop _ _, _ | .lmov _ _, _ | .rdsrc _, _
  | .skip, _ => rfl
  | .seq p q, j => by
      simp only [NoGrow, compile, noGrowB, Bool.and_eq_true]
      exact ⟨noGrow_compile p j, noGrow_compile q j⟩
  | .ifLt a b p q, j => by
      have hp := noGrow_compile p j
      have hq := noGrow_compile q j
      simp only [NoGrow] at hp hq
      simp [NoGrow, compile, noGrowB, hp, hq, ltTestP, dropBy, Prim.noGrowB]
  | .rep a body, j => by
      simp only [NoGrow, compile, noGrowB, Bool.and_eq_true]
      exact ⟨rfl, noGrow_compile body (j + 1)⟩

/-- **The law of the compiled program** is the point mass at the encoded semantics. -/
theorem law_compile (hWM : E.W ≤ E.M) (c : Code) (j : ℕ) (hd : j + depth c ≤ nD) (σ : St)
    (hI : Inv E σ) (ctr : Fin nD → List Bool) (hc : ∀ i : Fin nD, j ≤ i.val → ctr i = []) :
    law (compile c j) (enc E σ ctr) = PMF.pure (enc E (exec E c σ) ctr) := by
  rw [law_eq_run _ (noGrow_compile c j), run_compile E hWM c j hd σ hI ctr hc]

/-! ### Well-formedness -/

/-- Unfold the instruction programs to primitives. -/
macro "unfold_instr" : tactic => `(tactic| simp only [compile, nandP, emitP, fixP, emitX1, oneP,
  zeroP, movP, incP, addP, subP, lnilP, lpushP, pushBodyP, lpopP, lmovP, rdsrcP, ltTestP, dropBy,
  shiftIn, countOnes, skipZ, moveBits, sin, push, nop, setZero, takeHead])

theorem pres_compile : ∀ (c : Code) (j : ℕ) (i : Fin nD),
    (∀ j', j ≤ j' → j' < j + depth c → j' % nD ≠ i.val) → (compile c j).Preserves (tC i)
  | .seq p q, j, i, h => by
      simp only [depth] at h
      exact ⟨pres_compile p j i (fun j' h1 h2 => h j' h1 (by omega)),
        pres_compile q j i (fun j' h1 h2 => h j' h1 (by omega))⟩
  | .ifLt a b p q, j, i, h => by
      simp only [depth] at h
      refine ⟨preserves_of_preservesB (by unfold_instr; simp [preservesB, Prim.writes]), ?_, ?_⟩
      · exact ⟨preserves_of_preservesB (by simp [preservesB, Prim.writes]),
          pres_compile q j i (fun j' h1 h2 => h j' h1 (by omega))⟩
      · exact ⟨preserves_of_preservesB (by simp [preservesB, Prim.writes]),
          pres_compile p j i (fun j' h1 h2 => h j' h1 (by omega))⟩
  | .rep a body, j, i, h => by
      simp only [depth] at h
      have hji : j % nD ≠ i.val := h j le_rfl (by omega)
      have hne : tCd j ≠ tC i := by
        intro e; apply hji; simpa [tCd] using congrArg Fin.val (tC_inj.mp e)
      refine ⟨by simp [Preserves, Prim.writes, Ne.symm hne], hne,
        pres_compile body (j + 1) i (fun j' h1 h2 => h j' (by omega) (by omega))⟩
  | .nand _ _ _, _, _, _ | .one _, _, _, _ | .zero _, _, _, _ | .mov _ _, _, _, _
  | .inc _, _, _, _ | .add _ _, _, _, _ | .sub _ _, _, _, _ | .lnil _, _, _, _
  | .lpush _ _, _, _, _ | .lpop _ _, _, _, _ | .lmov _ _, _, _, _ | .rdsrc _, _, _, _
  | .skip, _, _, _ => preserves_of_preservesB (by unfold_instr; simp [preservesB, Prim.writes])

/-- **The compiled programs are well formed.** -/
theorem wf_compile : ∀ (c : Code) (j : ℕ), j + depth c ≤ nD → (compile c j).WF
  | .seq p q, j, h => by
      simp only [depth] at h
      exact ⟨wf_compile p j (by omega), wf_compile q j (by omega)⟩
  | .ifLt a b p q, j, h => by
      simp only [depth] at h
      refine ⟨wf_of_wfB (by unfold_instr; simp [wfB, preservesB, Prim.writes]), ⟨trivial, ?_⟩,
        ⟨trivial, ?_⟩⟩
      · exact wf_compile q j (by omega)
      · exact wf_compile p j (by omega)
  | .rep a body, j, h => by
      simp only [depth] at h
      refine ⟨trivial, wf_compile body (j + 1) (by omega), ?_⟩
      have hj : j % nD = j := Nat.mod_eq_of_lt (by omega)
      exact pres_compile body (j + 1) ⟨j % nD, Nat.mod_lt _ (by decide)⟩
        (fun j' h1 h2 => by simp only; rw [hj, Nat.mod_eq_of_lt (by omega)]; omega)
  | .nand _ _ _, _, _ | .one _, _, _ | .zero _, _, _ | .mov _ _, _, _
  | .inc _, _, _ | .add _ _, _, _ | .sub _ _, _, _ | .lnil _, _, _
  | .lpush _ _, _, _ | .lpop _ _, _, _ | .lmov _ _, _, _ | .rdsrc _, _, _
  | .skip, _, _ => wf_of_wfB (by unfold_instr; simp [wfB, preservesB, Prim.writes])

end RegVM

end SigabaNeo.Tape
