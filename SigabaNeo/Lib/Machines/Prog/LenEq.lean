import SigabaNeo.Lib.Machines.Prog.AppendW

/-!
# Unary constants and the length test

* `natU o a b n`: `o := 1^n` by doubling along the bits of `n` (`O(log n)` instructions,
  `run_natU`);
* **`lenEqP n`** (`Prog 6`): input `C` on tape `0` (kept), output `[decide (|C| = n)]` on tape `1`,
  the other tapes blank before and after (`run_lenEqP`, `law_lenEqP`).
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

/-- `o := 1^n` (from any `o`; `a`, `b` scratch). -/
def natU (o a b : Fin k) : ℕ → Prog k
  | 0 => clr o
  | n + 1 =>
    if (n + 1) % 2 = 0 then natU o a b ((n + 1) / 2) ⨾ appT o o a b
    else natU o a b n ⨾ prim (.snoc o true)
  decreasing_by all_goals omega

theorem run_natU {o a b : Fin k} (hoa : o ≠ a) (hob : o ≠ b) (hab : a ≠ b) :
    ∀ (n : ℕ) (s : Store k), s a = [] → s b = [] →
      run (natU o a b n) s = Function.update s o (List.replicate n true)
  | 0, s, _, _ => by rw [natU, run_clear]; rfl
  | n + 1, s, ha, hb => by
    rw [natU]
    split_ifs with h
    · rw [run_seq, run_natU hoa hob hab ((n + 1) / 2) s ha hb,
        run_appT_blank hoa hob hab _ (by rw [Function.update_of_ne (Ne.symm hoa)]; exact ha)
          (by rw [Function.update_of_ne (Ne.symm hob)]; exact hb),
        Function.update_self, Function.update_idem, List.replicate_append_replicate]
      congr 2; omega
    · rw [run_seq, run_natU hoa hob hab n s ha hb, run_prim]
      simp [Prim.apply, List.replicate_succ']
  decreasing_by all_goals omega

theorem coinFree_natU (o a b : Fin k) : ∀ n, (natU o a b n).CoinFree
  | 0 => by rw [natU]; rfl
  | n + 1 => by
    rw [natU]; split_ifs
    · exact (coinFree_natU o a b _).seq' (coinFree_appT _ _ _ _)
    · exact (coinFree_natU o a b n).seq' (CoinFree.prim' _)
  decreasing_by all_goals omega

theorem wf_natU {o a b : Fin k} (hoa : o ≠ a) (hba : b ≠ a) : ∀ n, (natU o a b n).WF
  | 0 => by rw [natU]; trivial
  | n + 1 => by
    rw [natU]; split_ifs
    · exact ⟨wf_natU hoa hba _, wf_appT hoa hba⟩
    · exact ⟨wf_natU hoa hba n, trivial⟩
  decreasing_by all_goals omega

/-- `f := [true]` or `[false]`. -/
def setB (f : Fin k) (b : Bool) : Prog k := clr f ⨾ prim (.snoc f b)

theorem run_setB (f : Fin k) (b : Bool) (s : Store k) :
    run (setB f b) s = Function.update s f [b] := by
  simp [setB, run_prim, Prim.apply]

/-- **The length test**: tapes `0` input (kept), `1` flag, `2` template, `3` copy, `4` `5`
scratch. -/
def lenEqP (n : ℕ) : Prog 6 :=
  natU 2 4 5 n ⨾ cp 3 0 ⨾ dropT 3 2 4 ⨾
    ifBlank 3 (dropT 2 0 4 ⨾ ifBlank 2 (setB 1 true) (setB 1 false)) (setB 1 false) ⨾
    clr 2 ⨾ clr 3

/-- The store with `C` on tape `0`, every other tape blank. -/
def in0 (C : List Bool) : Store 6 := Function.update (fun _ => []) 0 C

theorem ite_t {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem coinFree_setB (f : Fin k) (b : Bool) : (setB f b).CoinFree :=
  (CoinFree.prim' _).seq' (CoinFree.prim' _)

theorem run_lenEqP (n : ℕ) (C : List Bool) :
    run (lenEqP n) (in0 C) = Function.update (in0 C) 1 [decide (C.length = n)] := by
  simp only [lenEqP, run_seq]
  have e1 : run (dropT 3 2 4) (run (cp 3 0) (run (natU 2 4 5 n) (in0 C))) =
      Function.update (Function.update (in0 C) 2 (List.replicate n true)) 3 (C.drop n) := by
    rw [run_natU (by decide) (by decide) (by decide) n _ rfl rfl, run_copy,
      run_dropT_blank (by decide) _ (by simp [in0, Function.update_apply])]
    funext t; simp +decide [in0, Function.update_apply]; split_ifs <;> simp_all
  rw [e1, run_ifBlank]
  simp only [Function.update_self]
  by_cases hc : C.length ≤ n
  · rw [ite_t (List.drop_eq_nil_iff.mpr hc), run_seq,
      run_dropT_blank (by decide) _ (by simp [in0, Function.update_apply]), run_ifBlank]
    have e2 : (Function.update (Function.update (Function.update (in0 C) 2 (List.replicate n true))
        3 (C.drop n)) 2 ((Function.update (Function.update (in0 C) 2 (List.replicate n true)) 3
        (C.drop n) 2).drop (Function.update (Function.update (in0 C) 2 (List.replicate n true)) 3
        (C.drop n) 0).length)) 2 = List.replicate (n - C.length) true := by
      simp +decide [in0, Function.update_apply]
    rw [e2]
    by_cases hn : n ≤ C.length
    · rw [ite_t (by simp; omega), run_setB, run_clear, run_clear]
      funext t; simp +decide [in0, Function.update_apply, List.drop_eq_nil_iff.mpr hc]
      split_ifs <;> simp_all; omega
    · rw [ite_f (by simp; omega), run_setB, run_clear, run_clear]
      funext t; simp +decide [in0, Function.update_apply, List.drop_eq_nil_iff.mpr hc]
      split_ifs <;> simp_all; omega
  · rw [ite_f (by rw [List.drop_eq_nil_iff]; omega), run_setB, run_clear, run_clear]
    funext t; simp +decide [in0, Function.update_apply]
    split_ifs <;> simp_all; omega

theorem coinFree_lenEqP (n : ℕ) : (lenEqP n).CoinFree := by
  simp only [lenEqP]
  exact (coinFree_natU _ _ _ n).seq' ((CoinFree.prim' _).seq' ((coinFree_dropT _ _ _).seq'
    ((CoinFree.ifBlank' ((coinFree_dropT _ _ _).seq' (CoinFree.ifBlank' (coinFree_setB _ _)
      (coinFree_setB _ _))) (coinFree_setB _ _)).seq'
    ((CoinFree.prim' _).seq' (CoinFree.prim' _)))))

theorem wf_lenEqP (n : ℕ) : (lenEqP n).WF :=
  ⟨wf_natU (by decide) (by decide) n, trivial, wf_dropT (by decide),
    ⟨⟨wf_dropT (by decide), ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩,
    trivial, trivial⟩

/-- **The law of the length test.** -/
theorem law_lenEqP (n : ℕ) (C : List Bool) :
    (lenEqP n).law (in0 C) = PMF.pure (Function.update (in0 C) 1 [decide (C.length = n)]) := by
  rw [law_eq_run_of_coinFree _ (coinFree_lenEqP n), run_lenEqP]

end Prog

end SigabaNeo.Tape
