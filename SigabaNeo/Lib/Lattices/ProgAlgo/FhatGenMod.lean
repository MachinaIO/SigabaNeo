import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenArith

/-!
# Generating gate tapes: modular addition and subtraction

Moving a prefix of a list (`takeC`), constant lists of wires by a test on the bit index
(`constC`), and the register code of `modAdd`, `modSub`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

theorem exec_lpush_lt (σ : St) (l : LR) (r : SR) (hl : (σ.ls l).length < E.C)
    (hr : σ.sc r ≤ E.M) :
    exec E (.lpush l r) σ = { σ with ls := Function.update σ.ls l (σ.ls l ++ [σ.sc r]) } := by
  simp [exec, hl, min_eq_left hr]

/-! ### Moving a prefix -/

/-- Move the first `|n|` elements of `lA` to the end of `lR` (through the register `41`). -/
def takeC (n : SR) (lA lR : LR) : Code := .rep n (.seq (.lpop 41 lA) (.lpush lR 41))

theorem iter_take {lA lR : LR} (hAR : lA ≠ lR) :
    ∀ (X Y L0 : List ℕ) (σ : St), Inv E σ → σ.ls lA = X ++ Y → σ.ls lR = L0 →
      L0.length + X.length ≤ E.C →
      ∃ sc', (exec E (.seq (.lpop 41 lA) (.lpush lR 41)))^[X.length] σ =
        { σ with sc := sc', ls := Function.update (Function.update σ.ls lA Y) lR (L0 ++ X) } ∧
        Fr [41] σ.sc sc'
  | [], Y, L0, σ, _, hA, hR, _ => by
    refine ⟨σ.sc, ?_, Fr.refl _ _⟩
    simp only [List.length_nil, Function.iterate_zero, id, List.append_nil]
    rw [List.nil_append] at hA
    rw [← hA, ← hR]; simp
  | x :: X, Y, L0, σ, hInv, hA, hR, hcap => by
    simp only [List.length_cons] at hcap ⊢
    rw [Function.iterate_succ_apply]
    have hx : x ≤ E.M := (hInv.1 lA).2 x (by simp [hA])
    set sc1 := Function.update σ.sc 41 x
    set ls1 := Function.update (Function.update σ.ls lA (X ++ Y)) lR (L0 ++ [x])
    set σ1 : St := { σ with sc := sc1, ls := ls1 }
    have e1 : exec E (.seq (.lpop 41 lA) (.lpush lR 41)) σ = σ1 := by
      simp only [exec_seq]
      rw [exec_lpush_lt _ _ _ (by simp [exec, Function.update_of_ne hAR.symm, hR]; omega)
        (by simp [exec, hA]; exact hx)]
      simp [exec, hA, Function.update_of_ne hAR.symm, hR, σ1, sc1, ls1]
    rw [e1]
    have hI1 : Inv E σ1 := by
      have := inv_exec E (.seq (.lpop 41 lA) (.lpush lR 41)) σ hInv; rw [e1] at this; exact this
    obtain ⟨sc', h, f⟩ := iter_take hAR X Y (L0 ++ [x]) σ1 hI1
      (by simp [σ1, ls1, Function.update_of_ne hAR]) (by simp [σ1, ls1]) (by simp; omega)
    refine ⟨sc', ?_, fun r hr => (f r hr).trans ?_⟩
    · rw [h]; simp only [σ1, ls1]
      congr 1
      funext l; simp only [Function.update_apply]; split_ifs <;> simp
    · simp only [σ1, sc1]; exact Function.update_of_ne (by simpa using hr) _ _

/-- **Moving a prefix.** -/
theorem exec_takeC {n : SR} {lA lR : LR} (hAR : lA ≠ lR) (X Y L0 : List ℕ) (σ : St)
    (hInv : Inv E σ) (hA : σ.ls lA = X ++ Y) (hR : σ.ls lR = L0) (hn : σ.sc n = X.length)
    (hcap : L0.length + X.length ≤ E.C) :
    ∃ sc', exec E (takeC n lA lR) σ =
        { σ with sc := sc', ls := Function.update (Function.update σ.ls lA Y) lR (L0 ++ X) } ∧
      Fr [41] σ.sc sc' := by
  rw [takeC, exec_rep, hn]; exact iter_take hAR X Y L0 σ hInv hA hR hcap

/-- Codes without `nand`. -/
def NoNand : Code → Prop
  | .nand _ _ _ => False
  | .seq p q | .ifLt _ _ p q => NoNand p ∧ NoNand q
  | .rep _ body => NoNand body
  | _ => True

/-- **A code without `nand` leaves the program alone.** -/
theorem exec_out_t : ∀ (c : Code), NoNand c → ∀ (σ : St) (o : List Bool) (t : ℕ),
    exec E c { σ with out := o, t := t } = { exec E c σ with out := o, t := t }
  | .nand _ _ _, h, _, _, _ => h.elim
  | .one _, _, _, _, _ | .zero _, _, _, _, _ | .mov _ _, _, _, _, _ | .inc _, _, _, _, _
  | .add _ _, _, _, _, _ | .sub _ _, _, _, _, _ | .lnil _, _, _, _, _ | .lpush _ _, _, _, _, _
  | .lpop _ _, _, _, _, _ | .lmov _ _, _, _, _, _ | .rdsrc _, _, _, _, _ | .skip, _, _, _, _ => rfl
  | .seq p q, h, σ, o, t => by
    simp only [exec_seq]; rw [exec_out_t p h.1, exec_out_t q h.2]
  | .ifLt a b p q, h, σ, o, t => by
    simp only [exec]; split_ifs
    · exact exec_out_t p h.1 σ o t
    · exact exec_out_t q h.2 σ o t
  | .rep a body, h, σ, o, t => by
    simp only [exec]
    generalize σ.sc a = m
    induction m generalizing σ with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        exec_out_t body h, ih]

theorem exec_mk_noNand (c : Code) (hc : NoNand c) (P : SLP ι) (σ : St) :
    exec E c (mk E ix P σ) = mk E ix P (exec E c σ) := exec_out_t c hc σ _ _

end FhatGen

end SigabaNeo.Lattices
