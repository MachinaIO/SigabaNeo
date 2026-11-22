import SigabaNeo.Lib.Lattices.ProgAlgo.ValArith

/-!
# Well-formedness of compiled codes

A compiled code `compileA cert c` is well formed (every loop body leaves its counter tape alone)
when every `rep t body` of `c` has `t ∉ wr body` (`loopOkB`) and the step is well formed.
-/

namespace SigabaNeo.Tape

namespace ValVM

open Prog

/-- Every loop body of the code leaves its counter word alone. -/
def loopOkB : Code → Bool
  | .rep c b => !((wr b).contains c) && loopOkB b
  | .seq p q => loopOkB p && loopOkB q
  | .ifb _ p q => loopOkB p && loopOkB q
  | _ => true

theorem pres_frame_vac {m : ℕ} {e : Fin m ↪ Fin 256} {p : XProg m} {i : Fin 256}
    (h : ∀ j, e j ≠ i) : (XProg.frame e p).Preserves i := fun j hj => absurd hj (h j)

theorem pres_frame_one {m : ℕ} {e : Fin m ↪ Fin 256} {p : Prog m} {i : Fin 256} (j₀ : Fin m)
    (h : ∀ j, e j = i → j = j₀) (hp : p.preservesB j₀ = true) :
    (XProg.frame e (.prog p)).Preserves i := fun j hj => by
  rw [h j hj]; exact preserves_of_preservesB hp

theorem tS_ne_tWd' (x : Fin 120) : ∀ j, eS j ≠ tWd x := fun j => tS_ne_tWd j x

variable {H : List ℕ → Prop} {P : Prog 132} (cert : StepCert H P)

/-- **The compiled code leaves the words it does not write.** -/
theorem preserves_compileA : ∀ (c : Code) (x : Fin 120), x ∉ wr c →
    (compileA cert c).toX.Preserves (tWd x)
  | .gate d a b, x, h => by
    simp only [wr, List.mem_singleton] at h
    refine ⟨pres_frame_one 2 (fun j e => ?_) (by decide), pres_frame_one 2 (fun j e => ?_) (by decide),
      pres_frame_vac (tS_ne_tWd' x), pres_frame_vac (fun j e => ?_)⟩
    · have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fIn, ofV, tWd] at this
      split_ifs at this <;> first | omega | exact Fin.ext (by omega)
    · have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fIn, ofV, tWd] at this
      split_ifs at this <;> first | omega | exact Fin.ext (by omega)
    · have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fOut, ofV, tWd] at this
      split_ifs at this
      · omega
      · exact h (Fin.ext (by omega))
  | .mvV d s, x, h => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [compileA]
    split_ifs with hds
    · exact pres_frame_vac (fun j e => by
        have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)
    · exact pres_frame_vac (fun j e => by
        have := congrArg Fin.val e
        simp only [mkE, Function.Embedding.coeFn_mk, fMv, ofV, tWd, tTV] at this
        split_ifs at this <;> first | omega | exact h.1 (Fin.ext (by omega)) |
          exact h.2 (Fin.ext (by omega)))
  | .mv d s c, x, h => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [compileA]
    split_ifs with hds
    · exact pres_frame_vac (fun j e => by
        have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)
    · refine pres_frame_one 4 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fMv, ofV, tWd] at this
      split_ifs at this <;> first | omega | exact absurd (Fin.ext (by omega)) h.1 |
        exact absurd (Fin.ext (by omega)) h.2 | exact Fin.ext (by omega)
  | .cp d s, x, h => by
    simp only [wr, List.mem_singleton] at h
    simp only [compileA]
    split_ifs with hds
    · exact pres_frame_vac (fun j e => by
        have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)
    · refine pres_frame_one 1 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fCp, ofV, tWd] at this
      split_ifs at this <;> first | exact absurd (Fin.ext (by omega)) h | exact Fin.ext (by omega)
  | .drop t c, x, h => by
    simp only [wr, List.mem_singleton] at h
    simp only [compileA]
    split_ifs with hds
    · exact pres_frame_vac (fun j e => by
        have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)
    · refine pres_frame_one 2 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fDr, ofV, tWd] at this
      split_ifs at this <;> first | omega | exact absurd (Fin.ext (by omega)) h | exact Fin.ext (by omega)
  | .clr t, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_frame_vac (fun j e => h (tWd_inj e).symm)
  | .tl t, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_frame_vac (fun j e => h (tWd_inj e).symm)
  | .rep c b, x, h => by
    simp only [wr, List.mem_cons, not_or] at h
    exact ⟨fun e => h.1 (tWd_inj e).symm, preserves_compileA b x h.2⟩
  | .seq p q, x, h => by
    simp only [wr, List.mem_append, not_or] at h
    exact ⟨preserves_compileA p x h.1, preserves_compileA q x h.2⟩
  | .ifb t p q, x, h => by
    simp only [wr, List.mem_append, not_or] at h
    exact ⟨preserves_compileA p x h.1, preserves_compileA q x h.2⟩
  | .nop, x, _ => pres_frame_vac (fun j e => by
      have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)

/-- **A compiled code is well formed**, when its loops leave their counters alone. -/
theorem wf_compileA (hP : P.WF) : ∀ c : Code, loopOkB c = true → (compileA cert c).toX.WF
  | .gate d a b, _ => ⟨wf_of_wfB (by decide), wf_of_wfB (by decide), hP, wf_of_wfB (by decide)⟩
  | .mvV d s, _ => by
    simp only [compileA]; split_ifs <;> exact wf_of_wfB (by decide)
  | .mv d s c, _ => by
    simp only [compileA]; split_ifs <;> exact wf_of_wfB (by decide)
  | .cp d s, _ => by
    simp only [compileA]; split_ifs <;> exact wf_of_wfB (by decide)
  | .drop t c, _ => by
    simp only [compileA]; split_ifs <;> exact wf_of_wfB (by decide)
  | .clr t, _ => wf_of_wfB (by decide)
  | .tl t, _ => wf_of_wfB (by decide)
  | .rep c b, h => by
    simp only [loopOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨wf_compileA hP b h.2, preserves_compileA cert b c (fun hm => ?_)⟩
    have h1 := h.1
    simp [hm] at h1
  | .seq p q, h => by
    simp only [loopOkB, Bool.and_eq_true] at h
    exact ⟨wf_compileA hP p h.1, wf_compileA hP q h.2⟩
  | .ifb t p q, h => by
    simp only [loopOkB, Bool.and_eq_true] at h
    exact ⟨wf_compileA hP p h.1, wf_compileA hP q h.2⟩
  | .nop, _ => wf_of_wfB (by decide)

end ValVM

end SigabaNeo.Tape
