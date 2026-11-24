import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMLib
import SigabaNeo.Lib.Machines.Prog.CoinFreeX

/-!
# Well-formedness of compiled ring-word codes

`compile c` (`SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.RingVM`) is well formed (every loop body leaves
its counter tape alone) when every `rep t body` of `c` has `t ∉ wr body` (`loopOkB`,
**`wf_compile`**), and it is coin-free (**`coinFree_compile`**), so its machine is deterministic.
-/

namespace SigabaNeo.Tape

namespace RingVM

open Prog

/-- Every loop body of the code leaves its counter word alone. -/
def loopOkB : Code → Bool
  | .rep c b => !((wr b).contains c) && loopOkB b
  | .seq p q => loopOkB p && loopOkB q
  | .ifb _ p q => loopOkB p && loopOkB q
  | _ => true

theorem pres_frame_vac {m : ℕ} {e : Fin m ↪ Fin 247} {p : XProg m} {i : Fin 247}
    (h : ∀ j, e j ≠ i) : (XProg.frame e p).Preserves i := fun j hj => absurd hj (h j)

theorem pres_frame_one {m : ℕ} {e : Fin m ↪ Fin 247} {p : Prog m} {i : Fin 247} (j₀ : Fin m)
    (h : ∀ j, e j = i → j = j₀) (hp : p.preservesB j₀ = true) :
    (XProg.frame e (.prog p)).Preserves i := fun j hj => by
  rw [h j hj]; exact preserves_of_preservesB hp

theorem pres_loadA (i : ℕ) (hi : i < 40) (a x : Fin 200) :
    (loadA i hi a).Preserves (tWd x) :=
  pres_frame_one 2 (fun j e => by
    have := congrArg Fin.val e
    simp only [loadA, mkE, Function.Embedding.coeFn_mk, fIn, ofW, tWd] at this
    split_ifs at this <;> first | omega | exact Fin.ext (by omega)) (by decide)

theorem pres_loadT (t x : Fin 200) : (loadT t).Preserves (tWd x) :=
  pres_frame_one 1 (fun j e => by
    have := congrArg Fin.val e
    simp only [loadT, mkE, Function.Embedding.coeFn_mk, fTm, ofW, tWd] at this
    split_ifs at this <;> first | omega | exact Fin.ext (by omega)) (by decide)

theorem pres_store (d x : Fin 200) (h : x ≠ d) : (store d).Preserves (tWd x) :=
  pres_frame_vac (fun j e => by
    have := congrArg Fin.val e
    simp only [mkE, Function.Embedding.coeFn_mk, fOut, ofW, tWd] at this
    split_ifs at this
    · omega
    · exact h (Fin.ext (by omega)))

theorem pres_eOp {m : ℕ} {hm : m ≤ 40} {two : ℕ} {h2 : two = 2 ∨ two = 43} {k3 k4 : Bool}
    (P : Prog m) (x : Fin 200) : (XProg.frame (eOp m hm two h2 k3 k4) (.prog P)).Preserves (tWd x) :=
  pres_frame_vac (fun j e => by
    have := congrArg Fin.val e
    simp only [mkE, Function.Embedding.coeFn_mk, fOp, ofW, gOp, tWd] at this
    split_ifs at this <;> omega)

theorem pres_nopX (x : Fin 200) : nopX.Preserves (tWd x) :=
  pres_frame_vac (fun j e => by
    have := congrArg Fin.val e; simp [mkE, f1, tWd, tX0] at this; omega)

theorem pres_opBin {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he : ∀ x, (XProg.frame e (.prog P)).Preserves (tWd x))
    (d a b x : Fin 200) (h : x ≠ d) : (opBin P e d a b).Preserves (tWd x) :=
  ⟨pres_loadA 1 _ a x, pres_loadA 2 _ b x, he x, pres_store d x h⟩

theorem pres_opUn {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he : ∀ x, (XProg.frame e (.prog P)).Preserves (tWd x))
    (d a x : Fin 200) (h : x ≠ d) : (opUn P e d a).Preserves (tWd x) :=
  ⟨pres_loadA 1 _ a x, he x, pres_store d x h⟩

theorem pres_opTm {m : ℕ} (P : Prog (m + 1)) (e : Fin (m + 1) ↪ Fin 247) (he : ∀ x, (XProg.frame e (.prog P)).Preserves (tWd x))
    (d a t x : Fin 200) (h : x ≠ d) : (opTm P e d a t).Preserves (tWd x) :=
  ⟨pres_loadA 1 _ a x, pres_loadT t x, he x, pres_store d x h⟩

/-- **The compiled code leaves the words it does not write.** -/
theorem preserves_compile : ∀ (c : Code) (x : Fin 200), x ∉ wr c → (compile c).Preserves (tWd x)
  | .add d a b, x, h | .sub d a b, x, h | .mul d a b, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_opBin _ _ (fun y => pres_eOp _ y) d a b x h
  | .canon d a, x, h | .neg d a, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_opUn _ _ (fun y => pres_eOp _ y) d a x h
  | .digit d a t, x, h | .rotB d a t, x, h | .aut d a t, x, h | .rhoJ d a t, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_opTm _ _ (fun y => pres_eOp _ y) d a t x h
  | .mv d s c, x, h => by
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [compile]
    split_ifs with hds
    · exact pres_nopX x
    · refine pres_frame_one 4 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fMv, ofW, tWd] at this
      split_ifs at this <;> first | omega | exact absurd (Fin.ext (by omega)) h.1 |
        exact absurd (Fin.ext (by omega)) h.2 | exact Fin.ext (by omega)
  | .cp d s, x, h => by
    simp only [wr, List.mem_singleton] at h
    simp only [compile]
    split_ifs with hds
    · exact pres_nopX x
    · refine pres_frame_one 1 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fCp, ofW, tWd] at this
      split_ifs at this <;> first | exact absurd (Fin.ext (by omega)) h | exact Fin.ext (by omega)
  | .drop t c, x, h => by
    simp only [wr, List.mem_singleton] at h
    simp only [compile]
    split_ifs with hds
    · exact pres_nopX x
    · refine pres_frame_one 2 (fun j e => ?_) (by decide)
      have := congrArg Fin.val e
      simp only [mkE, Function.Embedding.coeFn_mk, fDr, ofW, tWd] at this
      split_ifs at this <;> first | omega | exact absurd (Fin.ext (by omega)) h | exact Fin.ext (by omega)
  | .clr t, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_frame_vac (fun j e => h (tWd_inj e).symm)
  | .tl t, x, h => by
    simp only [wr, List.mem_singleton] at h
    exact pres_frame_vac (fun j e => h (tWd_inj e).symm)
  | .rep c b, x, h => by
    simp only [wr, List.mem_cons, not_or] at h
    exact ⟨fun e => h.1 (tWd_inj e).symm, preserves_compile b x h.2⟩
  | .seq p q, x, h => by
    simp only [wr, List.mem_append, not_or] at h
    exact ⟨preserves_compile p x h.1, preserves_compile q x h.2⟩
  | .ifb t p q, x, h => by
    simp only [wr, List.mem_append, not_or] at h
    exact ⟨preserves_compile p x h.1, preserves_compile q x h.2⟩
  | .nop, x, _ => pres_nopX x

theorem wf_opBin {m : ℕ} (P : Prog (m + 1)) (hP : P.WF) (e : Fin (m + 1) ↪ Fin 247) (d a b : Fin 200) :
    (opBin P e d a b).WF := ⟨wf_of_wfB (by decide), wf_of_wfB (by decide), hP, wf_of_wfB (by decide)⟩

theorem wf_opUn {m : ℕ} (P : Prog (m + 1)) (hP : P.WF) (e : Fin (m + 1) ↪ Fin 247) (d a : Fin 200) :
    (opUn P e d a).WF := ⟨wf_of_wfB (by decide), hP, wf_of_wfB (by decide)⟩

theorem wf_opTm {m : ℕ} (P : Prog (m + 1)) (hP : P.WF) (e : Fin (m + 1) ↪ Fin 247) (d a t : Fin 200) :
    (opTm P e d a t).WF := ⟨wf_of_wfB (by decide), wf_of_wfB (by decide), hP, wf_of_wfB (by decide)⟩

/-- **A compiled code is well formed**, when its loops leave their counters alone. -/
theorem wf_compile : ∀ c : Code, loopOkB c = true → (compile c).WF
  | .add d a b, _ => wf_opBin _ wf_addRMP _ d a b
  | .sub d a b, _ => wf_opBin _ wf_subRMP _ d a b
  | .mul d a b, _ => wf_opBin _ wf_mulRMP _ d a b
  | .canon d a, _ => wf_opUn _ wf_canonRP _ d a
  | .neg d a, _ => wf_opUn _ wf_notP _ d a
  | .digit d a t, _ => wf_opTm _ wf_digitRWP _ d a t
  | .rotB d a t, _ => wf_opTm _ wf_rotBP _ d a t
  | .aut d a t, _ => wf_opTm _ wf_autMP _ d a t
  | .rhoJ d a t, _ => wf_opTm _ wf_rhoJP _ d a t
  | .mv d s c, _ => by
    simp only [compile]; split_ifs <;> exact wf_of_wfB (by decide)
  | .cp d s, _ => by
    simp only [compile]; split_ifs <;> exact wf_of_wfB (by decide)
  | .drop t c, _ => by
    simp only [compile]; split_ifs <;> exact wf_of_wfB (by decide)
  | .clr t, _ => wf_of_wfB (by decide)
  | .tl t, _ => wf_of_wfB (by decide)
  | .rep c b, h => by
    simp only [loopOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine ⟨wf_compile b h.2, preserves_compile b c (fun hm => ?_)⟩
    have h1 := h.1
    simp [hm] at h1
  | .seq p q, h => by
    simp only [loopOkB, Bool.and_eq_true] at h
    exact ⟨wf_compile p h.1, wf_compile q h.2⟩
  | .ifb t p q, h => by
    simp only [loopOkB, Bool.and_eq_true] at h
    exact ⟨wf_compile p h.1, wf_compile q h.2⟩
  | .nop, _ => wf_of_wfB (by decide)

/-- **A compiled code draws no coin.** -/
theorem coinFree_compile : ∀ c : Code, (compile c).CoinFree
  | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .canon _ _ | .neg _ _ | .digit _ _ _ | .rotB _ _ _
  | .aut _ _ _ | .rhoJ _ _ _ | .clr _ | .tl _ | .nop => rfl
  | .mv d s c => by simp only [compile]; split_ifs <;> rfl
  | .cp d s => by simp only [compile]; split_ifs <;> rfl
  | .drop t c => by simp only [compile]; split_ifs <;> rfl
  | .rep c b => XProg.coinFree_loop _ (coinFree_compile b)
  | .seq p q => XProg.coinFree_seq (coinFree_compile p) (coinFree_compile q)
  | .ifb t p q => XProg.coinFree_ifBit _ (coinFree_compile p) (coinFree_compile q)

end RingVM

end SigabaNeo.Tape
