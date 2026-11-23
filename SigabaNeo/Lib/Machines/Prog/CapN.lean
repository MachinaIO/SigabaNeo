import SigabaNeo.Lib.Machines.Prog.CountP
import SigabaNeo.Lib.Machines.Prog.PhaseB
import SigabaNeo.Lib.Machines.Prog.NatPSize
import SigabaNeo.Lib.Machines.Prog.CoinFreeX

/-!
# A cap with a large template

`capP w` writes its template `false^w` with `putW`, one state per bit: too many states when the
cap is `2^50`. `capN w : XProg 5` builds the same template with `natP` (counter tape `2`, about
`195 log₂ w` states, `size_capN`) and then runs the loop of `capP` (`capLoop`):

* `law_capN`: tape `0 := false^(min g w)` from `false^g`, as `run_capP`;
* `ph_capN`: per-tape bounds and steps (`capLT`, at most `w` rounds).
-/

namespace SigabaNeo.Tape

namespace Prog

/-- The loop of the cap, its copy back and the clears (tape `3` the template). -/
def capLoop : Prog 5 := forN 4 3 capBody ⨾ cp 0 1 ⨾ clr 1 ⨾ clr 3

theorem capP_eq (w : ℕ) : capP w = putW 3 (List.replicate w false) ⨾ capLoop := rfl

theorem coinFree_capLoop : capLoop.CoinFree := by
  simp [CoinFree, capLoop, forN, capBody, nop, coinFreeB]

theorem wf_capLoop : capLoop.WF :=
  ⟨⟨trivial, wf_of_wfB rfl, preserves_of_preservesB rfl⟩, trivial, trivial, trivial⟩

/-- The time bound of `capLoop` (`Mx` bounds every tape). -/
def capLT (w Mx : ℕ) : ℕ :=
  (2 * (Mx + 1) + 3) + (w * (2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) + 1) + 2) +
    (3 * (2 * (Mx + 3) + 5))

/-- **Per-tape bounds of `capLoop`** (the template on tape `3` of at most `w` bits). -/
theorem bounds_capLoop (w S O X Q : ℕ) (ℓ : Fin 5 → ℕ) (hℓ : ℓ ≤ ![S, O, X, w, Q]) :
    lenBoundT capLoop ℓ ≤ ![O + w, 0, max X 1, 0, w] ∧
      timeBoundT capLoop ℓ ≤ capLT w (S + O + X + Q + w + 1) := by
  have l0 : ℓ 0 ≤ S := hℓ 0
  have l1 : ℓ 1 ≤ O := hℓ 1
  have l2 : ℓ 2 ≤ X := hℓ 2
  have l3 : ℓ 3 ≤ w := hℓ 3
  have l4 : ℓ 4 ≤ Q := hℓ 4
  set Mx := S + O + X + Q + w + 1 with hMx
  set ℓ2 := (Prim.copy (4 : Fin 5) 3).lenT ℓ with hℓ2
  have h2v : ℓ2 ≤ capV w S O X 0 := by
    intro t
    simp only [hℓ2, Prim.lenT, Function.update_apply, capV]
    fin_cases t <;> simp <;> omega
  have hit : ∀ j, (loopStepT 4 capBody)^[j] ℓ2 ≤ capV w S O X j := by
    intro j
    induction j with
    | zero => exact h2v
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact capBody_len w S O X j _ ((tailB_le 4 _).trans ih)
  have hw2 : ℓ2 4 ≤ w := by have := h2v 4; simp [capV] at this; omega
  have hround : ∀ j < ℓ2 4, roundTimeT (timeBoundT capBody) 4 ((loopStepT 4 capBody)^[j] ℓ2) ≤
      2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) := by
    intro j hj
    have hb : ∀ t, ((loopStepT 4 capBody)^[j] ℓ2) t ≤ Mx := fun t => by
      have := hit j t
      fin_cases t <;> simp [capV] at this ⊢ <;> omega
    simp only [roundTimeT]
    have hs := supB_le_ofC hb
    have hbody := timeBoundT_le_pcount capBody ⟨trivial, ⟨trivial, trivial, trivial⟩⟩
      (tailB 4 ((loopStepT 4 capBody)^[j] ℓ2)) (M := Mx)
      (fun t => (tailB_le 4 _ t).trans (hb t))
    have : pcount capBody = 5 := rfl
    rw [this] at hbody
    omega
  have tloop := timeBoundT_loop_le 4 capBody ℓ2 hround
  have hlenloop : lenBoundT (loop 4 capBody) ℓ2 ≤ capV w S O X w := by
    rw [lenBoundT_loop]
    refine iterSupT_le fun j hj => (hit j).trans ?_
    intro t
    fin_cases t <;> simp [capV] <;> omega
  refine ⟨fun t => ?_, ?_⟩
  · show (Prim.clear (3 : Fin 5)).lenT ((Prim.clear (1 : Fin 5)).lenT ((Prim.copy (0 : Fin 5) 1).lenT
      (lenBoundT (loop 4 capBody) ℓ2))) t ≤ _
    have a1 := hlenloop 1
    have a2 := hlenloop 2
    have a4 := hlenloop 4
    simp only [capV] at a1 a2 a4
    simp only [Prim.lenT, Function.update_apply]
    fin_cases t <;> simp at a1 a2 a4 ⊢ <;> omega
  · show (2 * (supB ℓ + (Prim.copy (4 : Fin 5) 3).pad) + 3) + timeBoundT (loop 4 capBody) ℓ2 +
        timeBoundT (cp 0 1 ⨾ clr 1 ⨾ clr 3) (lenBoundT (loop 4 capBody) ℓ2) ≤ _
    have s1 : supB ℓ ≤ Mx := supB_le_ofC fun t => by fin_cases t <;> simp <;> omega
    have hb3 : ∀ t, lenBoundT (loop 4 capBody) ℓ2 t ≤ Mx := fun t => by
      have := hlenloop t; fin_cases t <;> simp [capV] at this ⊢ <;> omega
    have t3 := timeBoundT_le_pcount (cp 0 1 ⨾ clr 1 ⨾ clr 3 : Prog 5) ⟨trivial, trivial, trivial⟩ _ hb3
    have : pcount (cp 0 1 ⨾ clr 1 ⨾ clr 3 : Prog 5) = 3 := rfl
    rw [this] at t3
    have tl' : timeBoundT (loop 4 capBody) ℓ2 ≤ w * (2 * Mx + 3 + 5 * (2 * (Mx + 5) + 5) + 1) + 2 :=
      tloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hw2) 2)
    simp only [Prim.pad, capLT]
    omega

end Prog

namespace XProg

open Prog

/-- **Cap a count at `w`**, the template `false^w` built by `natP` (counter tape `2`). -/
def capN (w : ℕ) : XProg 5 := .seq (natP 3 2 w) (.prog capLoop)

/-- **The law of `capN`**: tape `0 := false^(min g w)` from `false^g`, as `capP`. -/
theorem law_capN (w g : ℕ) (s : Store 5) (h0 : s 0 = List.replicate g false) (h1 : s 1 = [])
    (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = []) :
    (capN w).law s = PMF.pure (Function.update s 0 (List.replicate (min g w) false)) := by
  rw [capN, law_seq, law_natP (by decide) w s h2, PMF.pure_bind, law_prog,
    law_eq_run_of_coinFree _ coinFree_capLoop]
  rw [← run_capP w g s h0 h1 h2 h3 h4, capP_eq, run_seq, run_putW]

theorem coinFree_natP {n : ℕ} (t c' : Fin n) : ∀ m, (natP t c' m).CoinFree
  | 0 => by rw [natP]; rfl
  | m + 1 => by
    rw [natP]
    have ih := coinFree_natP t c' ((m + 1) / 2)
    split_ifs
    · exact coinFree_seq ih rfl
    · exact coinFree_seq (coinFree_seq ih rfl) rfl

theorem coinFree_capN (w : ℕ) : (capN w).CoinFree :=
  coinFree_seq (coinFree_natP _ _ w) coinFree_capLoop

theorem wf_capN (w : ℕ) : (capN w).WF := ⟨wf_natP (by decide) w, wf_capLoop⟩

/-- **`capN` as a phase**: the template by `natP`, then at most `w` rounds. -/
theorem ph_capN (w S O X Z Q : ℕ) :
    Ph (capN w) ![S, O, X, Z, Q]
      ((2 * w + 1) * (4 * max (supB ![S, O, X, Z, Q]) w + 12) +
        capLT w (S + O + max X w + Q + w + 1))
      ![O + w, 0, max (max X w) 1, 0, w] := by
  refine (ph_natP (by decide) w _).seq fun ℓ hℓ => ?_
  obtain ⟨h1, h2⟩ := bounds_capLoop w S O (max X w) Q ℓ (fun j => by
    have := hℓ j
    fin_cases j <;> simp [natB] at this ⊢ <;> omega)
  exact ⟨h2, h1⟩

theorem size_capN {w B : ℕ} (hw : w < 2 ^ (B + 1)) :
    (capN w).size ≤ (B + 1) * 195 + 36 + capLoop.size := by
  show (natP (3 : Fin 5) 2 w).size + capLoop.size ≤ _
  have := size_natP_lt (3 : Fin 5) 2 hw
  omega

end XProg

end SigabaNeo.Tape
