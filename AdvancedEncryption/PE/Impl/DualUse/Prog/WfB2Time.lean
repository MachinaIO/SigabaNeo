import PE.Impl.DualUse.Prog.WfB2
import SigabaNeo.Lib.Lattices.ProgAlgo.ValCost
import SigabaNeo.Lib.Machines.Prog.PhaseB

/-!
# The time of the block-structured `W_f` block

Per-tape bounds of the phases of `wfBody` (`XProg.Ph`): the preparations by their primitives and
templates (`ph_tmplP`, `ph_putW`), the runs of the machine by `inv_compileA` with static word
bounds, the key sum by `boundsT_simKeyP`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-! ### Templates and literals -/

section Tmpl

variable {n : ℕ}

/-- The bounds after the templates `l` (counter `c`). -/
def tmplB (c : Fin n) : List (Fin n × ℕ) → (Fin n → ℕ) → (Fin n → ℕ)
  | [], β => β
  | x :: l, β => tmplB c l (natB x.1 c x.2 β)

/-- The steps of the templates `l`. -/
def tmplTT (c : Fin n) : List (Fin n × ℕ) → (Fin n → ℕ) → ℕ
  | [], β => 2 * (supB β + 1) + 3
  | x :: l, β => (2 * x.2 + 1) * (4 * max (supB β) x.2 + 12) + tmplTT c l (natB x.1 c x.2 β)

theorem ph_tmplP (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ), (∀ x ∈ l, x.1 ≠ c) →
    Ph (tmplP c l) β (tmplTT c l β) (tmplB c l β)
  | [], β, _ => by
    refine (ph_prim (.copy c c) β).mono le_rfl le_rfl (fun t => ?_)
    simp only [Prim.lenT, tmplB, Function.update_apply]
    split_ifs with h <;> simp [h]
  | x :: l, β, hl => (ph_natP (Ne.symm (hl x (by simp))) x.2 β).seq
      (ph_tmplP c l _ (fun y hy => hl y (by simp [hy])))

/-- The literal `w` appended to `t`. -/
theorem ph_putW (t : Fin n) : ∀ (w : List Bool) (β : Fin n → ℕ),
    Ph (putW t w) β ((w.length + 1) * (2 * (supB β + w.length + 1) + 3))
      (Function.update β t (β t + w.length))
  | [], β => by
    refine (ph_prim (.copy t t) β).mono le_rfl (by simp) (fun i => ?_)
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with h <;> simp [h]
  | b :: w, β => by
    refine ((ph_prim (.snoc t b) β).seq (ph_putW t w _)).mono le_rfl ?_ (fun i => ?_)
    · simp only [Prim.lenT, List.length_cons]
      have : supB (Function.update β t (β t + 1)) ≤ supB β + 1 :=
        supB_le_of fun i => by
          by_cases h : i = t
          · subst h; simp only [Function.update_self]; exact Nat.add_le_add_right (le_supB β _) 1
          · rw [Function.update_of_ne h]; exact (le_supB β i).trans (Nat.le_succ _)
      nlinarith
    · simp only [Prim.lenT, List.length_cons]
      by_cases h : i = t
      · subst h; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne h]; exact le_rfl

end Tmpl

end AdvancedEncryption.DualUse.Prog
