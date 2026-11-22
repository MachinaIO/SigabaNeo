import SigabaNeo.Lib.Machines.Prog.BoundsT

/-!
# Per-tape bounds of tape programs by numeric evaluation

`timeBoundT p ℓ` and `lenBoundT p ℓ` (`SigabaNeo.Lib.Machines.Prog.BoundsT`) are defined by
recursion on `p`, with a loop charged through all the iterates of its body's bound, so they cannot
be evaluated directly on a program with nested loops. Here they are bounded by a **verified
numeric interpreter** `NB.run` over concrete per-tape bounds (lists of naturals, `NB.vg`):

* a primitive updates the bound list exactly (`NB.primL`, `vg_primL`) and costs
  `2 · (max + pad) + 3`;
* branches join (`NB.vjoin`, the pointwise maximum);
* a loop first looks for an **invariant** bound (iterate the body and join, at most `fuel` times;
  this succeeds when the body clears what it grows): then it is charged `n` rounds at the
  invariant, `n` the bound of its counter; otherwise it is **unrolled** over its `n` rounds.

**Soundness** (`NB.run_sound`): `run fuel p v = some (v', T)` gives, for every `ℓ ≤ vg v`,
`lenBoundT p ℓ ≤ vg v'` and `timeBoundT p ℓ ≤ T`. A certificate (`NB.check`) is a closed
computation, checked by `decide +kernel`.
-/

namespace SigabaNeo.Tape.NB

open Prog

variable {k : ℕ}

/-! ### Bound lists -/

/-- The bound of tape `t`. -/
def vg (v : List ℕ) (t : Fin k) : ℕ := v.getD t.val 0

/-- `x :: v`, with `x` evaluated when the list is (a match on `x`: the kernel's evaluation then
stores a numeral, not the expression of `x`). -/
def lcons (x : ℕ) (v : List ℕ) : List ℕ :=
  match x with
  | 0 => 0 :: v
  | n + 1 => (n + 1) :: v

@[simp] theorem lcons_eq (x : ℕ) (v : List ℕ) : lcons x v = x :: v := by cases x <;> rfl

/-- Set the entry `i` (extending by zeros). -/
def lset : List ℕ → ℕ → ℕ → List ℕ
  | [], 0, x => lcons x []
  | [], i + 1, x => 0 :: lset [] i x
  | _ :: v, 0, x => lcons x v
  | a :: v, i + 1, x => a :: lset v i x

theorem getD_lset : ∀ (v : List ℕ) (i x j : ℕ),
    (lset v i x).getD j 0 = if j = i then x else v.getD j 0
  | [], 0, x, j => by cases j <;> simp [lset]
  | [], i + 1, x, j => by
    cases j with
    | zero => simp [lset]
    | succ j => rw [lset, List.getD_cons_succ, getD_lset [] i x j]; simp
  | _ :: v, 0, x, j => by cases j <;> simp [lset]
  | a :: v, i + 1, x, j => by
    cases j with
    | zero => simp [lset]
    | succ j => rw [lset, List.getD_cons_succ, getD_lset v i x j]; simp

/-- Set the bound of tape `i`. -/
def vset (v : List ℕ) (i : Fin k) (x : ℕ) : List ℕ := lset v i.val x

theorem vg_vset (v : List ℕ) (i : Fin k) (x : ℕ) :
    vg (vset v i x) = Function.update (vg v) i x := by
  funext t
  simp only [vg, vset, getD_lset, Function.update_apply, Fin.ext_iff]

/-- The pointwise maximum. -/
def vjoin : List ℕ → List ℕ → List ℕ
  | [], w => w
  | a :: v, [] => a :: v
  | a :: v, b :: w => lcons (max a b) (vjoin v w)

theorem getD_vjoin : ∀ (v w : List ℕ) (j : ℕ),
    (vjoin v w).getD j 0 = max (v.getD j 0) (w.getD j 0)
  | [], w, j => by simp [vjoin]
  | a :: v, [], j => by simp [vjoin]
  | a :: v, b :: w, j => by
    cases j with
    | zero => simp [vjoin]
    | succ j => rw [vjoin, lcons_eq, List.getD_cons_succ, getD_vjoin v w j]; simp

theorem vg_vjoin (v w : List ℕ) (t : Fin k) : vg (vjoin v w) t = max (vg v t) (vg w t) :=
  getD_vjoin v w t.val

theorem le_vjoin_left (v w : List ℕ) : (vg v : Fin k → ℕ) ≤ vg (vjoin v w) := fun t => by
  rw [vg_vjoin]; exact le_max_left _ _

theorem le_vjoin_right (v w : List ℕ) : (vg w : Fin k → ℕ) ≤ vg (vjoin v w) := fun t => by
  rw [vg_vjoin]; exact le_max_right _ _

/-- The pointwise order. -/
def vle : List ℕ → List ℕ → Bool
  | [], _ => true
  | a :: v, [] => a == 0 && vle v []
  | a :: v, b :: w => decide (a ≤ b) && vle v w

theorem getD_le_of_vle : ∀ {v w : List ℕ}, vle v w = true → ∀ j, v.getD j 0 ≤ w.getD j 0
  | [], w, _, j => by simp
  | a :: v, [], h, j => by
    simp only [vle, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simp [h.1]
    | succ j => simpa using getD_le_of_vle h.2 j
  | a :: v, b :: w, h, j => by
    simp only [vle, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j => simpa using getD_le_of_vle h.2 j

theorem vg_le_of_vle {v w : List ℕ} (h : vle v w = true) : (vg v : Fin k → ℕ) ≤ vg w :=
  fun t => getD_le_of_vle h t.val

/-- The largest entry. -/
def vmax : List ℕ → ℕ
  | [] => 0
  | a :: v => max a (vmax v)

theorem getD_le_vmax : ∀ (v : List ℕ) (j : ℕ), v.getD j 0 ≤ vmax v
  | [], j => by simp
  | a :: v, 0 => by simp [vmax]
  | a :: v, j + 1 => by simpa [vmax] using (getD_le_vmax v j).trans (le_max_right a _)

theorem supB_vg_le (v : List ℕ) : supB (vg v : Fin k → ℕ) ≤ vmax v :=
  Finset.sup_le fun t _ => getD_le_vmax v t.val

/-! ### The interpreter -/

/-- The bound list after a primitive. -/
def primL : Prim k → List ℕ → List ℕ
  | .clear i, v => vset v i 0
  | .copy i j, v => vset v i (vg v j)
  | .carry _ _ _, v => v
  | .tail i, v => vset v i (vg v i - 1)
  | .pop i j, v => vset (vset v i (vg v i - 1)) j (min 1 (vg v i))
  | .eq _ _ f, v => vset v f 1
  | .cons i _, v | .snoc i _, v | .consHead i _, v | .snocHead i _, v => vset v i (vg v i + 1)

theorem vg_primL (p : Prim k) (v : List ℕ) : vg (primL p v) = p.lenT (vg v) := by
  cases p <;> simp only [primL, Prim.lenT, vg_vset]

/-- `some (v, t)`, with `t` evaluated when the result is (as `lcons`). -/
def res (v : List ℕ) (t : ℕ) : Option (List ℕ × ℕ) :=
  match t with
  | 0 => some (v, 0)
  | n + 1 => some (v, n + 1)

@[simp] theorem res_eq (v : List ℕ) (t : ℕ) : res v t = some (v, t) := by cases t <;> rfl

/-- Look for an invariant bound of a loop body `f`, from `w`, joining at most `n` times. -/
def fixL (f : List ℕ → Option (List ℕ × ℕ)) : ℕ → List ℕ → Option (List ℕ × ℕ)
  | 0, _ => none
  | n + 1, w => match f w with
    | none => none
    | some (wb, tb) => if vle wb w then res w tb else fixL f n (vjoin w wb)

/-- `m` rounds of a loop body `f` from `w`: the join of the iterates and the largest round time. -/
def unrollL (f : List ℕ → Option (List ℕ × ℕ)) : ℕ → List ℕ → Option (List ℕ × ℕ)
  | 0, w => res w 0
  | m + 1, w => match f w with
    | none => none
    | some (wb, tb) => match unrollL f m wb with
      | none => none
      | some (J, R) => res (vjoin w J) (max (2 * vmax w + 3 + tb) R)

/-- The tape a lengthening primitive lengthens by one bit. -/
def growT : Prim k → Option (Fin k)
  | .cons i _ | .snoc i _ | .consHead i _ | .snocHead i _ => some i
  | _ => none

/-- A loop whose body is one lengthening primitive on a tape `o ≠ i`: closed form. -/
def loopFast (i : Fin k) (body : Prog k) (v : List ℕ) : Option (List ℕ × ℕ) :=
  match body with
  | .prim p => match growT p with
    | some o => if o = i then none else
        res (vset v o (vg v o + vg v i)) (vg v i * (4 * (vmax v + vg v i) + 9) + 2)
    | none => none
  | _ => none

/-- **The numeric interpreter**: the bound list afterwards and a time bound. -/
def run (fuel : ℕ) : Prog k → List ℕ → Option (List ℕ × ℕ)
  | .prim p, v => res (primL p v) (2 * (vmax v + p.pad) + 3)
  | .coin _, _ => none
  | .seq p q, v => match run fuel p v with
    | none => none
    | some (v₁, t₁) => match run fuel q v₁ with
      | none => none
      | some (v₂, t₂) => res v₂ (t₁ + t₂)
  | .ifBlank _ p q, v | .ifBit _ p q, v => match run fuel p v, run fuel q v with
    | some (v₁, t₁), some (v₂, t₂) => res (vjoin v₁ v₂) (max t₁ t₂ + 1)
    | _, _ => none
  | .loop i body, v => match loopFast i body v with
    | some r => some r
    | none => match fixL (run fuel body) fuel v with
      | some (w, tb) => res w (vg v i * (2 * vmax w + 3 + tb + 1) + 2)
      | none => match unrollL (run fuel body) (vg v i) v with
        | some (J, R) => res J (vg v i * (R + 1) + 2)
        | none => none
  termination_by structural p => p

/-! ### Soundness -/

/-- `v'` and `T` bound the program from every `ℓ ≤ vg v`. -/
def Sound (p : Prog k) (v v' : List ℕ) (T : ℕ) : Prop :=
  ∀ ℓ, ℓ ≤ vg v → lenBoundT p ℓ ≤ vg v' ∧ timeBoundT p ℓ ≤ T

theorem fixL_spec (f : List ℕ → Option (List ℕ × ℕ)) :
    ∀ (n : ℕ) (v w : List ℕ) (tb : ℕ), fixL f n v = some (w, tb) →
      ∃ wb, f w = some (wb, tb) ∧ vle wb w = true ∧ (vg v : Fin k → ℕ) ≤ vg w
  | 0, v, w, tb, h => by simp [fixL] at h
  | n + 1, v, w, tb, h => by
    simp only [fixL, res_eq] at h
    rcases hf : f v with _ | ⟨wb, t⟩
    · rw [hf] at h; simp at h
    · rw [hf] at h
      simp only [res_eq] at h
      split_ifs at h with hle
      · simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨wb, hf, hle, le_rfl⟩
      · obtain ⟨wb', h1, h2, h3⟩ := fixL_spec f n _ w tb h
        exact ⟨wb', h1, h2, (le_vjoin_left v wb).trans h3⟩

theorem unrollL_spec {i : Fin k} {body : Prog k} {f : List ℕ → Option (List ℕ × ℕ)}
    (hf : ∀ v v' T, f v = some (v', T) → Sound body v v' T) :
    ∀ (m : ℕ) (w J : List ℕ) (R : ℕ), unrollL f m w = some (J, R) → ∀ ℓ, ℓ ≤ vg w →
      (∀ j ≤ m, (loopStepT i body)^[j] ℓ ≤ vg J) ∧
      ∀ j < m, roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ) ≤ R
  | 0, w, J, R, h, ℓ, hℓ => by
    simp only [unrollL, res_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun j hj => by rw [Nat.le_zero.mp hj]; exact hℓ, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, w, J, R, h, ℓ, hℓ => by
    simp only [unrollL, res_eq] at h
    rcases hfw : f w with _ | ⟨wb, tb⟩
    · rw [hfw] at h; simp at h
    rw [hfw] at h
    simp only [res_eq] at h
    rcases hu : unrollL f m wb with _ | ⟨J', R'⟩
    · rw [hu] at h; simp at h
    rw [hu] at h
    simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := hf w wb tb hfw
    have h1 : loopStepT i body ℓ ≤ vg wb :=
      ((lenBoundT_mono body) (tailB_le i ℓ)).trans (hb ℓ hℓ).1
    obtain ⟨ih1, ih2⟩ := unrollL_spec hf m wb J' R' hu _ h1
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero => exact hℓ.trans (le_vjoin_left _ _)
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact (ih1 j (by omega)).trans (le_vjoin_right _ _)
    · cases j with
      | zero =>
        refine ((roundTimeT_le body i ℓ).trans ?_).trans (le_max_left _ _)
        have := supB_mono hℓ
        have := supB_vg_le (k := k) w
        have := (hb ℓ hℓ).2
        omega
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact (ih2 j (by omega)).trans (le_max_right _ _)

theorem lenT_of_growT {p : Prim k} {o : Fin k} (h : growT p = some o) (ℓ : Fin k → ℕ) :
    p.lenT ℓ = Function.update ℓ o (ℓ o + 1) ∧ p.pad = 1 := by
  cases p <;> simp_all [growT, Prim.lenT, Prim.pad]

theorem supB_update_add (ℓ : Fin k → ℕ) (o : Fin k) (j : ℕ) :
    supB (Function.update ℓ o (ℓ o + j)) ≤ supB ℓ + j :=
  Finset.sup_le fun t _ => by
    rw [Function.update_apply]
    split_ifs with h
    · subst h; have := le_supB ℓ t; omega
    · have := le_supB ℓ t; omega

theorem sound_loopFast {i : Fin k} {body : Prog k} {v v' : List ℕ} {T : ℕ}
    (h : loopFast i body v = some (v', T)) : Sound (.loop i body) v v' T := by
  unfold loopFast at h
  rcases body with p | _ | _ | _ | _ | _ <;> simp only [reduceCtorEq] at h
  rcases hg : growT p with _ | o
  · rw [hg] at h; simp at h
  rw [hg] at h
  simp only at h
  split_ifs at h with hoi
  simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro ℓ hℓ
  have hl := fun ℓ' => (lenT_of_growT hg ℓ').1
  have hpad := (lenT_of_growT hg ℓ).2
  have hit : ∀ j, (loopStepT i (.prim p))^[j] ℓ ≤ Function.update ℓ o (ℓ o + j) := by
    intro j
    induction j with
    | zero => intro t; simp [Function.update_apply]; split_ifs <;> simp_all
    | succ j ihj =>
      rw [Function.iterate_succ_apply']
      refine (loopStepT_mono i _ ihj).trans fun t => ?_
      simp only [loopStepT, lenBoundT, hl, tailB, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
  have hM : supB ℓ ≤ vmax v := (supB_mono hℓ).trans (supB_vg_le v)
  have hi : ℓ i ≤ vg v i := hℓ i
  refine ⟨iterSupT_le fun j hj t => ?_, ?_⟩
  · refine (hit j t).trans ?_
    by_cases ht : t = o
    · subst ht
      have h3 : ℓ t ≤ vg v t := hℓ t
      have h4 : j ≤ vg v i := hj.trans hi
      simp only [vg_vset, Function.update_self]
      omega
    · simp only [Function.update_of_ne ht, vg_vset]
      exact hℓ t
  · refine (timeBoundT_loop_le i _ ℓ (R := 4 * (vmax v + vg v i) + 8) fun j hj => ?_).trans ?_
    · have h1 := (supB_mono (hit j)).trans (supB_update_add ℓ o j)
      have h2 := supB_mono (tailB_le i ((loopStepT i (.prim p))^[j] ℓ))
      simp only [roundTimeT, timeBoundT, hpad]
      have h4 : j ≤ vg v i := (Nat.le_of_lt hj).trans hi
      have h5 : supB ℓ ≤ vmax v := hM
      omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul hi (by omega)) 2

theorem run_sound (fuel : ℕ) : ∀ (p : Prog k) (v v' : List ℕ) (T : ℕ),
    run fuel p v = some (v', T) → Sound p v v' T := by
  intro p
  induction p with
  | prim p =>
    intro v v' T h ℓ hℓ
    simp only [run, res_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rw [vg_primL]; exact p.lenT_mono hℓ, ?_⟩
    simp only [timeBoundT]
    have := supB_mono hℓ
    have := supB_vg_le (k := k) v
    omega
  | coin i => intro v v' T h; simp [run] at h
  | seq p q ihp ihq =>
    intro v v' T h ℓ hℓ
    simp only [run, res_eq] at h
    rcases hp : run fuel p v with _ | ⟨v₁, t₁⟩
    · rw [hp] at h; simp at h
    rw [hp] at h
    simp only [res_eq] at h
    rcases hq : run fuel q v₁ with _ | ⟨v₂, t₂⟩
    · rw [hq] at h; simp at h
    rw [hq] at h
    simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a1, a2⟩ := ihp v v₁ t₁ hp ℓ hℓ
    obtain ⟨b1, b2⟩ := ihq v₁ v₂ t₂ hq _ a1
    exact ⟨b1, by simp only [timeBoundT]; omega⟩
  | ifBlank i p q ihp ihq | ifBit i p q ihp ihq =>
    intro v v' T h ℓ hℓ
    simp only [run, res_eq] at h
    rcases hp : run fuel p v with _ | ⟨v₁, t₁⟩
    · rw [hp] at h; simp at h
    rcases hq : run fuel q v with _ | ⟨v₂, t₂⟩
    · rw [hp, hq] at h; simp at h
    rw [hp, hq] at h
    simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a1, a2⟩ := ihp v v₁ t₁ hp ℓ hℓ
    obtain ⟨b1, b2⟩ := ihq v v₂ t₂ hq ℓ hℓ
    refine ⟨fun t => ?_, ?_⟩
    · simp only [lenBoundT, vg_vjoin]; exact max_le_max (a1 t) (b1 t)
    · simp only [timeBoundT]; omega
  | loop i body ih =>
    intro v v' T h
    simp only [run, res_eq] at h
    rcases hfast : loopFast i body v with _ | ⟨vf, tf⟩
    swap
    · rw [hfast] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sound_loopFast hfast
    rw [hfast] at h
    simp only at h
    intro ℓ hℓ
    have hi : ℓ i ≤ vg v i := hℓ i
    rcases hfx : fixL (run fuel body) fuel v with _ | ⟨w, tb⟩
    · rw [hfx] at h
      simp only [res_eq] at h
      rcases hu : unrollL (run fuel body) (vg v i) v with _ | ⟨J, R⟩
      · rw [hu] at h; simp at h
      rw [hu] at h
      simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨u1, u2⟩ := unrollL_spec (i := i) ih (vg v i) v J R hu ℓ hℓ
      refine ⟨iterSupT_le fun j hj => u1 j (hj.trans hi), ?_⟩
      refine (timeBoundT_loop_le i body ℓ fun j hj => u2 j (by omega)).trans ?_
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) 2
    · rw [hfx] at h
      simp only [res_eq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨wb, hwb, hle, hvw⟩ := fixL_spec (run fuel body) fuel v w tb hfx
      have hb := ih w wb tb hwb
      have hinv : loopStepT i body (vg w) ≤ vg w :=
        ((lenBoundT_mono body) (tailB_le i _)).trans ((hb _ le_rfl).1.trans (vg_le_of_vle hle))
      have h0 : ℓ ≤ vg w := hℓ.trans hvw
      refine ⟨lenBoundT_loop_le_of_inv i body h0 hinv, ?_⟩
      refine (timeBoundT_loop_le_of_inv i body h0 hinv).trans ?_
      have r1 := roundTimeT_le body i (vg w)
      have r2 := supB_vg_le (k := k) w
      have r3 := (hb _ le_rfl).2
      exact Nat.add_le_add_right (Nat.mul_le_mul hi (by omega)) 2

/-- The certificate check: the run succeeds, below the claimed bound list and time. -/
def check (fuel : ℕ) (p : Prog k) (v claim : List ℕ) (T : ℕ) : Bool :=
  match run fuel p v with
  | some (v', t) => vle v' claim && decide (t ≤ T)
  | none => false

/-- **Bounds from a checked certificate.** -/
theorem bounds_of_check {fuel : ℕ} {p : Prog k} {v claim : List ℕ} {T : ℕ}
    (h : check fuel p v claim T = true) {ℓ : Fin k → ℕ} (hℓ : ℓ ≤ vg v) :
    lenBoundT p ℓ ≤ vg claim ∧ timeBoundT p ℓ ≤ T := by
  unfold check at h
  rcases hr : run fuel p v with _ | ⟨v', t⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := run_sound fuel p v v' t hr ℓ hℓ
  exact ⟨h1.trans (vg_le_of_vle h.1), h2.trans h.2⟩

end SigabaNeo.Tape.NB
