import PE.Impl.ExpLUT.Prog.RedKeyMFront

/-!
# Module 9 (certificates): the length field fails for the current `rkKeyP`

`XProg.lenBoundT` is a *static* bound: a loop's bound is the supremum over all its rounds,
**including round `0`**, so the counter tape of `forN c t body` keeps the bound `ℓ t` after the
loop although it is blank at run time. In the invalid branch `rkInvP`, the last phase
`appT 0 1 2 3 ⨾ clr 1` counts on tape `2` (`forN 2 1 …`) and nothing clears tape `2` afterwards,
so the static bound of tape `2` after `rkKeyP mid` is at least `|keyEnc| = codecSize (keyEnc Dc)`:

* **`lenBoundT_rkKeyP_two_ge`**: `codecSize (keyEnc Dc) ≤ lenBoundT (rkKeyP mid) ℓ 2` (every `mid`,
  every `ℓ`);
* **`not_len_rkKeyP`**: if `0 < codecSize (keyEnc Dc)`, `¬ lenBoundT (rkKeyP mid) ℓ ≤ io2 Lk 0 0`.

So `Sub.keyCompOf`'s `hlen` cannot be discharged for `rkKeyP` as defined in `RedKeyMFront`;
`RedKeyTFront` gives the fixed component (scratch tapes cleared).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-! ### Lower bounds for static length bounds -/

theorem iterate_add_one_at {k : ℕ} (t : Fin k) (g : (Fin k → ℕ) → (Fin k → ℕ))
    (hg : ∀ ℓ', g ℓ' t = ℓ' t + 1) : ∀ (j : ℕ) (ℓ : Fin k → ℕ), (g^[j] ℓ) t = ℓ t + j
  | 0, ℓ => rfl
  | j + 1, ℓ => by
    rw [Function.iterate_succ_apply', hg, iterate_add_one_at t g hg j ℓ]
    omega

/-- **Doubling doubles the bound** of `t`. -/
theorem dblP_bound_ge {k : ℕ} {t c : Fin k} (hct : c ≠ t) (ℓ : Fin k → ℕ) :
    2 * ℓ t ≤ XProg.lenBoundT (dblP t c) ℓ t := by
  set ℓ1 : Fin k → ℕ := Function.update ℓ c (ℓ t) with hℓ1
  set g : (Fin k → ℕ) → (Fin k → ℕ) := fun ℓ' => XProg.lenBoundT (bitAp t false) (tailB c ℓ')
  have e : XProg.lenBoundT (dblP t c) ℓ = iterSupT g (ℓ1 c) ℓ1 := rfl
  have hg : ∀ ℓ', g ℓ' t = ℓ' t + 1 := fun ℓ' => by
    show Prim.lenT (.snoc t false) (tailB c ℓ') t = _
    simp only [Prim.lenT, Function.update_self, tailB, Function.update_of_ne hct.symm]
  have h := le_iterSupT g (n := ℓ1 c) (j := ℓ1 c) le_rfl ℓ1 t
  rw [iterate_add_one_at t g hg] at h
  have h1 : ℓ1 t = ℓ t := by simp [hℓ1, Function.update_of_ne hct.symm]
  have h2 : ℓ1 c = ℓ t := by simp [hℓ1]
  rw [e]
  calc 2 * ℓ t = ℓ1 t + ℓ1 c := by rw [h1, h2]; ring
    _ ≤ _ := h

/-- **`natP` builds at least `n`** on `t` (statically). -/
theorem natP_bound_ge {k : ℕ} {t c : Fin k} (hct : c ≠ t) :
    ∀ (n : ℕ) (ℓ : Fin k → ℕ), n ≤ XProg.lenBoundT (natP t c n) ℓ t
  | 0, _ => Nat.zero_le _
  | n + 1, ℓ => by
    have ih := natP_bound_ge hct ((n + 1) / 2)
    rw [natP]
    split_ifs with h
    · show n + 1 ≤ XProg.lenBoundT (dblP t c) (XProg.lenBoundT (natP t c ((n + 1) / 2)) ℓ) t
      have := dblP_bound_ge hct (XProg.lenBoundT (natP t c ((n + 1) / 2)) ℓ)
      have := ih ℓ
      omega
    · show n + 1 ≤ Prim.lenT (.snoc t false)
        (XProg.lenBoundT (dblP t c) (XProg.lenBoundT (natP t c ((n + 1) / 2)) ℓ)) t
      simp only [Prim.lenT, Function.update_self]
      have := dblP_bound_ge hct (XProg.lenBoundT (natP t c ((n + 1) / 2)) ℓ)
      have := ih ℓ
      omega

/-- The counter tape `2` of `appT 0 1 2 3` keeps the bound of tape `1`. -/
theorem appT_counter_ge (ℓ : Fin 247 → ℕ) :
    ℓ 1 ≤ Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ 2 := by
  set ℓ1 : Fin 247 → ℕ := Function.update ℓ 3 (ℓ 1)
  set ℓ2 : Fin 247 → ℕ := Function.update ℓ1 2 (ℓ1 1)
  have e : Prog.lenBoundT (appT (0 : Fin 247) 1 2 3 ⨾ clr 1) ℓ 2 =
      iterSupT (Prog.loopStepT 2 (appBody 0 3)) (ℓ2 2) ℓ2 2 := by
    show Prim.lenT (.clear 1) (Prim.lenT (.clear 3)
      (Prog.lenBoundT (Prog.loop 2 (appBody 0 3)) ℓ2)) 2 = _
    simp only [Prim.lenT, Function.update_apply]
    rfl
  rw [e]
  have h := le_iterSupT (Prog.loopStepT 2 (appBody (0 : Fin 247) 3)) (n := ℓ2 2) (j := 0)
    (Nat.zero_le _) ℓ2 2
  refine le_trans ?_ h
  simp [ℓ2, ℓ1]

/-! ### The static bound of tape `2` after `rkKeyP` -/

/-- The shape of `rkInvP`, generic in the key length `n`. -/
theorem inv_shape_two_ge (A B : XProg 247) (n : ℕ) (ℓ : Fin 247 → ℕ) :
    n ≤ XProg.lenBoundT (.seq A (.seq B (.seq (natP 1 2 n) (.prog (appT 0 1 2 3 ⨾ clr 1))))) ℓ 2 :=
  (natP_bound_ge (by decide) _ _).trans (appT_counter_ge _)

/-- **The invalid branch leaves the bound `|keyEnc|` on tape `2`.** -/
theorem lenBoundT_rkInvP_two_ge (ℓ : Fin 247 → ℕ) :
    codecSize (keyEnc Dc) ≤ XProg.lenBoundT rkInvP ℓ 2 := by
  unfold rkInvP
  exact inv_shape_two_ge _ _ _ ℓ

/-- The shape of `rkKeyOf`: tape `2` after the invalid branch is a lower bound. -/
theorem keyOf_shape_two_ge (L Y V I Z : XProg 247) (ℓ : Fin 247 → ℕ) :
    XProg.lenBoundT I (XProg.lenBoundT Y (XProg.lenBoundT L ℓ)) 2 ≤
      XProg.lenBoundT (.seq L (.ifBit 2 (.seq Y (.ifBit 2 V I)) Z)) ℓ 2 :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem lenBoundT_rkKeyOf_two_ge (vP : XProg 247) (ℓ : Fin 247 → ℕ) :
    codecSize (keyEnc Dc) ≤ XProg.lenBoundT (rkKeyOf vP) ℓ 2 := by
  unfold rkKeyOf
  exact (lenBoundT_rkInvP_two_ge _).trans (keyOf_shape_two_ge _ _ _ _ _ ℓ)

/-- **The static bound of tape `2` after `rkKeyP mid` is at least `|keyEnc|`**, for every `mid`. -/
theorem lenBoundT_rkKeyP_two_ge (mid : XProg 247) (ℓ : Fin 247 → ℕ) :
    codecSize (keyEnc Dc) ≤ XProg.lenBoundT (rkKeyP mid) ℓ 2 :=
  lenBoundT_rkKeyOf_two_ge _ ℓ

/-- **The `len` field of `Sub.KeyComp` fails for `rkKeyP mid`** (whatever `mid`, `Lk`, `ℓ`). -/
theorem not_len_rkKeyP (hk : 0 < codecSize (keyEnc Dc)) (mid : XProg 247) (ℓ : Fin 247 → ℕ)
    (Lk : ℕ) : ¬ XProg.lenBoundT (rkKeyP mid) ℓ ≤ io2 (R := 245) Lk 0 0 := by
  intro h
  have h2 := (lenBoundT_rkKeyP_two_ge mid ℓ).trans (h 2)
  simp [io2] at h2
  omega

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
