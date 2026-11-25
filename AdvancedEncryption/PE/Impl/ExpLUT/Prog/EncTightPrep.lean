import PE.Impl.ExpLUT.Prog.EncTightBase
/-!
# Per-tape bounds of the encryption parser (tight encryption clock, part 6)

The coin sampler is charged by the length of its output register and the common bound of its
six other tapes (`ATB`). From the loaded input (`inputBound 0 n`), the parser leaves the input
tape at most `n` bits and the public word (tape `1`) at most `3 n` (`lenBoundT_parse_le`), not
the common cap `2^104` of the uniform analysis, so the sampler costs at most `2^252` steps.
-/

namespace AdvancedEncryption.ExpLUT.Prog.EncTight

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog

/-- The per-tape effect of one frame parse placed by `u`. -/
def ustep {k : ℕ} (u : Fin 4 → Fin k) (B : Fin k → ℕ) : Fin k → ℕ := fun t =>
  if t = u 2 then B (u 0) else if t = u 1 then B t + B (u 0) else if t = u 3 then 0 else B t

theorem ustep_mono {k : ℕ} (u : Fin 4 → Fin k) : Monotone (ustep u) := by
  intro A B h t
  unfold ustep
  split_ifs
  · exact h _
  · exact Nat.add_le_add (h _) (h _)
  · exact le_rfl
  · exact h _

/-- The growth of one round of the parse loop: one bit on the output and on the flag. -/
def δU {k : ℕ} (u : Fin 4 → Fin k) (t : Fin k) : ℕ :=
  (if t = u 1 then 1 else 0) + (if t = u 3 then 1 else 0)

theorem lenBoundT_unfrBody_le {k : ℕ} (u : Fin 4 → Fin k) (hu : Function.Injective u)
    (ℓ : Fin k → ℕ) (t : Fin k) : lenBoundT (map u unfrBody) ℓ t ≤ ℓ t + δU u t := by
  have h01 : u 0 ≠ u 1 := hu.ne (by decide)
  have h03 : u 0 ≠ u 3 := hu.ne (by decide)
  have h13 : u 1 ≠ u 3 := hu.ne (by decide)
  simp only [map, unfrBody, Prim.map, lenBoundT, Prim.lenT, Function.update_apply, δU]
  by_cases a1 : t = u 1
  · subst a1; simp [h01.symm, h13]
  · by_cases a3 : t = u 3
    · subst a3; simp [h03.symm, h13.symm]
    · by_cases a0 : t = u 0
      · subst a0; simp [h01, h03]
      · simp [a1, a3, a0]

theorem iter_loopStep_le {k : ℕ} (u : Fin 4 → Fin k) (hu : Function.Injective u)
    (ℓ : Fin k → ℕ) :
    ∀ j, (loopStepT (u 2) (map u unfrBody))^[j] ℓ ≤ fun t => ℓ t + j * δU u t := by
  intro j
  induction j with
  | zero => intro t; simp
  | succ j ih =>
    intro t
    rw [Function.iterate_succ_apply']
    refine ((lenBoundT_mono _ (tailB_le (u 2) _)) t).trans ?_
    refine (lenBoundT_unfrBody_le u hu _ t).trans ?_
    have := ih t
    simp only [Nat.succ_mul] at this ⊢; omega

/-- **One frame parse**: per-tape effect. -/
theorem lenBoundT_unfr_le {k : ℕ} (u : Fin 4 → Fin k) (hu : Function.Injective u)
    (ℓ : Fin k → ℕ) : lenBoundT (map u unfrP) ℓ ≤ ustep u ℓ := by
  intro t
  set ℓ' := Function.update ℓ (u 2) (ℓ (u 0)) with hℓ'
  have hloop : lenBoundT (loop (u 2) (map u unfrBody)) ℓ' ≤ fun t => ℓ' t + ℓ' (u 2) * δU u t :=
    iterSupT_le fun j hj t => ((iter_loopStep_le u hu ℓ' j) t).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _)
  have e : lenBoundT (map u unfrP) ℓ =
      Function.update (lenBoundT (loop (u 2) (map u unfrBody)) ℓ') (u 3) 0 := rfl
  rw [e]
  have h20 : u 2 ≠ u 0 := hu.ne (by decide)
  have h21 : u 2 ≠ u 1 := hu.ne (by decide)
  have h23 : u 2 ≠ u 3 := hu.ne (by decide)
  have h13 : u 1 ≠ u 3 := hu.ne (by decide)
  have hl := hloop t
  simp only [ustep, Function.update_apply, δU] at hl ⊢
  by_cases a3 : t = u 3
  · simp [a3]
  · rw [if_neg a3]
    simp only [hℓ', Function.update_apply] at hl
    split_ifs at hl ⊢ <;> simp_all

end AdvancedEncryption.ExpLUT.Prog.EncTight
