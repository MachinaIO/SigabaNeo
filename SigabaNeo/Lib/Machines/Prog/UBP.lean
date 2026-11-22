import SigabaNeo.Lib.Machines.Prog.Stream
import SigabaNeo.Lib.Machines.Prog.BoundsT

/-!
# Uniform bounds of tape programs

`UBP p M T M'`: from per-tape bounds all at most `M`, the program `p` costs at most `T` steps
(`timeBoundT`) and leaves every tape at most `M'` bits (`lenBoundT`). Uniform bounds compose
(`UBP.seq`), and loops whose body lengthens the tapes by at most `g` bits per round are bounded in
closed form (`ubp_loop`): `M` rounds, each from tapes at most `M + g M`.
-/

namespace SigabaNeo.Tape.Prog

variable {k : ℕ}

/-- **A uniform bound** of a program. -/
def UBP (p : Prog k) (M T M' : ℕ) : Prop :=
  ∀ ℓ : Fin k → ℕ, (∀ i, ℓ i ≤ M) → timeBoundT p ℓ ≤ T ∧ ∀ i, lenBoundT p ℓ i ≤ M'

theorem UBP.seq {p q : Prog k} {M T M' U M'' : ℕ} (hp : UBP p M T M') (hq : UBP q M' U M'') :
    UBP (p ⨾ q) M (T + U) M'' := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

theorem UBP.mono {p : Prog k} {M T M' T' M'' : ℕ} (h : UBP p M T M') (hT : T ≤ T')
    (hM : M' ≤ M'') : UBP p M T' M'' :=
  fun ℓ hℓ => ⟨(h ℓ hℓ).1.trans hT, fun i => ((h ℓ hℓ).2 i).trans hM⟩

theorem UBP.lower {p : Prog k} {M M₀ T M' : ℕ} (h : UBP p M T M') (hM : M₀ ≤ M) :
    UBP p M₀ T M' := fun ℓ hℓ => h ℓ fun i => (hℓ i).trans hM

theorem supB_le_of' {ℓ : Fin k → ℕ} {M : ℕ} (h : ∀ i, ℓ i ≤ M) : supB ℓ ≤ M :=
  Finset.sup_le fun i _ => h i

theorem pad_le' (p : Prim k) : p.pad ≤ 1 := by cases p <;> simp [Prim.pad]

theorem grow_le' (p : Prim k) : p.grow ≤ 1 := by cases p <;> simp [Prim.grow]

/-- A primitive: one sweep, one more bit at most. -/
theorem ubp_prim (p : Prim k) (M : ℕ) : UBP (prim p) M (2 * (M + 1) + 3) (M + 1) := by
  intro ℓ hℓ
  refine ⟨?_, fun i => ?_⟩
  · show 2 * (supB ℓ + p.pad) + 3 ≤ _
    have := supB_le_of' hℓ
    have := pad_le' p
    omega
  · show p.lenT ℓ i ≤ _
    have h1 : p.lenT ℓ i ≤ p.lenT (fun _ => M) i := Prim.lenT_mono p (fun j => hℓ j) i
    have h2 : p.lenT (fun _ => M) i ≤ M + p.grow := Prim.lenT_const_le p M i
    have := grow_le' p
    omega

/-- A primitive that lengthens no word. -/
theorem ubp_prim0 (p : Prim k) (hp : p.grow = 0) (M : ℕ) :
    UBP (prim p) M (2 * (M + 1) + 3) M := by
  intro ℓ hℓ
  refine ⟨((ubp_prim p M) ℓ hℓ).1, fun i => ?_⟩
  show p.lenT ℓ i ≤ _
  have h1 : p.lenT ℓ i ≤ p.lenT (fun _ => M) i := Prim.lenT_mono p (fun j => hℓ j) i
  have h2 : p.lenT (fun _ => M) i ≤ M + p.grow := Prim.lenT_const_le p M i
  omega

theorem ubp_ifBlank {i : Fin k} {p q : Prog k} {M T M' U M'' : ℕ} (hp : UBP p M T M')
    (hq : UBP q M U M'') : UBP (ifBlank i p q) M (max T U + 1) (max M' M'') := fun ℓ hℓ =>
  ⟨by show max _ _ + 1 ≤ _; have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => by show max _ _ ≤ _; exact max_le_max ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

theorem ubp_ifBit {i : Fin k} {p q : Prog k} {M T M' U M'' : ℕ} (hp : UBP p M T M')
    (hq : UBP q M U M'') : UBP (ifBit i p q) M (max T U + 1) (max M' M'') := fun ℓ hℓ =>
  ⟨by show max _ _ + 1 ≤ _; have := (hp ℓ hℓ).1; have := (hq ℓ hℓ).1; omega,
    fun t => by show max _ _ ≤ _; exact max_le_max ((hp ℓ hℓ).2 t) ((hq ℓ hℓ).2 t)⟩

/-- A program from its global bounds. -/
theorem ubp_global (p : Prog k) (M : ℕ) : UBP p M (timeBound p M) (lenBound p M) := by
  intro ℓ hℓ
  have hc : ℓ ≤ fun _ => M := hℓ
  exact ⟨(timeBoundT_mono p hc).trans (timeBoundT_const_le p M),
    fun i => ((lenBoundT_mono p hc).trans (lenBoundT_const_le p M)) i⟩

/-- **A loop whose body lengthens the tapes by at most `g` bits per round.** -/
theorem ubp_loop (i : Fin k) (body : Prog k) (g : ℕ) (Tb : ℕ → ℕ)
    (hb : ∀ M', UBP body M' (Tb M') (M' + g)) (M : ℕ) :
    UBP (loop i body) M (M * (2 * (M + g * M) + 3 + Tb (M + g * M) + 1) + 2) (M + g * M) := by
  intro ℓ hℓ
  have hit : ∀ j t, ((loopStepT i body)^[j] ℓ) t ≤ M + g * j := by
    intro j
    induction j with
    | zero => intro t; simpa using hℓ t
    | succ j ih =>
      intro t
      rw [Function.iterate_succ_apply']
      have h := ((hb (M + g * j)) (tailB i ((loopStepT i body)^[j] ℓ))
        (fun u => (tailB_le i _ u).trans (ih u))).2 t
      show lenBoundT body _ t ≤ _
      rw [Nat.mul_succ]; omega
  have hiM : ℓ i ≤ M := hℓ i
  refine ⟨?_, fun t => ?_⟩
  · refine (timeBoundT_loop_le i body ℓ (R := 2 * (M + g * M) + 3 + Tb (M + g * M))
      fun j hj => ?_).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hiM) 2)
    have hle : ∀ u, ((loopStepT i body)^[j] ℓ) u ≤ M + g * M := fun u =>
      (hit j u).trans (by have := Nat.mul_le_mul_left g (show j ≤ M by omega); omega)
    show 2 * supB _ + 3 + timeBoundT body _ ≤ _
    have h1 := supB_le_of' hle
    have h2 := ((hb (M + g * M)) (tailB i ((loopStepT i body)^[j] ℓ))
      (fun u => (tailB_le i _ u).trans (hle u))).1
    omega
  · rw [lenBoundT_loop]
    refine iterSupT_le (ℓ' := fun _ => M + g * M) (fun j hj u => (hit j u).trans ?_) t
    have := Nat.mul_le_mul_left g (hj.trans hiM)
    show M + g * j ≤ M + g * M
    omega

end SigabaNeo.Tape.Prog
