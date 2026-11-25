import PE.Impl.RingBTVW.Prog.UBound
import PE.Impl.RingBTVW.Prog.SetupTime3
import SigabaNeo.Lib.Machines.Prog.FrameOut

/-!
# Uniform bounds of loops, appends and framed blocks

Further uniform bounds (`UB p M T M'`: from tapes below `M`, cost at most `T`, tapes below `M'`
after), for the programs that assemble the outputs of `Setup` and `Enc`:

* `ub_copyS`: a copy keeps the bound;
* **`ub_loop`**, `ub_forN`: a loop whose body grows every tape by at most `g` per round, from a
  counter of at most `n` (resp. `M`) bits;
* `ub_appendTapeP`, `ub_frameApP`: appending a tape (resp. its frame) at most doubles (triples)
  the bound;
* `ub_frameLe`: a framed block keeps its bound;
* `ub_of_atb`: a framed sampler with a shape bound (`ATBb`, `PE.Impl.RingBTVW.Prog.SetupTime3`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {k : ℕ}

theorem ub_copyS (i j : Fin k) (M : ℕ) : UB (prog (.prim (.copy i j))) M (2 * (M + 1) + 3) M := by
  intro ℓ hℓ
  refine ⟨((ub_prim _ M) ℓ hℓ).1, fun t => ?_⟩
  rw [lenBoundT_prim]
  simp only [Prim.lenT, Function.update_apply]
  split_ifs
  · exact hℓ j
  · exact hℓ t

/-- The time of a loop of at most `n` rounds from tapes below `M`, a round growing by `g`. -/
def loopT (T : ℕ → ℕ) (g M n : ℕ) : ℕ := n * (2 * (M + n * g) + 3 + T (M + n * g) + 1) + 2

/-- **A loop** of at most `n` rounds whose body grows every tape by at most `g`. -/
theorem ub_loop {i : Fin k} {body : XProg k} {g : ℕ} {T : ℕ → ℕ}
    (hb : ∀ X, UB body X (T X) (X + g)) {M n : ℕ} (ℓ : Fin k → ℕ) (hℓ : ∀ j, ℓ j ≤ M)
    (hn : ℓ i ≤ n) :
    timeBoundT (loop i body) ℓ ≤ loopT T g M n ∧ ∀ j, lenBoundT (loop i body) ℓ j ≤ M + n * g := by
  have hit : ∀ j, ∀ t, ((loopStepT i body)^[j] ℓ) t ≤ M + j * g := by
    intro j
    induction j with
    | zero => intro t; simpa using hℓ t
    | succ j ih =>
      intro t
      rw [Function.iterate_succ_apply']
      have h1 : ∀ t, tailB i ((loopStepT i body)^[j] ℓ) t ≤ M + j * g :=
        fun t => (tailB_le i _ t).trans (ih t)
      have := (hb (M + j * g) _ h1).2 t
      rw [loopStepT]
      refine this.trans (le_of_eq ?_)
      ring
  refine ⟨?_, fun t => ?_⟩
  · refine (timeBoundT_loop_le i body ℓ (R := 2 * (M + n * g) + 3 + T (M + n * g))
      fun j hj => ?_).trans ?_
    · have hj' : j ≤ n := by omega
      have hb' : ∀ t, ((loopStepT i body)^[j] ℓ) t ≤ M + n * g := fun t =>
        (hit j t).trans (by have := Nat.mul_le_mul_right g hj'; omega)
      unfold Prog.roundTimeT
      have h1 := supB_le_of hb'
      have h2 : ∀ t, tailB i ((loopStepT i body)^[j] ℓ) t ≤ M + n * g :=
        fun t => (tailB_le i _ t).trans (hb' t)
      have h3 := (hb (M + n * g) _ h2).1
      omega
    · unfold loopT
      exact Nat.add_le_add_right (Nat.mul_le_mul hn le_rfl) 2
  · show iterSupT (fun ℓ' => lenBoundT body (tailB i ℓ')) (ℓ i) ℓ t ≤ M + n * g
    refine iterSupT_le (ℓ' := fun _ => M + n * g) (fun j hj t => ?_) t
    show _ ≤ M + n * g
    exact (hit j t).trans (by have := Nat.mul_le_mul_right g (hj.trans hn); omega)

/-- The time of `forN` from tapes below `M` (at most `M` rounds). -/
def forT (T : ℕ → ℕ) (g M : ℕ) : ℕ := 2 * (M + 1) + 3 + loopT T g M M

theorem ub_forN {c t : Fin k} {body : XProg k} {g : ℕ} {T : ℕ → ℕ}
    (hb : ∀ X, UB body X (T X) (X + g)) (M : ℕ) :
    UB (forN c t body) M (forT T g M) (M + M * g) := by
  intro ℓ hℓ
  have h1 := ub_copyS c t M ℓ hℓ
  have h2 := ub_loop (i := c) hb (M := M) (n := M) _ h1.2 (h1.2 c)
  exact ⟨Nat.add_le_add h1.1 h2.1, h2.2⟩

/-- The time of one round of `appendTapeP` and `frameApP`. -/
def stepT (X : ℕ) : ℕ := 3 * (2 * (X + 3) + 3)

theorem ub_appStep (r S : Fin k) (X : ℕ) :
    UB (seq (prog (.prim (.snocHead r S))) (prog (.prim (.tail S)))) X (stepT X) (X + 3) := by
  have h1 : UB (prog (.prim (.snocHead r S))) X (2 * (X + 1) + 3) (X + 1) := ub_prim _ X
  have h2 : UB (prog (.prim (.tail S))) (X + 1) (2 * (X + 1 + 1) + 3) (X + 1 + 1) := ub_prim _ _
  exact (h1.seq h2).mono (by unfold stepT; omega) (by omega)

theorem ub_frStep (r S : Fin k) (X : ℕ) :
    UB (seq (prog (.prim (.snoc r true))) (seq (prog (.prim (.snocHead r S)))
      (prog (.prim (.tail S))))) X (stepT X) (X + 3) := by
  have h1 : UB (prog (.prim (.snoc r true))) X (2 * (X + 1) + 3) (X + 1) := ub_prim _ X
  have h2 : UB (prog (.prim (.snocHead r S))) (X + 1) (2 * (X + 1 + 1) + 3) (X + 1 + 1) :=
    ub_prim _ _
  have h3 : UB (prog (.prim (.tail S))) (X + 1 + 1) (2 * (X + 1 + 1 + 1) + 3) (X + 1 + 1 + 1) :=
    ub_prim _ _
  exact (h1.seq (h2.seq h3)).mono (by unfold stepT; omega) (by omega)

/-- The time of appending a tape (or its frame) from tapes below `M`. -/
def appT (M : ℕ) : ℕ := 3 * (2 * (M + 3 * M + 3) + 3) + forT stepT 3 M

theorem ub_appendTapeP (r a S c : Fin k) (M : ℕ) :
    UB (appendTapeP r a S c) M (appT M) (4 * M + 1) := by
  have u := (ub_copyS S a M).seq <| (ub_forN (c := c) (t := a) (ub_appStep r S) M).seq <|
    (ub_clear S (M + M * 3)).seq (ub_clear a (M + M * 3))
  refine u.mono ?_ (by omega)
  unfold appT forT stepT
  have : 2 * (M + M * 3 + 1) ≤ 2 * (M + 3 * M + 3) := by omega
  omega

theorem ub_frameApP (r a S c : Fin k) (M : ℕ) :
    UB (frameApP r a S c) M (appT M) (4 * M + 1) := by
  have u := (ub_copyS S a M).seq <| (ub_forN (c := c) (t := a) (ub_frStep r S) M).seq <|
    (ub_prim (.snoc r false) (M + M * 3)).seq (ub_clear S (M + M * 3 + 1))
  refine u.mono ?_ (by omega)
  unfold appT forT stepT
  omega

/-- **A framed block keeps its uniform bound.** -/
theorem ub_frameLe {m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {M T M' : ℕ} (h : UB p M T M')
    (hM : M ≤ M') : UB (frame e p) M T M' := by
  intro ℓ hℓ
  have hc : ∀ j, (fun j => ℓ (e j)) j ≤ M := fun j => hℓ (e j)
  refine ⟨(h _ hc).1, fun i => ?_⟩
  show embedF e ℓ (lenBoundT p fun j => ℓ (e j)) i ≤ M'
  rcases embedF_cases e ℓ (lenBoundT p fun j => ℓ (e j)) i with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
  · rw [h']; exact (hℓ i).trans hM
  · rw [h']; exact (h _ hc).2 j

/-- **A framed sampler with a shape bound.** -/
theorem ub_of_atb (e : Fin 7 ↪ Fin k) {p : XProg 7} {B : Bnd} (h : ATBb p B) {M : ℕ}
    (hM : B.S₀ ≤ M) : UB (frame e p) M (B.T M M) (M + B.a + B.s) := by
  refine ub_frameLe e (fun ℓ hℓ => ?_) (by omega)
  have hsh : ℓ ≤ shp (0 : Fin 7) M M := fun i => by simp only [shp]; split_ifs <;> exact hℓ i
  refine ⟨ATB.time h hM hsh, fun i => ?_⟩
  have := ((lenBoundT_mono p hsh).trans (h M M hM).2) i
  simp only [shp] at this
  split_ifs at this <;> omega

end AdvancedEncryption.RingBTVW.Prog
