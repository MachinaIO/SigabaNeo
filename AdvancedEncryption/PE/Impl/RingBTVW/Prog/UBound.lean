import PE.Impl.RingBTVW.Prog.B1

/-!
# Uniform time bounds of component blocks

A crude but explicit way to bound `XProg.timeBoundT`: **`UB p M T M'`** says that from any bound
vector below `M` on every tape, `p` costs at most `T` and ends below `M'` on every tape. Uniform
bounds compose (`UB.seq`, `UB.mono`), and:

* `ub_prim`: a primitive costs `2 (M + 1) + 3` and grows the bound by at most one;
* `ub_natP`: a counter of `n ≤ M` bits;
* `ub_frame`: a framed deterministic program (`NoGrow`) costs its global bound `Prog.timeBound p M`
  and keeps the bound `M`;
* `ub_clearL`.

**`time_b1P`**: the trapdoor-row block `b1P` on inputs of at most `a`, `b` bits costs at most
`timeB1 N K k (max a b + sizeB1 N K k)`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {k : ℕ}

/-- **A uniform bound**: from tapes below `M`, cost at most `T`, tapes below `M'` after. -/
def UB (p : XProg k) (M T M' : ℕ) : Prop :=
  ∀ ℓ : Fin k → ℕ, (∀ i, ℓ i ≤ M) → timeBoundT p ℓ ≤ T ∧ ∀ i, lenBoundT p ℓ i ≤ M'

theorem UB.seq {p q : XProg k} {M T M' U M'' : ℕ} (hp : UB p M T M') (hq : UB q M' U M'') :
    UB (XProg.seq p q) M (T + U) M'' := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

theorem UB.mono {p : XProg k} {M T M' T' M'' : ℕ} (h : UB p M T M') (hT : T ≤ T') (hM : M' ≤ M'') :
    UB p M T' M'' := fun ℓ hℓ => ⟨(h ℓ hℓ).1.trans hT, fun i => ((h ℓ hℓ).2 i).trans hM⟩

theorem grow_le (p : Prim k) : p.grow ≤ 1 := by cases p <;> simp [Prim.grow]

theorem ub_prim (p : Prim k) (M : ℕ) : UB (prog (.prim p)) M (2 * (M + 1) + 3) (M + 1) := by
  intro ℓ hℓ
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_prim]
    have := supB_le_of hℓ
    have := pad_le p
    omega
  · rw [lenBoundT_prim]
    have h1 : p.lenT ℓ i ≤ p.lenT (fun _ => M) i := Prim.lenT_mono p (fun j => hℓ j) i
    have h2 : p.lenT (fun _ => M) i ≤ M + p.grow := Prim.lenT_const_le p M i
    have := grow_le p
    omega

theorem ub_clear (j : Fin k) (M : ℕ) : UB (prog (.prim (.clear j))) M (2 * (M + 1) + 3) M := by
  intro ℓ hℓ
  refine ⟨((ub_prim _ M) ℓ hℓ).1, fun i => ?_⟩
  rw [lenBoundT_prim]
  simp only [Prim.lenT, Function.update_apply]
  split_ifs
  · exact Nat.zero_le _
  · exact hℓ i

theorem ub_natP {t c : Fin k} (hct : c ≠ t) {n M : ℕ} (hn : n ≤ M) :
    UB (natP t c n) M ((2 * n + 1) * (4 * M + 12)) M := by
  intro ℓ hℓ
  obtain ⟨h1, h2⟩ := natP_bounds hct n ℓ M hℓ hn
  refine ⟨h2, fun i => (h1 i).trans ?_⟩
  simp only [natB]
  split_ifs
  · exact hn
  · exact max_le (hℓ c) hn
  · exact hℓ i

theorem ub_frame {m : ℕ} (e : Fin m ↪ Fin k) (p : Prog m) (hp : p.NoGrow) (M : ℕ) :
    UB (frame e (prog p)) M (Prog.timeBound p M) M := by
  intro ℓ hℓ
  have hc : (fun j => ℓ (e j)) ≤ fun _ => M := fun j => hℓ (e j)
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_frame, timeBoundT_prog]
    exact (Prog.timeBoundT_mono p hc).trans (Prog.timeBoundT_const_le p M)
  · show embedF e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i ≤ M
    rcases embedF_cases e ℓ (Prog.lenBoundT p fun j => ℓ (e j)) i with ⟨-, h⟩ | ⟨j, rfl, h⟩
    · rw [h]; exact hℓ i
    · rw [h]
      have := ((Prog.lenBoundT_mono p hc).trans (Prog.lenBoundT_const_le p M)) j
      rwa [Prog.lenBound_eq p hp] at this

theorem ub_clearL [NeZero k] (M : ℕ) : ∀ l : List (Fin k),
    UB (clearL l) M (l.length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)) M
  | [] => by
    intro ℓ hℓ
    simp only [clearL, List.length_nil, Nat.zero_mul, Nat.zero_add]
    refine ⟨(ub_prim (.copy 0 0) M ℓ hℓ).1, fun i => ?_⟩
    · show (Prim.copy 0 0).lenT ℓ i ≤ M
      simp only [Prim.lenT, Function.update_apply]
      split_ifs with h
      · subst h; exact hℓ 0
      · exact hℓ i
  | t :: l => by
    have := (ub_clear t M).seq (ub_clearL M l)
    refine this.mono (by simp only [List.length_cons]; ring_nf; omega) le_rfl

/-! ### The trapdoor row -/

/-- The sizes of the templates of `b1P`. -/
def sizeB1 (N K k : ℕ) : ℕ :=
  K + N + N * K + k + rowL N K k + 1 * (2 * k) * N + (N * K + rowL N K k + rowL N K k)

/-- **The time of `b1P`** from tapes below `M`. -/
def timeB1 (N K k M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * k + 1) * (4 * M + 12) + (2 * rowL N K k + 1) * (4 * M + 12) +
    (2 * rowL N K k + 1) * (4 * M + 12) + (2 * (1 * (2 * k) * N) + 1) * (4 * M + 12) +
    (2 * (N * K + rowL N K k + rowL N K k) + 1) * (4 * M + 12) +
    Prog.timeBound Prog.splitP M + Prog.timeBound Prog.gadP M + Prog.timeBound Prog.subRWP M +
    (2 * (N * K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3) +
    Prog.timeBound Prog.joinP (M + 1) +
    (b1Tapes.length * (2 * (M + 1 + 1) + 3) + (2 * (M + 1 + 1) + 3))

theorem ub_b1P (N K k M : ℕ) (hM : sizeB1 N K k ≤ M) :
    UB (b1P N K k) M (timeB1 N K k M) (M + 1) := by
  unfold sizeB1 at hM
  have u := (ub_natP (t := (2 : Fin 82)) (c := 10) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (3 : Fin 82)) (c := 10) (by decide) (n := N) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 82)) (c := 10) (by decide) (n := N * K) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 82)) (c := 10) (by decide) (n := k) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 82)) (c := 10) (by decide) (n := rowL N K k) (M := M) (by omega)).seq <|
    (ub_natP (t := (14 : Fin 82)) (c := 10) (by decide) (n := rowL N K k) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 82)) (c := 10) (by decide) (n := 1 * (2 * k) * N) (M := M)
      (by omega)).seq <|
    (ub_natP (t := (8 : Fin 82)) (c := 10) (by decide) (n := N * K + rowL N K k + rowL N K k)
      (M := M) (by omega)).seq <|
    (ub_frame eS _ Prog.noGrow_splitP M).seq <| (ub_frame eG _ Prog.noGrow_gadP M).seq <|
    (ub_frame eD _ Prog.noGrow_subRWP M).seq <|
    (ub_natP (t := (58 : Fin 82)) (c := 10) (by decide) (n := N * K - 1) (M := M)
      (by omega)).seq <|
    (ub_prim (.cons 58 true) M).seq <| (ub_frame eJ _ Prog.noGrow_joinP (M + 1)).seq <|
    ub_clearL (M + 1) b1Tapes
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeB1, Nat.add_assoc]

/-- **The time of the trapdoor-row block** on inputs of at most `a`, `b` bits. -/
theorem time_b1P (N K k a b : ℕ) :
    timeBoundT (b1P N K k) (io2 (R := 80) a b 0) ≤ timeB1 N K k (max a b + sizeB1 N K k) :=
  (ub_b1P N K k _ (by omega) _ fun i => by
    simp only [io2]; split_ifs <;> omega).1

end AdvancedEncryption.RingBTVW.Prog
