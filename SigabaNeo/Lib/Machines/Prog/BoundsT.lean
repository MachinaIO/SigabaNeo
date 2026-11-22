import SigabaNeo.Lib.Machines.Prog.Basic

/-!
# Per-tape length and time bounds of tape programs

`lenBound` and `timeBound` (`SigabaNeo.Lib.Machines.Prog.Basic`) take one bound `L` on the length of
every word of the store, so a loop is charged `L` rounds even when its counter is short. Here the
bound is a vector `ℓ : Fin k → ℕ`, one entry per tape (`Fits s ℓ`: `|s i| ≤ ℓ i` for every `i`).

* `lenBoundT p ℓ` bounds each tape after `p` separately (`lenBoundT_spec`).
* `timeBoundT p ℓ` bounds the steps of the compiled machine (`compile_runsWordsT`, in
  `SigabaNeo.Lib.Machines.Prog.CompileT`). A primitive still costs `2 (supB ℓ + pad) + 3`, where
  `supB ℓ` is the largest entry (its column machine sweeps every tape), but `loop i body` is charged
  `ℓ i` rounds, the bound of its own counter tape. Round `j` is charged at the iterated bound
  `(loopStepT i body)^[j] ℓ` (the counter shrinks by one each round, the body acts on the rest).

The loop bounds are stated through the iterated bounds, as in `lenBound_spec`, so no monotonicity is
needed for soundness. Both bounds are monotone in `ℓ` (`lenBoundT_mono`, `timeBoundT_mono`), which
gives the invariant forms `timeBoundT_loop_le_of_inv`, `lenBoundT_loop_le_of_inv`: a loop over a
counter of length at most `ℓ i` whose rounds stay below an invariant bound `ℓ'` costs at most
`ℓ i · (roundTimeT … ℓ' + 1) + 2`.

From the constant bound `fun _ => L` the per-tape bounds refine the global ones
(`lenBoundT_const_le`, `timeBoundT_const_le`).
-/

namespace SigabaNeo.Tape

open Cslib Turing

variable {k : ℕ}

/-! ### Per-tape bounds on stores -/

/-- Every word of the store `s` fits its own bound: `|s i| ≤ ℓ i`. -/
def Fits (s : Store k) (ℓ : Fin k → ℕ) : Prop := ∀ i, (s i).length ≤ ℓ i

/-- The largest per-tape bound. -/
def supB (ℓ : Fin k → ℕ) : ℕ := Finset.univ.sup ℓ

theorem le_supB (ℓ : Fin k → ℕ) (i : Fin k) : ℓ i ≤ supB ℓ :=
  Finset.le_sup (f := ℓ) (Finset.mem_univ i)

theorem supB_mono {ℓ ℓ' : Fin k → ℕ} (h : ℓ ≤ ℓ') : supB ℓ ≤ supB ℓ' :=
  Finset.sup_mono_fun fun i _ => h i

theorem supB_const_le (L : ℕ) : supB (fun _ : Fin k => L) ≤ L :=
  Finset.sup_le fun _ _ => le_rfl

theorem Fits.maxLen_le {s : Store k} {ℓ : Fin k → ℕ} (hs : Fits s ℓ) : maxLen s ≤ supB ℓ :=
  (maxLen_le_iff s _).mpr fun i => (hs i).trans (le_supB ℓ i)

theorem fits_const_iff (s : Store k) (L : ℕ) : Fits s (fun _ => L) ↔ maxLen s ≤ L :=
  (maxLen_le_iff s L).symm

theorem Fits.update {s : Store k} {ℓ : Fin k → ℕ} (hs : Fits s ℓ) (i : Fin k) {w : List Bool}
    {n : ℕ} (hw : w.length ≤ n) : Fits (Function.update s i w) (Function.update ℓ i n) := by
  intro t
  by_cases ht : t = i
  · subst ht; simpa using hw
  · simpa [ht] using hs t

theorem Fits.mono {s : Store k} {ℓ ℓ' : Fin k → ℕ} (hs : Fits s ℓ) (h : ℓ ≤ ℓ') : Fits s ℓ' :=
  fun i => (hs i).trans (h i)

theorem update_le_update {ℓ ℓ' : Fin k → ℕ} (h : ℓ ≤ ℓ') (i : Fin k) {a b : ℕ} (hab : a ≤ b) :
    Function.update ℓ i a ≤ Function.update ℓ' i b := by
  intro t
  by_cases ht : t = i
  · subst ht; simpa using hab
  · simpa [ht] using h t

/-- The bound after dropping the first bit of tape `i`. -/
def tailB (i : Fin k) (ℓ : Fin k → ℕ) : Fin k → ℕ := Function.update ℓ i (ℓ i - 1)

theorem fits_tailAt {s : Store k} {ℓ : Fin k → ℕ} (hs : Fits s ℓ) (i : Fin k) :
    Fits (tailAt i s) (tailB i ℓ) :=
  hs.update i (by have := hs i; simp only [List.length_tail]; omega)

theorem tailB_mono (i : Fin k) : Monotone (tailB (k := k) i) :=
  fun _ _ h => update_le_update h i (Nat.sub_le_sub_right (h i) 1)

theorem tailB_le (i : Fin k) (ℓ : Fin k → ℕ) : tailB i ℓ ≤ ℓ := by
  intro t
  by_cases ht : t = i
  · subst ht; simp [tailB]
  · simp [tailB, ht]

/-! ### Primitives -/

namespace Prim

/-- The per-tape bound after a primitive. -/
def lenT : Prim k → (Fin k → ℕ) → (Fin k → ℕ)
  | clear i, ℓ => Function.update ℓ i 0
  | copy i j, ℓ => Function.update ℓ i (ℓ j)
  | carry _ _ _, ℓ => ℓ
  | tail i, ℓ => Function.update ℓ i (ℓ i - 1)
  | pop i j, ℓ => Function.update (Function.update ℓ i (ℓ i - 1)) j (min 1 (ℓ i))
  | eq _ _ f, ℓ => Function.update ℓ f 1
  | cons i _, ℓ | snoc i _, ℓ | consHead i _, ℓ | snocHead i _, ℓ =>
    Function.update ℓ i (ℓ i + 1)

theorem fits_apply (p : Prim k) {s : Store k} {ℓ : Fin k → ℕ} (hs : Fits s ℓ) :
    Fits (p.apply s) (p.lenT ℓ) := by
  cases p with
  | clear i => exact hs.update i (by simp)
  | copy i j => exact hs.update i (hs j)
  | carry f i j =>
    intro t
    by_cases ht : t = i
    · subst ht; simpa [apply, lenT] using hs t
    · simpa [apply, lenT, ht] using hs t
  | tail i => exact hs.update i (by have := hs i; simp only [List.length_tail]; omega)
  | pop i j =>
    exact (hs.update i (by have := hs i; simp only [List.length_tail]; omega)).update j
      (by have := hs i; simp only [List.length_take]; omega)
  | eq i j f => exact hs.update f (by simp)
  | cons i b => exact hs.update i (by simpa using hs i)
  | snoc i b => exact hs.update i (by simpa using hs i)
  | consHead i j =>
    exact hs.update i (by have := hs i; simp only [List.length_append, List.length_take]; omega)
  | snocHead i j =>
    exact hs.update i (by have := hs i; simp only [List.length_append, List.length_take]; omega)

theorem lenT_mono (p : Prim k) : Monotone p.lenT := by
  intro ℓ ℓ' h
  cases p with
  | clear i => exact update_le_update h i le_rfl
  | copy i j => exact update_le_update h i (h j)
  | carry f i j => exact h
  | tail i => exact update_le_update h i (Nat.sub_le_sub_right (h i) 1)
  | pop i j =>
    exact update_le_update (update_le_update h i (Nat.sub_le_sub_right (h i) 1)) j
      (min_le_min le_rfl (h i))
  | eq i j f => exact update_le_update h f le_rfl
  | cons i b | snoc i b | consHead i j | snocHead i j =>
    exact update_le_update h i (Nat.add_le_add_right (h i) 1)

theorem lenT_of_not_mem (p : Prim k) (ℓ : Fin k → ℕ) {t : Fin k} (ht : t ∉ p.writes) :
    p.lenT ℓ t = ℓ t := by
  cases p <;> simp_all [writes, lenT, Function.update]

end Prim

/-! ### Programs -/

/-- The pointwise largest value of `(g^[j] ℓ) t` over `j ≤ n`. -/
def iterSupT (g : (Fin k → ℕ) → (Fin k → ℕ)) (n : ℕ) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  fun t => (Finset.range (n + 1)).sup fun j => (g^[j] ℓ) t

theorem le_iterSupT (g : (Fin k → ℕ) → (Fin k → ℕ)) {n j : ℕ} (hj : j ≤ n) (ℓ : Fin k → ℕ) :
    g^[j] ℓ ≤ iterSupT g n ℓ :=
  fun t => Finset.le_sup (f := fun j => (g^[j] ℓ) t) (Finset.mem_range.mpr (by omega))

theorem iterSupT_le {g : (Fin k → ℕ) → (Fin k → ℕ)} {n : ℕ} {ℓ ℓ' : Fin k → ℕ}
    (h : ∀ j ≤ n, g^[j] ℓ ≤ ℓ') : iterSupT g n ℓ ≤ ℓ' :=
  fun t => Finset.sup_le fun j hj => h j (by simp at hj; omega) t

theorem iterSupT_mono {g : (Fin k → ℕ) → (Fin k → ℕ)} (hg : Monotone g) {n n' : ℕ} (hn : n ≤ n')
    {ℓ ℓ' : Fin k → ℕ} (h : ℓ ≤ ℓ') : iterSupT g n ℓ ≤ iterSupT g n' ℓ' :=
  iterSupT_le fun j hj => ((hg.iterate j) h).trans (le_iterSupT g (hj.trans hn) ℓ')

namespace Prog

/-- **The per-tape length bound** after a program, from per-tape bounds `ℓ` before it. -/
def lenBoundT : Prog k → (Fin k → ℕ) → (Fin k → ℕ)
  | prim p, ℓ => p.lenT ℓ
  | coin i, ℓ => Function.update ℓ i 1
  | seq p q, ℓ => lenBoundT q (lenBoundT p ℓ)
  | ifBlank _ p q, ℓ => fun t => max (lenBoundT p ℓ t) (lenBoundT q ℓ t)
  | ifBit _ p q, ℓ => fun t => max (lenBoundT p ℓ t) (lenBoundT q ℓ t)
  | loop i body, ℓ => iterSupT (fun ℓ' => lenBoundT body (tailB i ℓ')) (ℓ i) ℓ

/-- The bound after one round of `loop i body`: drop the first bit of tape `i`, run `body`. -/
def loopStepT (i : Fin k) (body : Prog k) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  lenBoundT body (tailB i ℓ)

theorem lenBoundT_loop (i : Fin k) (body : Prog k) (ℓ : Fin k → ℕ) :
    lenBoundT (loop i body) ℓ = iterSupT (loopStepT i body) (ℓ i) ℓ := rfl

/-- The time of one round of a loop on tape `i` from per-tape bounds `ℓ`: the column machine
dropping the first bit of the counter, then the body. -/
def roundTimeT (bodyTime : (Fin k → ℕ) → ℕ) (i : Fin k) (ℓ : Fin k → ℕ) : ℕ :=
  (2 * supB ℓ + 3) + bodyTime (tailB i ℓ)

/-- **The per-tape time bound**: a bound on the steps of the compiled machine from per-tape bounds
`ℓ`. A loop is charged `ℓ i` rounds, the bound of its counter tape. -/
def timeBoundT : Prog k → (Fin k → ℕ) → ℕ
  | prim p, ℓ => 2 * (supB ℓ + p.pad) + 3
  | coin _, ℓ => 2 * supB ℓ + 4
  | seq p q, ℓ => timeBoundT p ℓ + timeBoundT q (lenBoundT p ℓ)
  | ifBlank _ p q, ℓ => max (timeBoundT p ℓ) (timeBoundT q ℓ) + 1
  | ifBit _ p q, ℓ => max (timeBoundT p ℓ) (timeBoundT q ℓ) + 1
  | loop i body, ℓ =>
    ℓ i * ((Finset.range (ℓ i)).sup
      (fun j => roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ)) + 1) + 2

/-! ### Soundness of the length bound -/

/-- **Per-tape length bound**: after `p`, every tape `t` holds at most `lenBoundT p ℓ t` bits. -/
theorem lenBoundT_spec (p : Prog k) :
    ∀ (ℓ : Fin k → ℕ) (s : Store k), Fits s ℓ → ∀ s' ∈ (p.law s).support,
      Fits s' (lenBoundT p ℓ) := by
  induction p with
  | prim p =>
    intro ℓ s hs s' hs'
    simp only [law, denote, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact p.fits_apply hs
  | coin i =>
    intro ℓ s hs s' hs'
    simp only [law, denote, ProbComp.eval_map, PMF.support_map, Set.mem_image] at hs'
    obtain ⟨b, _, rfl⟩ := hs'
    exact hs.update i (by simp)
  | seq p q ihp ihq =>
    intro ℓ s hs s' hs'
    simp only [law, denote, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨a, ha, hs'⟩ := hs'
    exact ihq _ a (ihp ℓ s hs a ha) s' hs'
  | ifBlank i p q ihp ihq =>
    intro ℓ s hs s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact (ihp ℓ s hs s' hs').mono fun t => le_max_left _ _
    · exact (ihq ℓ s hs s' hs').mono fun t => le_max_right _ _
  | ifBit i p q ihp ihq =>
    intro ℓ s hs s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact (ihp ℓ s hs s' hs').mono fun t => le_max_left _ _
    · exact (ihq ℓ s hs s' hs').mono fun t => le_max_right _ _
  | loop i body ih =>
    intro ℓ s hs s' hs'
    have this := mem_support_iterate (s i).length (fun t => denote body (tailAt i t)) s
      (fun m t => Fits t ((loopStepT i body)^[m] ℓ)) hs
      (fun m t ht t' ht' => by
        rw [Function.iterate_succ_apply']
        exact ih _ _ (fits_tailAt ht i) t' ht') s' hs'
    exact this.mono (le_iterSupT _ (hs i) ℓ)

/-! ### Monotonicity -/

theorem lenBoundT_mono (p : Prog k) : Monotone (lenBoundT p) := by
  induction p with
  | prim p => exact p.lenT_mono
  | coin i => exact fun ℓ ℓ' h => update_le_update h i le_rfl
  | seq p q ihp ihq => exact ihq.comp ihp
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun ℓ ℓ' h t => max_le_max (ihp h t) (ihq h t)
  | loop i body ih =>
    exact fun ℓ ℓ' h => iterSupT_mono (ih.comp (tailB_mono i)) (h i) h

theorem loopStepT_mono (i : Fin k) (body : Prog k) : Monotone (loopStepT i body) :=
  (lenBoundT_mono body).comp (tailB_mono i)

theorem roundTimeT_mono {bodyTime : (Fin k → ℕ) → ℕ} (hb : Monotone bodyTime) (i : Fin k) :
    Monotone (roundTimeT bodyTime i) :=
  fun _ _ h => Nat.add_le_add (by have := supB_mono h; omega) (hb (tailB_mono i h))

theorem timeBoundT_mono (p : Prog k) : Monotone (timeBoundT p) := by
  induction p with
  | prim p => exact fun ℓ ℓ' h => by have := supB_mono h; simp only [timeBoundT]; omega
  | coin i => exact fun ℓ ℓ' h => by have := supB_mono h; simp only [timeBoundT]; omega
  | seq p q ihp ihq => exact fun ℓ ℓ' h => Nat.add_le_add (ihp h) (ihq (lenBoundT_mono p h))
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun ℓ ℓ' h => Nat.add_le_add_right (max_le_max (ihp h) (ihq h)) 1
  | loop i body ih =>
    intro ℓ ℓ' h
    simp only [timeBoundT]
    refine Nat.add_le_add_right (Nat.mul_le_mul (h i) (Nat.add_le_add_right ?_ 1)) 2
    exact (Finset.sup_mono (Finset.range_mono (h i))).trans' (Finset.sup_mono_fun fun j _ =>
      roundTimeT_mono ih i (((loopStepT_mono i body).iterate j) h))

/-! ### Preserved tapes keep their bound -/

/-- A program that never writes tape `t` leaves its bound alone. -/
theorem lenBoundT_of_preserves (t : Fin k) (p : Prog k) (hp : p.Preserves t) (ℓ : Fin k → ℕ) :
    lenBoundT p ℓ t = ℓ t := by
  induction p generalizing ℓ with
  | prim p => exact p.lenT_of_not_mem ℓ hp
  | coin j => simp [lenBoundT, Function.update, show t ≠ j from fun h => hp h.symm]
  | seq p q ihp ihq => simp only [lenBoundT]; rw [ihq hp.2, ihp hp.1]
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    simp only [lenBoundT]; rw [ihp hp.1, ihq hp.2, max_self]
  | loop j body ih =>
    have hit : ∀ m, ((loopStepT j body)^[m] ℓ) t = ℓ t := by
      intro m
      induction m with
      | zero => rfl
      | succ m ihm =>
        rw [Function.iterate_succ_apply', loopStepT, ih hp.2, tailB,
          Function.update_of_ne (Ne.symm hp.1), ihm]
    show (Finset.range (ℓ j + 1)).sup (fun m => ((loopStepT j body)^[m] ℓ) t) = ℓ t
    simp only [hit]
    exact Finset.sup_const ⟨0, by simp⟩ _

/-! ### Typical shapes -/

theorem timeBoundT_seq (p q : Prog k) (ℓ : Fin k → ℕ) :
    timeBoundT (seq p q) ℓ = timeBoundT p ℓ + timeBoundT q (lenBoundT p ℓ) := rfl

/-- **A loop with a uniform round bound** `R` costs at most `ℓ i · (R + 1) + 2`. -/
theorem timeBoundT_loop_le (i : Fin k) (body : Prog k) (ℓ : Fin k → ℕ) {R : ℕ}
    (hR : ∀ j < ℓ i, roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ) ≤ R) :
    timeBoundT (loop i body) ℓ ≤ ℓ i * (R + 1) + 2 := by
  simp only [timeBoundT]
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ 1)) 2
  exact Finset.sup_le fun j hj => hR j (Finset.mem_range.mp hj)

/-- The iterated bounds of a loop stay below an invariant bound `ℓ'` (`ℓ ≤ ℓ'` and one round
from `ℓ'` stays below `ℓ'`). -/
theorem iterate_loopStepT_le_of_inv (i : Fin k) (body : Prog k) {ℓ ℓ' : Fin k → ℕ} (h0 : ℓ ≤ ℓ')
    (hinv : loopStepT i body ℓ' ≤ ℓ') (j : ℕ) : (loopStepT i body)^[j] ℓ ≤ ℓ' := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (loopStepT_mono i body ih).trans hinv

/-- **A loop under an invariant bound** `ℓ'`: at most `ℓ i` rounds, each at most
`roundTimeT … ℓ'`. -/
theorem timeBoundT_loop_le_of_inv (i : Fin k) (body : Prog k) {ℓ ℓ' : Fin k → ℕ} (h0 : ℓ ≤ ℓ')
    (hinv : loopStepT i body ℓ' ≤ ℓ') :
    timeBoundT (loop i body) ℓ ≤ ℓ i * (roundTimeT (timeBoundT body) i ℓ' + 1) + 2 :=
  timeBoundT_loop_le i body ℓ fun j _ =>
    roundTimeT_mono (timeBoundT_mono body) i (iterate_loopStepT_le_of_inv i body h0 hinv j)

theorem lenBoundT_loop_le_of_inv (i : Fin k) (body : Prog k) {ℓ ℓ' : Fin k → ℕ} (h0 : ℓ ≤ ℓ')
    (hinv : loopStepT i body ℓ' ≤ ℓ') : lenBoundT (loop i body) ℓ ≤ ℓ' :=
  iterSupT_le fun j _ => iterate_loopStepT_le_of_inv i body h0 hinv j

theorem roundTimeT_le (body : Prog k) (i : Fin k) (ℓ : Fin k → ℕ) :
    roundTimeT (timeBoundT body) i ℓ ≤ 2 * supB ℓ + 3 + timeBoundT body ℓ :=
  Nat.add_le_add_left (timeBoundT_mono body (tailB_le i ℓ)) _

/-- **A loop whose body never touches its counter, under an invariant bound** `ℓ'` on the other
tapes: the counter's entry may stay at `ℓ' i`, since one round only lowers it. -/
theorem loopStepT_le_of_preserves (i : Fin k) (body : Prog k) (hb : body.Preserves i)
    {ℓ' : Fin k → ℕ} (hinv : ∀ t, t ≠ i → loopStepT i body ℓ' t ≤ ℓ' t) :
    loopStepT i body ℓ' ≤ ℓ' := by
  intro t
  by_cases ht : t = i
  · subst ht
    rw [loopStepT, lenBoundT_of_preserves t body hb, tailB, Function.update_self]
    exact Nat.sub_le _ _
  · exact hinv t ht

/-! ### Comparison with the global bounds -/

theorem _root_.SigabaNeo.Tape.Prim.lenT_const_le (p : Prim k) (L : ℕ) :
    p.lenT (fun _ => L) ≤ fun _ => L + p.grow := by
  intro t
  cases p <;> simp only [Prim.lenT, Prim.grow, Function.update_apply] <;> (try split_ifs) <;> omega

/-- From the constant bound `L`, the per-tape bound is at most the global one. -/
theorem lenBoundT_const_le (p : Prog k) :
    ∀ L : ℕ, lenBoundT p (fun _ => L) ≤ fun _ => lenBound p L := by
  induction p with
  | prim p => exact p.lenT_const_le
  | coin i =>
    intro L t
    simp only [lenBoundT, lenBound, Function.update_apply]
    split_ifs <;> omega
  | seq p q ihp ihq =>
    exact fun L => ((lenBoundT_mono q) (ihp L)).trans (ihq _)
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun L t => max_le_max (ihp L t) (ihq L t)
  | loop i body ih =>
    intro L
    have hj : ∀ j, (loopStepT i body)^[j] (fun _ => L) ≤ fun _ => (lenBound body)^[j] L := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ihj =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (loopStepT_mono i body ihj).trans
          (((lenBoundT_mono body) (tailB_le i _)).trans (ih _))
    exact iterSupT_le fun j hjL t => (hj j t).trans (le_iterMax _ hjL)

/-- **The per-tape time bound refines the global one**: from the constant bound `L` it is at most
`timeBound p L`. -/
theorem timeBoundT_const_le (p : Prog k) :
    ∀ L : ℕ, timeBoundT p (fun _ => L) ≤ timeBound p L := by
  induction p with
  | prim p => intro L; have := supB_const_le (k := k) L; simp only [timeBoundT, timeBound]; omega
  | coin i => intro L; have := supB_const_le (k := k) L; simp only [timeBoundT, timeBound]; omega
  | seq p q ihp ihq =>
    intro L
    exact Nat.add_le_add (ihp L) (((timeBoundT_mono q) (lenBoundT_const_le p L)).trans (ihq _))
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun L => Nat.add_le_add_right (max_le_max (ihp L) (ihq L)) 1
  | loop i body ih =>
    intro L
    have hj : ∀ j, (loopStepT i body)^[j] (fun _ => L) ≤ fun _ => (lenBound body)^[j] L := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ihj =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (loopStepT_mono i body ihj).trans
          (((lenBoundT_mono body) (tailB_le i _)).trans (lenBoundT_const_le body _))
    simp only [timeBoundT, timeBound]
    refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ 1)) 2
    refine Finset.sup_mono_fun fun j _ => ?_
    have h1 := roundTimeT_le body i ((loopStepT i body)^[j] fun _ => L)
    have h2 := supB_mono (hj j)
    have h3 := supB_const_le (k := k) ((lenBound body)^[j] L)
    have h4 := (timeBoundT_mono body (hj j)).trans (ih ((lenBound body)^[j] L))
    simp only [roundTime]
    omega

end Prog

end SigabaNeo.Tape
