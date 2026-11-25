import SigabaNeoStd.Machines.Prog.CompileT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy.Redirect

/-!
# Framed tape programs

Every primitive of `Prog k` is a column machine sweeping *all* `k` tapes, so even with per-tape
bounds (`timeBoundT`) a primitive costs twice the longest word of the whole store. `XProg k`
extends `Prog` with a combinator

  `frame e p` for `e : Fin m ↪ Fin k` and `p : XProg m`,

which runs `p` on the tapes `e 0, …, e (m-1)` only (cslib-frontier's `extendTapes`): the other
tapes are neither read nor written, and the compiled machine is the machine of `p` with its work
tapes renamed. So `timeBoundT (frame e p) ℓ = timeBoundT p (ℓ ∘ e)`: the cost depends only on the
framed tapes' bounds (no overhead at all).

`XProg k` has the leaves `prog p` (a `Prog k`), the frame, and the control constructs of `Prog`
(`seq`, `ifBlank`, `ifBit`, `loop`), so frames can sit inside loops and loops inside frames.
`Prog` itself is unchanged; its compiler, laws and bounds are reused for the leaves.

## Main results

* `XProg.lenBoundT_spec`, `XProg.preserves_spec`: per-tape length bounds and preserved tapes.
* `XProg.compile_runsWordsT`: the compiled machine realizes `denote p s` within `timeBoundT p ℓ`.
* `XProg.toMachineT`, `XProg.run_toMachineT`, `XProg.cost_toMachineT`: the explicit machine.
* `XProg.timeBoundT_frame`: a frame costs what its body costs from the framed bounds.
-/

namespace SigabaNeo.Tape

open Cslib Turing MultiTapeMachine MultiTapePTM

/-! ### Embedding a sub-store -/

section Embed

variable {k m : ℕ} {α : Type}

/-- Overwrite the tapes `e j` of `f` by `g j`. -/
def embedF (e : Fin m ↪ Fin k) (f : Fin k → α) (g : Fin m → α) : Fin k → α :=
  fun l => (MultiTapeTM.partialInv e l).elim (f l) g

theorem partialInv_self (e : Fin m ↪ Fin k) (j : Fin m) :
    MultiTapeTM.partialInv e (e j) = some j :=
  (MultiTapeTM.partialInv_isPartialInv e j (e j)).mpr rfl

theorem eq_of_partialInv {e : Fin m ↪ Fin k} {l : Fin k} {j : Fin m}
    (h : MultiTapeTM.partialInv e l = some j) : e j = l :=
  (MultiTapeTM.partialInv_isPartialInv e j l).mp h

@[simp] theorem embedF_apply_self (e : Fin m ↪ Fin k) (f : Fin k → α) (g : Fin m → α)
    (j : Fin m) : embedF e f g (e j) = g j := by
  simp [embedF]

/-- Pointwise, an embedded value is the outer one or one of the inner ones. -/
theorem embedF_cases (e : Fin m ↪ Fin k) (f : Fin k → α) (g : Fin m → α) (l : Fin k) :
    (MultiTapeTM.partialInv e l = none ∧ embedF e f g l = f l) ∨
      ∃ j, e j = l ∧ embedF e f g l = g j := by
  unfold embedF
  rcases h : MultiTapeTM.partialInv e l with _ | j
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨j, eq_of_partialInv h, rfl⟩

theorem Fits.embedF {e : Fin m ↪ Fin k} {s : Store k} {ℓ : Fin k → ℕ} {a : Store m}
    {ℓ' : Fin m → ℕ} (hs : Fits s ℓ) (ha : Fits a ℓ') :
    Fits (SigabaNeo.Tape.embedF e s a) (SigabaNeo.Tape.embedF e ℓ ℓ') := by
  intro l
  simp only [SigabaNeo.Tape.embedF]
  rcases MultiTapeTM.partialInv e l with _ | j
  · exact hs l
  · exact ha j

theorem embedF_mono (e : Fin m ↪ Fin k) {f f' : Fin k → ℕ} {g g' : Fin m → ℕ} (hf : f ≤ f')
    (hg : g ≤ g') : embedF e f g ≤ embedF e f' g' := by
  intro l
  simp only [embedF]
  rcases MultiTapeTM.partialInv e l with _ | j
  · exact hf l
  · exact hg j

end Embed

/-! ### Framed programs -/

/-- Tape programs with frames: `Prog` leaves, frames running a program on some of the tapes, and
the control constructs of `Prog`. -/
inductive XProg : ℕ → Type
  /-- A plain program over all the tapes. -/
  | prog {k : ℕ} (p : Prog k) : XProg k
  /-- Run `p` on the tapes `e 0, …, e (m-1)`, leaving the others alone. -/
  | frame {k m : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) : XProg k
  /-- `p`, then `q`. -/
  | seq {k : ℕ} (p q : XProg k) : XProg k
  /-- `p` if tape `i` is blank, otherwise `q`. -/
  | ifBlank {k : ℕ} (i : Fin k) (p q : XProg k) : XProg k
  /-- `p` if the first bit of tape `i` is `true`, otherwise `q`. -/
  | ifBit {k : ℕ} (i : Fin k) (p q : XProg k) : XProg k
  /-- Repeat `|s i|` times: drop the first bit of tape `i`, then run `body`. -/
  | loop {k : ℕ} (i : Fin k) (body : XProg k) : XProg k

namespace XProg

variable {k : ℕ}

/-- The denotation: a randomized store transformation. -/
noncomputable def denote : {k : ℕ} → XProg k → Store k → ProbComp (Store k)
  | _, prog p, s => p.denote s
  | _, frame e p, s => embedF e s <$> denote p (fun j => s (e j))
  | _, seq p q, s => denote p s >>= denote q
  | _, ifBlank i p q, s => if s i = [] then denote p s else denote q s
  | _, ifBit i p q, s => if (s i).head? = some true then denote p s else denote q s
  | _, loop i body, s => OracleComp.iterate (s i).length (fun t => denote body (tailAt i t)) s

/-- The output law of a program on a store. -/
noncomputable def law (p : XProg k) (s : Store k) : PMF (Store k) := ProbComp.eval (p.denote s)

/-- `p` never writes tape `i`. -/
def Preserves : {k : ℕ} → Fin k → XProg k → Prop
  | _, i, prog p => p.Preserves i
  | _, i, frame e p => ∀ j, e j = i → p.Preserves j
  | _, i, seq p q => p.Preserves i ∧ q.Preserves i
  | _, i, ifBlank _ p q => p.Preserves i ∧ q.Preserves i
  | _, i, ifBit _ p q => p.Preserves i ∧ q.Preserves i
  | _, i, loop j body => j ≠ i ∧ body.Preserves i

/-- Every loop body leaves its counter tape alone. -/
def WF : {k : ℕ} → XProg k → Prop
  | _, prog p => p.WF
  | _, frame _ p => p.WF
  | _, seq p q => p.WF ∧ q.WF
  | _, ifBlank _ p q => p.WF ∧ q.WF
  | _, ifBit _ p q => p.WF ∧ q.WF
  | _, loop i body => body.WF ∧ body.Preserves i

/-! ### Bounds -/

/-- The per-tape length bound after a program. -/
def lenBoundT : {k : ℕ} → XProg k → (Fin k → ℕ) → (Fin k → ℕ)
  | _, prog p, ℓ => p.lenBoundT ℓ
  | _, frame e p, ℓ => embedF e ℓ (lenBoundT p (fun j => ℓ (e j)))
  | _, seq p q, ℓ => lenBoundT q (lenBoundT p ℓ)
  | _, ifBlank _ p q, ℓ => fun t => max (lenBoundT p ℓ t) (lenBoundT q ℓ t)
  | _, ifBit _ p q, ℓ => fun t => max (lenBoundT p ℓ t) (lenBoundT q ℓ t)
  | _, loop i body, ℓ => iterSupT (fun ℓ' => lenBoundT body (tailB i ℓ')) (ℓ i) ℓ

/-- The bound after one round of `loop i body`. -/
def loopStepT (i : Fin k) (body : XProg k) (ℓ : Fin k → ℕ) : Fin k → ℕ :=
  lenBoundT body (tailB i ℓ)

/-- The per-tape time bound of the compiled machine. -/
def timeBoundT : {k : ℕ} → XProg k → (Fin k → ℕ) → ℕ
  | _, prog p, ℓ => p.timeBoundT ℓ
  | _, frame e p, ℓ => timeBoundT p (fun j => ℓ (e j))
  | _, seq p q, ℓ => timeBoundT p ℓ + timeBoundT q (lenBoundT p ℓ)
  | _, ifBlank _ p q, ℓ => max (timeBoundT p ℓ) (timeBoundT q ℓ) + 1
  | _, ifBit _ p q, ℓ => max (timeBoundT p ℓ) (timeBoundT q ℓ) + 1
  | _, loop i body, ℓ =>
    ℓ i * ((Finset.range (ℓ i)).sup
      (fun j => Prog.roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ)) + 1) + 2

theorem timeBoundT_frame {m : ℕ} (e : Fin m ↪ Fin k) (p : XProg m) (ℓ : Fin k → ℕ) :
    timeBoundT (frame e p) ℓ = timeBoundT p (fun j => ℓ (e j)) := rfl

theorem timeBoundT_seq (p q : XProg k) (ℓ : Fin k → ℕ) :
    timeBoundT (seq p q) ℓ = timeBoundT p ℓ + timeBoundT q (lenBoundT p ℓ) := rfl

theorem timeBoundT_prog (p : Prog k) (ℓ : Fin k → ℕ) :
    timeBoundT (prog p) ℓ = p.timeBoundT ℓ := rfl

/-! ### Supports -/

theorem mem_support_frame {m : ℕ} {e : Fin m ↪ Fin k} {p : XProg m} {s s' : Store k}
    (h : s' ∈ ((frame e p).law s).support) :
    ∃ a ∈ (p.law (fun j => s (e j))).support, s' = embedF e s a := by
  simp only [law, denote, ProbComp.eval_map, PMF.support_map, Set.mem_image] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, rfl⟩

/-- **Per-tape length bound.** -/
theorem lenBoundT_spec (p : XProg k) :
    ∀ (ℓ : Fin k → ℕ) (s : Store k), Fits s ℓ → ∀ s' ∈ (p.law s).support,
      Fits s' (lenBoundT p ℓ) := by
  induction p with
  | prog p => exact fun ℓ s hs s' hs' => Prog.lenBoundT_spec p ℓ s hs s' hs'
  | frame e p ih =>
    intro ℓ s hs s' hs'
    obtain ⟨a, ha, rfl⟩ := mem_support_frame hs'
    exact hs.embedF (ih _ _ (fun j => hs (e j)) a ha)
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
    have this := Prog.mem_support_iterate (s i).length (fun t => denote body (tailAt i t)) s
      (fun m t => Fits t ((loopStepT i body)^[m] ℓ)) hs
      (fun m t ht t' ht' => by
        rw [Function.iterate_succ_apply']
        exact ih _ _ (fits_tailAt ht i) t' ht') s' hs'
    exact this.mono (le_iterSupT _ (hs i) ℓ)

/-- **Preserved tapes.** -/
theorem preserves_spec (p : XProg k) :
    ∀ (i : Fin k), p.Preserves i → ∀ (s : Store k), ∀ s' ∈ (p.law s).support, s' i = s i := by
  induction p with
  | prog p => exact fun i hp s s' hs' => Prog.preserves_spec i p hp s s' hs'
  | frame e p ih =>
    intro i hp s s' hs'
    obtain ⟨a, ha, rfl⟩ := mem_support_frame hs'
    rcases embedF_cases e s a i with ⟨_, h⟩ | ⟨j, hj, h⟩
    · exact h
    · rw [h, ih j (hp j hj) _ a ha, hj]
  | seq p q ihp ihq =>
    intro i hp s s' hs'
    simp only [law, denote, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨a, ha, hs'⟩ := hs'
    exact (ihq i hp.2 a s' hs').trans (ihp i hp.1 s a ha)
  | ifBlank j p q ihp ihq =>
    intro i hp s s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact ihp i hp.1 s s' hs'
    · exact ihq i hp.2 s s' hs'
  | ifBit j p q ihp ihq =>
    intro i hp s s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact ihp i hp.1 s s' hs'
    · exact ihq i hp.2 s s' hs'
  | loop j body ih =>
    intro i hp s s' hs'
    exact Prog.mem_support_iterate (s j).length (fun t => denote body (tailAt j t)) s
      (fun _ t => t i = s i) rfl
      (fun m t ht t' ht' => by
        rw [ih i hp.2 _ t' ht']
        simp [tailAt, Function.update, Ne.symm hp.1, ht]) s' hs'

/-! ### Monotonicity and loop shapes -/

theorem lenBoundT_mono (p : XProg k) : Monotone (lenBoundT p) := by
  induction p with
  | prog p => exact Prog.lenBoundT_mono p
  | frame e p ih => exact fun ℓ ℓ' h => embedF_mono e h (ih fun j => h (e j))
  | seq p q ihp ihq => exact ihq.comp ihp
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun ℓ ℓ' h t => max_le_max (ihp h t) (ihq h t)
  | loop i body ih =>
    exact fun ℓ ℓ' h => iterSupT_mono (ih.comp (tailB_mono i)) (h i) h

theorem loopStepT_mono (i : Fin k) (body : XProg k) : Monotone (loopStepT i body) :=
  (lenBoundT_mono body).comp (tailB_mono i)

theorem timeBoundT_mono (p : XProg k) : Monotone (timeBoundT p) := by
  induction p with
  | prog p => exact Prog.timeBoundT_mono p
  | frame e p ih => exact fun ℓ ℓ' h => ih fun j => h (e j)
  | seq p q ihp ihq => exact fun ℓ ℓ' h => Nat.add_le_add (ihp h) (ihq (lenBoundT_mono p h))
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    exact fun ℓ ℓ' h => Nat.add_le_add_right (max_le_max (ihp h) (ihq h)) 1
  | loop i body ih =>
    intro ℓ ℓ' h
    simp only [timeBoundT]
    refine Nat.add_le_add_right (Nat.mul_le_mul (h i) (Nat.add_le_add_right ?_ 1)) 2
    exact (Finset.sup_mono (Finset.range_mono (h i))).trans' (Finset.sup_mono_fun fun j _ =>
      Prog.roundTimeT_mono ih i (((loopStepT_mono i body).iterate j) h))

/-- A program that never writes tape `t` leaves its bound alone. -/
theorem lenBoundT_of_preserves (p : XProg k) :
    ∀ (t : Fin k), p.Preserves t → ∀ ℓ : Fin k → ℕ, lenBoundT p ℓ t = ℓ t := by
  induction p with
  | prog p => exact fun t hp ℓ => Prog.lenBoundT_of_preserves t p hp ℓ
  | frame e p ih =>
    intro t hp ℓ
    show embedF e ℓ _ t = ℓ t
    rcases embedF_cases e ℓ (lenBoundT p (fun j => ℓ (e j))) t with ⟨_, h⟩ | ⟨j, hj, h⟩
    · exact h
    · rw [h, ih j (hp j hj), hj]
  | seq p q ihp ihq => intro t hp ℓ; simp only [lenBoundT]; rw [ihq t hp.2, ihp t hp.1]
  | ifBlank _ p q ihp ihq | ifBit _ p q ihp ihq =>
    intro t hp ℓ; simp only [lenBoundT]; rw [ihp t hp.1, ihq t hp.2, max_self]
  | loop j body ih =>
    intro t hp ℓ
    have hit : ∀ m, ((loopStepT j body)^[m] ℓ) t = ℓ t := by
      intro m
      induction m with
      | zero => rfl
      | succ m ihm =>
        rw [Function.iterate_succ_apply', loopStepT, ih t hp.2, tailB,
          Function.update_of_ne (Ne.symm hp.1), ihm]
    show (Finset.range (ℓ j + 1)).sup (fun m => ((loopStepT j body)^[m] ℓ) t) = ℓ t
    simp only [hit]
    exact Finset.sup_const ⟨0, by simp⟩ _

/-- **A loop with a uniform round bound** `R` costs at most `ℓ i · (R + 1) + 2`. -/
theorem timeBoundT_loop_le (i : Fin k) (body : XProg k) (ℓ : Fin k → ℕ) {R : ℕ}
    (hR : ∀ j < ℓ i, Prog.roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ) ≤ R) :
    timeBoundT (loop i body) ℓ ≤ ℓ i * (R + 1) + 2 := by
  simp only [timeBoundT]
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ 1)) 2
  exact Finset.sup_le fun j hj => hR j (Finset.mem_range.mp hj)

theorem iterate_loopStepT_le_of_inv (i : Fin k) (body : XProg k) {ℓ ℓ' : Fin k → ℕ}
    (h0 : ℓ ≤ ℓ') (hinv : loopStepT i body ℓ' ≤ ℓ') (j : ℕ) :
    (loopStepT i body)^[j] ℓ ≤ ℓ' := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (loopStepT_mono i body ih).trans hinv

/-- **A loop under an invariant bound** `ℓ'`. -/
theorem timeBoundT_loop_le_of_inv (i : Fin k) (body : XProg k) {ℓ ℓ' : Fin k → ℕ}
    (h0 : ℓ ≤ ℓ') (hinv : loopStepT i body ℓ' ≤ ℓ') :
    timeBoundT (loop i body) ℓ ≤ ℓ i * (Prog.roundTimeT (timeBoundT body) i ℓ' + 1) + 2 :=
  timeBoundT_loop_le i body ℓ fun j _ =>
    Prog.roundTimeT_mono (timeBoundT_mono body) i (iterate_loopStepT_le_of_inv i body h0 hinv j)

theorem lenBoundT_loop_le_of_inv (i : Fin k) (body : XProg k) {ℓ ℓ' : Fin k → ℕ}
    (h0 : ℓ ≤ ℓ') (hinv : loopStepT i body ℓ' ≤ ℓ') : lenBoundT (loop i body) ℓ ≤ ℓ' :=
  iterSupT_le fun j _ => iterate_loopStepT_le_of_inv i body h0 hinv j

theorem loopStepT_le_of_preserves (i : Fin k) (body : XProg k) (hb : body.Preserves i)
    {ℓ' : Fin k → ℕ} (hinv : ∀ t, t ≠ i → loopStepT i body ℓ' t ≤ ℓ' t) :
    loopStepT i body ℓ' ≤ ℓ' := by
  intro t
  by_cases ht : t = i
  · subst ht
    rw [loopStepT, lenBoundT_of_preserves body t hb, tailB, Function.update_self]
    exact Nat.sub_le _ _
  · exact hinv t ht

theorem roundTimeT_le (body : XProg k) (i : Fin k) (ℓ : Fin k → ℕ) :
    Prog.roundTimeT (timeBoundT body) i ℓ ≤ 2 * supB ℓ + 3 + timeBoundT body ℓ :=
  Nat.add_le_add_left (timeBoundT_mono body (tailB_le i ℓ)) _

/-! ### The compiler -/

/-- The control states of the compiled machine. -/
def State : {k : ℕ} → XProg k → Type
  | _, prog p => p.State
  | _, frame _ p => State p
  | _, seq p q => State p ⊕ State q
  | _, ifBlank _ p q => Option (State q ⊕ State p)
  | _, ifBit _ p q => Option (State p ⊕ State q)
  | _, loop i body => Option (((CQ (tailSpec i).e ⊕ State body) ⊕ Unit) ⊕ Unit)

/-- The states are finite. -/
@[instance_reducible] def instFintypeState : {k : ℕ} → (p : XProg k) → Fintype p.State
  | _, prog p => inferInstanceAs (Fintype p.State)
  | _, frame _ p => instFintypeState p
  | _, seq p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (State p ⊕ State q))
  | _, ifBlank _ p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (Option (State q ⊕ State p)))
  | _, ifBit _ p q =>
    letI := instFintypeState p; letI := instFintypeState q
    inferInstanceAs (Fintype (Option (State p ⊕ State q)))
  | _, loop i body =>
    letI := instFintypeState body
    inferInstanceAs (Fintype (Option (((CQ (tailSpec i).e ⊕ State body) ⊕ Unit) ⊕ Unit)))

instance (p : XProg k) : Fintype p.State := instFintypeState p

/-- **The compiler**: a frame is the machine of its body with renamed work tapes. -/
noncomputable def compile : {k : ℕ} → (p : XProg k) → MultiTapePTM k Bool p.State Empty
  | _, prog p => p.compile
  | _, frame e p => (compile p).extendTapes e
  | _, seq p q => (compile p).seq (compile q)
  | _, ifBlank i p q => branch i (compile q) (compile p)
  | _, ifBit i p q => branchBit i (compile p) (compile q)
  | _, loop i body =>
    branch i (repeatUntilBlank i (Prog.loopRound i (compile body)))
      (ofDeterministic (haltTM _))

theorem roundTimeT_le_sup (body : XProg k) (i : Fin k) (ℓ : Fin k → ℕ) {j : ℕ} (hj : j < ℓ i) :
    Prog.roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ) ≤
      (Finset.range (ℓ i)).sup
        (fun j => Prog.roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ)) :=
  Finset.le_sup (f := fun j => Prog.roundTimeT (timeBoundT body) i ((loopStepT i body)^[j] ℓ))
    (Finset.mem_range.mpr hj)

/-- **Correctness and time of the compiled machine of a framed program.** -/
theorem compile_runsWordsT (p : XProg k) (hp : p.WF) (x : List Bool) :
    ∀ (ℓ : Fin k → ℕ) (s : Store k) (out₀ : List Bool), Fits s ℓ →
      (compile p).RunsWords x s out₀ (timeBoundT p ℓ) (ProbOracleComp.sample (denote p s)) id
        (fun _ => []) := by
  induction p with
  | prog p => exact fun ℓ s out₀ hs => Prog.compile_runsWordsT p hp x ℓ s out₀ hs
  | frame e p ih =>
    intro ℓ s out₀ hs
    have h := RunsWords.extendTapes (ws₀ := s) e
      (ih hp (fun j => ℓ (e j)) (fun j => s (e j)) out₀ (fun j => hs (e j)))
    show (compile p).extendTapes e |>.RunsWords x s out₀ _
      (ProbOracleComp.sample (embedF e s <$> denote p (fun j => s (e j)))) id (fun _ => [])
    rw [ProbOracleComp.sample_map]
    exact RunsWords.of_map _ _ _ h
  | seq p q ihp ihq =>
    intro ℓ s out₀ hs
    exact RunsWords.seqStore (ihp hp.1 ℓ s out₀ hs)
      (fun a ha => ihq hp.2 _ a out₀ (lenBoundT_spec p ℓ s hs a ha))
  | ifBlank i p q ihp ihq =>
    intro ℓ s out₀ hs
    by_cases hi : s i = []
    · have h := RunsWords.branch_nil i (compile q) hi (ihp hp.1 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
    · have h := RunsWords.branch_ne_nil i (compile p) hi (ihq hp.2 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
  | ifBit i p q ihp ihq =>
    intro ℓ s out₀ hs
    by_cases hi : (s i).head? = some true
    · have h := RunsWords.branchBit_true i (compile q) hi (ihp hp.1 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
    · have h := RunsWords.branchBit_false i (compile p) hi (ihq hp.2 ℓ s out₀ hs)
      simp only [denote, hi, ↓reduceIte]
      exact h.mono (by simp only [timeBoundT]; omega)
  | loop i body ih =>
    intro ℓ s out₀ hs
    set g := loopStepT i body with hg
    set T := (Finset.range (ℓ i)).sup
      (fun j => Prog.roundTimeT (timeBoundT body) i (g^[j] ℓ)) with hT
    have hround : ∀ (ℓ' : Fin _ → ℕ) (t : Store _), Fits t ℓ' →
        (Prog.loopRound i (compile body)).RunsWords x t out₀
          (Prog.roundTimeT (timeBoundT body) i ℓ')
          (ProbOracleComp.sample (denote body (tailAt i t))) id (fun _ => []) := by
      intro ℓ' t ht
      have hL := ht.maxLen_le
      have h := RunsWords.seqStore (A := pure (tailAt i t)) (B := denote body)
        (colTM_runsWords (tailSpec i) x t (tailAt i t) out₀ (t := 2 * supB ℓ' + 3)
          (by simp only [tailSpec, bwdSpec]; omega) (tail_result i t))
        (fun a ha => by
          simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih hp.1 _ _ out₀ (fits_tailAt ht i))
      rw [pure_bind] at h
      exact h
    have hn : (s i).length ≤ ℓ i := hs i
    by_cases h0 : s i = []
    · have hhalt : (ofDeterministic (haltTM _) : MultiTapePTM _ Bool Unit Empty).RunsWords x s out₀
          1 (pure s) id (fun _ => []) := runsWords_of_runFrom (haltTM_runFrom x s out₀)
      have h := RunsWords.branch_nil i (repeatUntilBlank i (Prog.loopRound i (compile body))) h0
        hhalt
      simp only [denote, h0, List.length_nil, OracleComp.iterate_zero]
      exact h.mono (by simp only [timeBoundT]; omega)
    · set n := (s i).length with hn'
      have hpos : 0 < n := List.length_pos_iff.mpr h0
      have hloop := RunsWords.repeatUntilBlank i (body := Prog.loopRound i (compile body))
        (x := x) (out₀ := out₀) (t := T) (rounds := n - 1) (s₀ := s) (ws := id) Function.injective_id
        (step := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (last := fun t => ProbOracleComp.sample (denote body (tailAt i t)))
        (fun m t => (t i).length = n - m ∧ Fits t (g^[m] ℓ)) ⟨by simp [hn'], hs⟩
        (fun m hm t ht => (hround _ t ht.2).mono (roundTimeT_le_sup body i ℓ (by omega)))
        (fun t ht => (hround _ t ht.2).mono (roundTimeT_le_sup body i ℓ (by omega)))
        (fun m hm t ht OS oracle st st' t' ht' => by
          have ht'' := mem_support_of_runWith_sample ht'
          have hi := preserves_spec body i hp.2 _ t' ht''
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [hi]; simp [tailAt, ht.1]; omega
          · rw [Function.iterate_succ_apply']
            exact lenBoundT_spec body _ _ (fits_tailAt ht.2 i) t' ht''
          · show t' i ≠ []
            rw [hi]
            simp only [tailAt, Function.update_self, ne_eq]
            rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
            omega)
        (fun t ht OS oracle st st' t' ht' => by
          have hi := preserves_spec body i hp.2 _ t' (mem_support_of_runWith_sample ht')
          show t' i = []
          rw [hi]
          simp only [tailAt, Function.update_self]
          rw [← List.length_eq_zero_iff, List.length_tail, ht.1]
          omega)
      have h := RunsWords.branch_ne_nil i (ofDeterministic (haltTM _)) h0 hloop
      have hprog : (OracleComp.iterate (n - 1)
          (fun t => ProbOracleComp.sample (denote body (tailAt i t))) s >>=
            fun t => ProbOracleComp.sample (denote body (tailAt i t)) :
            ProbOracleComp (fun _ : Empty × List Bool => List Bool) (Store _)) =
          ProbOracleComp.sample (denote (loop i body) s) := by
        rw [← OracleComp.iterate_succ, Nat.sub_add_cancel hpos, denote, sample_iterate]
      rw [hprog] at h
      refine h.mono ?_
      show (n - 1 + 1) * (T + 1) + 1 ≤ ℓ i * (T + 1) + 2
      have : (n - 1 + 1) * (T + 1) ≤ ℓ i * (T + 1) := Nat.mul_le_mul_right _ (by omega)
      omega

/-! ### The explicit machine -/

/-- The machine of a framed program: load the input onto tape `i₀`, run, emit tape `o`. -/
noncomputable def toPTM (p : XProg k) (i₀ o : Fin k) :
    MultiTapePTM k Bool ((Bool ⊕ p.State) ⊕ Bool) Empty :=
  ((ofDeterministic (loadTM i₀)).seq (compile p)).seq (ofDeterministic (emitTM o))

/-- The clock of the machine of a framed program, for inputs at most `n` long. -/
def totalTimeT (p : XProg k) (i₀ o : Fin k) (n : ℕ) : ℕ :=
  (2 * n + 2) + timeBoundT p (Prog.inputBound i₀ n) + (2 * lenBoundT p (Prog.inputBound i₀ n) o + 2)

theorem toPTM_runsWordsT (p : XProg k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toPTM i₀ o).RunsWords x (fun _ => []) [] (totalTimeT p i₀ o n)
      (ProbOracleComp.sample (denote p (inputStore i₀ x))) id (fun s => s o) := by
  have hload : (ofDeterministic (loadTM i₀) : MultiTapePTM k Bool Bool Empty).RunsWords x
      (fun _ => []) [] (2 * n + 2) (ProbOracleComp.sample (pure (inputStore i₀ x))) id
      (fun _ => []) :=
    (runsWords_of_runFrom (loadTM_runFrom i₀ x _ rfl [])).mono (by omega)
  have h₁ := RunsWords.seqStore hload (fun a ha => by
    simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at ha
    subst ha
    exact compile_runsWordsT p hp x _ _ [] (Prog.fits_inputStore i₀ hx))
  rw [pure_bind] at h₁
  have h₂ := h₁.seq_bind (t₂ := 2 * lenBoundT p (Prog.inputBound i₀ n) o + 2)
    (prog₂ := fun a => pure a) (ws₂ := fun _ => id)
    (emit₂ := fun _ b => b o) (fun a b hab => by simpa using hab)
    (fun a _ _ _ _ ha => by
      have hlen := lenBoundT_spec p _ _ (Prog.fits_inputStore i₀ hx) a
        (mem_support_of_runWith_sample ha) o
      refine (runsWords_of_runFrom_emit (e := fun b => b o)
        (emitTM_runFrom o x a ([] ++ []))).mono ?_
      omega)
  have h₃ := h₂.of_map Prod.snd id (fun s => s o)
  have heq : (Prod.snd <$> (ProbOracleComp.sample (denote p (inputStore i₀ x)) >>= fun a =>
      (fun b => (a, b)) <$> (pure a : ProbOracleComp (fun _ : Empty × List Bool => List Bool) _))) =
      ProbOracleComp.sample (denote p (inputStore i₀ x)) := by
    simp
  rw [heq] at h₃
  exact h₃

/-- The explicit machine (no oracles) of a framed program. -/
noncomputable def toMachineT (p : XProg k) (i₀ o : Fin k) (n : ℕ) : Machine :=
  Machine.ofPTM (p.toPTM i₀ o) (totalTimeT p i₀ o n)

/-- **The output law of the machine of a framed program.** -/
theorem run_toMachineT (p : XProg k) (hp : p.WF) (i₀ o : Fin k) (n : ℕ) (x : List Bool)
    (hx : x.length ≤ n) :
    (p.toMachineT i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o) := by
  rw [toMachineT, Machine.run_ofPTM]
  exact Prog.eval_runClosed_of_runsWords (toPTM_runsWordsT p hp i₀ o n x hx)

theorem states_toMachineT (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineT i₀ o n).states = Fintype.card p.State + 4 := by
  show Nat.card ((Bool ⊕ p.State) ⊕ Bool) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_bool]
  ring

/-- **The cost of the machine of a framed program.** -/
theorem cost_toMachineT (p : XProg k) (i₀ o : Fin k) (n : ℕ) :
    (p.toMachineT i₀ o n).cost =
      totalTimeT p i₀ o n + 6 * (Fintype.card p.State + 4) * 3 ^ k * 3 ^ 0 *
        Machine.entryBits k (Fintype.card p.State + 4) 0 := by
  rw [Machine.cost, Machine.descLen, states_toMachineT]
  rfl

end XProg

end SigabaNeo.Tape
