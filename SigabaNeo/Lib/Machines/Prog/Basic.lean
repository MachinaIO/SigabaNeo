import SigabaNeo.Lib.Machines.Prog.Prims
import CslibFrontier.Languages.Probabilistic.Iteration

/-!
# A structured tape language

Programs over `k` word tapes (`Prog k`): primitives (`Prim k`, each a column machine of
`SigabaNeo.Lib.Machines.Prog.Prims`), a fair coin, sequencing, branching on a blank tape or on the
first bit of a tape, and counter-driven loops. A program denotes a randomized store transformation
`denote p : Store k → ProbComp (Store k)`, with law `law p s = ProbComp.eval (denote p s)`.

`loop i b` repeats `|s i|` times: drop the first bit of tape `i`, then run `b`. It is well formed
(`Prog.WF`) when `b` never writes tape `i` (`Prog.Preserves`), so that the machine's loop, which
tests tape `i` for blank, runs exactly `|s i|` rounds.

For a bound `L` on the length of every word of the store, `lenBound p L` bounds the length of every
word afterwards (`lenBound_spec`), and `timeBound p L` bounds the steps of the compiled machine on
every coin sequence (`SigabaNeo.Lib.Machines.Prog.Compile`). Loops multiply: a loop of at most `L`
rounds costs `L` times the cost of its worst round.
-/

namespace SigabaNeo.Tape

open Cslib Turing

variable {k : ℕ}

/-! ### Primitives -/

/-- The primitive operations, each a column machine. -/
inductive Prim (k : ℕ) where
  /-- `i := []`. -/
  | clear (i : Fin k)
  /-- `i := s j`. -/
  | copy (i j : Fin k)
  /-- `i := carryOp f (s i) (s j)`: digitwise with a carry from the last digit (`add`, `sub`). -/
  | carry (f : DigitOp) (i j : Fin k)
  /-- `i := (s i).tail`. -/
  | tail (i : Fin k)
  /-- `i := (s i).tail`, then `j := (s i).take 1`. -/
  | pop (i j : Fin k)
  /-- `f := [decide (s i = s j)]`. -/
  | eq (i j f : Fin k)
  /-- `i := b :: s i`. -/
  | cons (i : Fin k) (b : Bool)
  /-- `i := s i ++ [b]`. -/
  | snoc (i : Fin k) (b : Bool)
  /-- `i := (s j).take 1 ++ s i`. -/
  | consHead (i j : Fin k)
  /-- `i := s i ++ (s j).take 1`. -/
  | snocHead (i j : Fin k)

namespace Prim

/-- The column machine of a primitive. -/
def spec : Prim k → ColSpec k
  | clear i => clearSpec i
  | copy i j => copySpec i j
  | carry f i j => carrySpec f i j
  | tail i => tailSpec i
  | pop i j => popSpec i j
  | eq i j f => eqSpec i j f
  | cons i b => consSpec i b
  | snoc i b => snocSpec i b
  | consHead i j => consHeadSpec i j
  | snocHead i j => snocHeadSpec i j

/-- The store transformation of a primitive. -/
def apply : Prim k → Store k → Store k
  | clear i, s => Function.update s i []
  | copy i j, s => Function.update s i (s j)
  | carry f i j, s => Function.update s i (carryOp f (s i) (s j)).2
  | tail i, s => Function.update s i (s i).tail
  | pop i j, s => Function.update (Function.update s i (s i).tail) j ((s i).take 1)
  | eq i j f, s => Function.update s f [decide (s i = s j)]
  | cons i b, s => Function.update s i (b :: s i)
  | snoc i b, s => Function.update s i (s i ++ [b])
  | consHead i j, s => Function.update s i ((s j).take 1 ++ s i)
  | snocHead i j, s => Function.update s i (s i ++ (s j).take 1)

/-- The tapes a primitive writes. -/
def writes : Prim k → List (Fin k)
  | clear i | copy i _ | carry _ i _ | tail i | cons i _ | snoc i _ | consHead i _
  | snocHead i _ => [i]
  | pop i j => [i, j]
  | eq _ _ f => [f]

/-- The number of padding columns: `1` for the primitives that may lengthen a word. -/
def pad : Prim k → ℕ
  | cons _ _ | snoc _ _ | consHead _ _ | snocHead _ _ => 1
  | _ => 0

/-- How much a primitive may lengthen the longest word. -/
def grow : Prim k → ℕ
  | cons _ _ | snoc _ _ | consHead _ _ | snocHead _ _ | eq _ _ _ => 1
  | _ => 0

theorem spec_e (p : Prim k) : p.spec.e = p.pad := by cases p <;> rfl

/-- **Each primitive's column machine computes its store transformation.** -/
theorem result (p : Prim k) (s : Store k) :
    ∀ t, tapesOf (p.spec.colResult s) t = tapeOfList (p.apply s t) := by
  cases p with
  | clear i => exact clear_result i s
  | copy i j => exact copy_result i j s
  | carry f i j => exact carry_result f i j s
  | tail i => exact tail_result i s
  | pop i j => exact pop_result i j s
  | eq i j f => exact eq_result i j f s
  | cons i b => exact cons_result i b s
  | snoc i b => exact snoc_result i b s
  | consHead i j => exact consHead_result i j s
  | snocHead i j => exact snocHead_result i j s

theorem apply_of_not_mem (p : Prim k) (s : Store k) {t : Fin k} (ht : t ∉ p.writes) :
    p.apply s t = s t := by
  cases p <;> simp_all [writes, apply, Function.update, eq_comm]

theorem maxLen_apply (p : Prim k) (s : Store k) {L : ℕ} (hs : maxLen s ≤ L) :
    maxLen (p.apply s) ≤ L + p.grow := by
  have hl := fun i => (length_le_maxLen s i).trans hs
  have htl := fun i => (length_tail_le_maxLen s i).trans hs
  cases p with
  | clear i => exact maxLen_update_le s i _ (by omega) (by simp)
  | copy i j => exact maxLen_update_le s i _ (by omega) (hl j |>.trans (by omega))
  | carry f i j => exact maxLen_update_le s i _ (by omega) (by simpa using hl i |>.trans (by omega))
  | tail i => exact maxLen_update_le s i _ (by omega) (htl i |>.trans (by omega))
  | pop i j =>
    exact maxLen_update_le _ j _ (maxLen_update_le s i _ (by omega) (htl i |>.trans (by omega)))
      (by have := hl i; simp only [List.length_take, grow, pad]; omega)
  | eq i j f =>
    exact maxLen_update_le s f _ (by simp only [grow]; omega) (by simp [grow])
  | cons i b => exact maxLen_update_le s i _ (by omega) (by simpa [grow, pad] using hl i)
  | snoc i b => exact maxLen_update_le s i _ (by omega) (by simpa [grow, pad] using hl i)
  | consHead i j =>
    exact maxLen_update_le s i _ (by omega)
      (by have := hl i; simp only [List.length_append, List.length_take, grow, pad]; omega)
  | snocHead i j =>
    exact maxLen_update_le s i _ (by omega)
      (by have := hl i; simp only [List.length_append, List.length_take, grow, pad]; omega)

end Prim

/-- Drop the first bit of tape `i`. -/
def tailAt (i : Fin k) (s : Store k) : Store k := Function.update s i (s i).tail

theorem maxLen_tailAt (i : Fin k) (s : Store k) : maxLen (tailAt i s) ≤ maxLen s :=
  maxLen_update_le s i _ le_rfl (length_tail_le_maxLen s i)

/-! ### Programs -/

/-- Programs over `k` word tapes. -/
inductive Prog (k : ℕ) where
  /-- A primitive. -/
  | prim (p : Prim k)
  /-- `i := [b]` for a fair coin `b`. -/
  | coin (i : Fin k)
  /-- `p`, then `q`. -/
  | seq (p q : Prog k)
  /-- `p` if tape `i` is blank, otherwise `q`. -/
  | ifBlank (i : Fin k) (p q : Prog k)
  /-- `p` if the first bit of tape `i` is `true`, otherwise `q`. -/
  | ifBit (i : Fin k) (p q : Prog k)
  /-- Repeat `|s i|` times: drop the first bit of tape `i`, then run `body`. -/
  | loop (i : Fin k) (body : Prog k)

namespace Prog

/-- The denotation: a randomized store transformation. -/
noncomputable def denote : Prog k → Store k → ProbComp (Store k)
  | prim p, s => pure (p.apply s)
  | coin i, s => (fun b => Function.update s i [b]) <$> ProbComp.uniform Bool
  | seq p q, s => denote p s >>= denote q
  | ifBlank i p q, s => if s i = [] then denote p s else denote q s
  | ifBit i p q, s => if (s i).head? = some true then denote p s else denote q s
  | loop i body, s => OracleComp.iterate (s i).length (fun t => denote body (tailAt i t)) s

/-- The output law of a program on a store. -/
noncomputable def law (p : Prog k) (s : Store k) : PMF (Store k) := ProbComp.eval (p.denote s)

/-- `p` never writes tape `i`. -/
def Preserves (i : Fin k) : Prog k → Prop
  | prim p => i ∉ p.writes
  | coin j => j ≠ i
  | seq p q => p.Preserves i ∧ q.Preserves i
  | ifBlank _ p q => p.Preserves i ∧ q.Preserves i
  | ifBit _ p q => p.Preserves i ∧ q.Preserves i
  | loop j body => j ≠ i ∧ body.Preserves i

/-- Every loop body leaves its counter tape alone. -/
def WF : Prog k → Prop
  | prim _ | coin _ => True
  | seq p q => p.WF ∧ q.WF
  | ifBlank _ p q => p.WF ∧ q.WF
  | ifBit _ p q => p.WF ∧ q.WF
  | loop i body => body.WF ∧ body.Preserves i

/-- The largest value of `g^[j] L` over `j ≤ L`. -/
def iterMax (g : ℕ → ℕ) (L : ℕ) : ℕ := (Finset.range (L + 1)).sup fun j => g^[j] L

theorem le_iterMax (g : ℕ → ℕ) {L j : ℕ} (hj : j ≤ L) : g^[j] L ≤ iterMax g L :=
  Finset.le_sup (f := fun j => g^[j] L) (Finset.mem_range.mpr (by omega))

/-- A bound on the longest word after the program, from a bound `L` before it. -/
def lenBound : Prog k → ℕ → ℕ
  | prim p, L => L + p.grow
  | coin _, L => L + 1
  | seq p q, L => lenBound q (lenBound p L)
  | ifBlank _ p q, L => max (lenBound p L) (lenBound q L)
  | ifBit _ p q, L => max (lenBound p L) (lenBound q L)
  | loop _ body, L => iterMax (lenBound body) L

/-- The time of one round of a loop on words at most `L` long: the column machine dropping the
first bit of the counter, then the body. -/
def roundTime (bodyTime : ℕ → ℕ) (L : ℕ) : ℕ := (2 * L + 3) + bodyTime L

/-- A bound on the steps of the compiled machine, from a bound `L` on the longest word. -/
def timeBound : Prog k → ℕ → ℕ
  | prim p, L => 2 * (L + p.pad) + 3
  | coin _, L => 2 * L + 4
  | seq p q, L => timeBound p L + timeBound q (lenBound p L)
  | ifBlank _ p q, L => max (timeBound p L) (timeBound q L) + 1
  | ifBit _ p q, L => max (timeBound p L) (timeBound q L) + 1
  | loop _ body, L =>
    L * ((Finset.range L).sup (fun j => roundTime (timeBound body) ((lenBound body)^[j] L)) + 1) + 2

/-! ### Supports -/

theorem mem_support_iterate {σ : Type} (n : ℕ) (f : σ → ProbComp σ) (s₀ : σ) (inv : ℕ → σ → Prop)
    (h0 : inv 0 s₀) (hstep : ∀ m t, inv m t → ∀ t' ∈ (ProbComp.eval (f t)).support, inv (m + 1) t') :
    ∀ t ∈ (ProbComp.eval (OracleComp.iterate n f s₀)).support, inv n t := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    intro t ht
    rw [OracleComp.iterate_succ, ProbComp.eval_bind, PMF.mem_support_bind_iff] at ht
    obtain ⟨a, ha, ht⟩ := ht
    exact hstep n a (ih a ha) t ht

/-- **Length bound**: after `p`, every word is at most `lenBound p L` long. -/
theorem lenBound_spec (p : Prog k) :
    ∀ (L : ℕ) (s : Store k), maxLen s ≤ L → ∀ s' ∈ (p.law s).support, maxLen s' ≤ lenBound p L := by
  induction p with
  | prim p =>
    intro L s hs s' hs'
    simp only [law, denote, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact p.maxLen_apply s hs
  | coin i =>
    intro L s hs s' hs'
    simp only [law, denote, ProbComp.eval_map, PMF.support_map, Set.mem_image] at hs'
    obtain ⟨b, _, rfl⟩ := hs'
    exact maxLen_update_le s i _ (by simp only [lenBound]; omega) (by simp [lenBound])
  | seq p q ihp ihq =>
    intro L s hs s' hs'
    simp only [law, denote, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨a, ha, hs'⟩ := hs'
    exact ihq _ a (ihp L s hs a ha) s' hs'
  | ifBlank i p q ihp ihq =>
    intro L s hs s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact (ihp L s hs s' hs').trans (le_max_left _ _)
    · exact (ihq L s hs s' hs').trans (le_max_right _ _)
  | ifBit i p q ihp ihq =>
    intro L s hs s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact (ihp L s hs s' hs').trans (le_max_left _ _)
    · exact (ihq L s hs s' hs').trans (le_max_right _ _)
  | loop i body ih =>
    intro L s hs s' hs'
    have hn : (s i).length ≤ L := (length_le_maxLen s i).trans hs
    have := mem_support_iterate (s i).length (fun t => denote body (tailAt i t)) s
      (fun m t => maxLen t ≤ (lenBound body)^[m] L) hs
      (fun m t ht t' ht' => by
        rw [Function.iterate_succ_apply']
        exact ih _ _ ((maxLen_tailAt i t).trans ht) t' ht') s' hs'
    exact this.trans (le_iterMax _ hn)

/-- **Preserved tapes**: a program that never writes tape `i` leaves its word alone. -/
theorem preserves_spec (i : Fin k) (p : Prog k) (hp : p.Preserves i) :
    ∀ (s : Store k), ∀ s' ∈ (p.law s).support, s' i = s i := by
  induction p with
  | prim p =>
    intro s s' hs'
    simp only [law, denote, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact p.apply_of_not_mem s hp
  | coin j =>
    intro s s' hs'
    simp only [law, denote, ProbComp.eval_map, PMF.support_map, Set.mem_image] at hs'
    obtain ⟨b, _, rfl⟩ := hs'
    simp [Function.update, show i ≠ j from fun h => hp h.symm]
  | seq p q ihp ihq =>
    intro s s' hs'
    simp only [law, denote, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨a, ha, hs'⟩ := hs'
    exact (ihq hp.2 a s' hs').trans (ihp hp.1 s a ha)
  | ifBlank j p q ihp ihq =>
    intro s s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact ihp hp.1 s s' hs'
    · exact ihq hp.2 s s' hs'
  | ifBit j p q ihp ihq =>
    intro s s' hs'
    simp only [law, denote] at hs'
    split_ifs at hs'
    · exact ihp hp.1 s s' hs'
    · exact ihq hp.2 s s' hs'
  | loop j body ih =>
    intro s s' hs'
    exact mem_support_iterate (s j).length (fun t => denote body (tailAt j t)) s
      (fun _ t => t i = s i) rfl
      (fun m t ht t' ht' => by
        rw [ih hp.2 _ t' ht']
        simp [tailAt, Function.update, Ne.symm hp.1, ht]) s' hs'

end Prog

end SigabaNeo.Tape
