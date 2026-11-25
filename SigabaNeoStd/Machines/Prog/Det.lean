import SigabaNeoStd.Machines.Prog.Compile

/-!
# Deterministic, non-lengthening tape programs

The word algorithms of the tape language are written in a fragment where reasoning is cheap:

* `Prog.NoGrow p`: `p` uses no coin and only the primitives that never lengthen a word (`clear`,
  `copy`, `carry`, `tail`, `pop`). Such a program has a **pure semantics** `run p : Store k → Store k`
  (`law_eq_run : law p s = PMF.pure (run p s)`), keeps the length bound (`lenBound_eq`), and its
  time bound is at most `tbC p * (L + 1) ^ tbD p` (`timeBound_le`), where `tbC p` and `tbD p` are
  read off the syntax (a sum of constants, and one plus the loop nesting depth). Non-lengthening
  programs compose under loops: a loop whose body lengthens words has a length bound exponential
  in the nesting depth, which this fragment avoids. Registers are therefore words of a fixed width,
  initialised by copying a word of the right length (a *template*) supplied by the caller.
* `Prog.map u p`: `p` with its tapes relabelled by `u : Fin n → Fin k`. For an injective `u`,
  `run (map u p) s = Function.extend u (run p (s ∘ u)) s` (`run_map`): programs are written over a
  small fixed set of tapes, where tape equalities are decidable, and placed on any distinct tapes
  of a larger machine. Relabelling changes neither the time bound, nor the length bound, nor the
  number of states, and preserves `NoGrow` and `WF` (`timeBound_map`, `size_map`, …).
* `run_loop_iter`: a loop whose body acts on an abstract state `a` (with the counter left alone)
  runs the abstract step once per bit of its counter.
* Small programs: `sin b i` (shift the bit `b` in at the end of tape `i`, dropping its first bit),
  `push i f` (shift in the first bit of tape `f`), `takeHead f a` (`f := (s a).take 1`), `setZero i`.
-/

namespace SigabaNeo.Tape

open Cslib

variable {k n : ℕ}

/-- The first bit of a word, `false` on the empty word. -/
def hd (w : List Bool) : Bool := w.headD false

@[simp] theorem hd_nil : hd [] = false := rfl
@[simp] theorem hd_cons (b : Bool) (w : List Bool) : hd (b :: w) = b := rfl

theorem head?_eq_some_true (w : List Bool) : w.head? = some true ↔ hd w = true := by
  cases w <;> simp [hd]

namespace Prim

/-- The primitives that never lengthen a word. -/
def noGrowB : Prim k → Bool
  | clear _ | copy _ _ | carry _ _ _ | tail _ | pop _ _ => true
  | _ => false

theorem pad_of_noGrowB {p : Prim k} (h : p.noGrowB = true) : p.pad = 0 := by
  cases p <;> simp_all [noGrowB, pad]

theorem grow_of_noGrowB {p : Prim k} (h : p.noGrowB = true) : p.grow = 0 := by
  cases p <;> simp_all [noGrowB, grow]

/-- Relabel the tapes of a primitive. -/
def map (u : Fin n → Fin k) : Prim n → Prim k
  | clear i => clear (u i)
  | copy i j => copy (u i) (u j)
  | carry f i j => carry f (u i) (u j)
  | tail i => tail (u i)
  | pop i j => pop (u i) (u j)
  | eq i j f => eq (u i) (u j) (u f)
  | cons i b => cons (u i) b
  | snoc i b => snoc (u i) b
  | consHead i j => consHead (u i) (u j)
  | snocHead i j => snocHead (u i) (u j)

theorem pad_map (u : Fin n → Fin k) (p : Prim n) : (p.map u).pad = p.pad := by cases p <;> rfl
theorem grow_map (u : Fin n → Fin k) (p : Prim n) : (p.map u).grow = p.grow := by cases p <;> rfl
theorem noGrowB_map (u : Fin n → Fin k) (p : Prim n) : (p.map u).noGrowB = p.noGrowB := by
  cases p <;> rfl

theorem writes_map (u : Fin n → Fin k) (p : Prim n) : (p.map u).writes = p.writes.map u := by
  cases p <;> rfl

end Prim

/-! ### Extending along an injective relabelling -/

section Extend

variable {u : Fin n → Fin k}

theorem extend_comp_self (s : Store k) : Function.extend u (s ∘ u) s = s := by
  funext t
  by_cases ht : ∃ m, u m = t
  · rw [Function.extend_def, dite_eq_left_of_eq_true (eq_true ht)]
    exact congrArg s (Classical.choose_spec ht)
  · rw [Function.extend_apply' _ _ _ ht]

theorem extend_update (hu : Function.Injective u) (w : Store n) (s : Store k) (i : Fin n)
    (a : List Bool) :
    Function.extend u (Function.update w i a) s = Function.update (Function.extend u w s) (u i) a := by
  funext t
  by_cases ht : ∃ m, u m = t
  · obtain ⟨m, rfl⟩ := ht
    rw [hu.extend_apply]
    by_cases hm : m = i
    · subst hm; simp
    · rw [Function.update_of_ne hm, Function.update_of_ne (hu.ne hm), hu.extend_apply]
  · rw [Function.extend_apply' _ _ _ ht, Function.update_of_ne, Function.extend_apply' _ _ _ ht]
    rintro rfl; exact ht ⟨i, rfl⟩

theorem extend_comp_of_inj (hu : Function.Injective u) (w : Store n) (s : Store k) :
    Function.extend u w s ∘ u = w :=
  Function.extend_comp hu w s

theorem extend_extend (hu : Function.Injective u) (w v : Store n) (s : Store k) :
    Function.extend u w (Function.extend u v s) = Function.extend u w s := by
  funext t
  by_cases ht : ∃ m, u m = t
  · obtain ⟨m, rfl⟩ := ht
    rw [hu.extend_apply, hu.extend_apply]
  · rw [Function.extend_apply' _ _ _ ht, Function.extend_apply' _ _ _ ht,
      Function.extend_apply' _ _ _ ht]

theorem extend_apply_of_not_mem (w : Store n) (s : Store k) {t : Fin k} (ht : ∀ m, u m ≠ t) :
    Function.extend u w s t = s t :=
  Function.extend_apply' _ _ _ fun ⟨m, hm⟩ => ht m hm

end Extend

theorem Prim.apply_map {u : Fin n → Fin k} (hu : Function.Injective u) (p : Prim n) (s : Store k) :
    (p.map u).apply s = Function.extend u (p.apply (s ∘ u)) s := by
  cases p <;> simp [Prim.apply, Prim.map, extend_update hu, extend_comp_self]

namespace Prog

/-! ### The fragment -/

/-- No coin, and only primitives that never lengthen a word. -/
def noGrowB : Prog k → Bool
  | prim p => p.noGrowB
  | coin _ => false
  | seq p q => p.noGrowB && q.noGrowB
  | ifBlank _ p q => p.noGrowB && q.noGrowB
  | ifBit _ p q => p.noGrowB && q.noGrowB
  | loop _ body => body.noGrowB

/-- `p` is deterministic and never lengthens a word. -/
def NoGrow (p : Prog k) : Prop := p.noGrowB = true

instance (p : Prog k) : Decidable p.NoGrow := inferInstanceAs (Decidable (_ = _))

/-- `Preserves`, as a boolean. -/
def preservesB (i : Fin k) : Prog k → Bool
  | prim p => !p.writes.contains i
  | coin j => j != i
  | seq p q => preservesB i p && preservesB i q
  | ifBlank _ p q => preservesB i p && preservesB i q
  | ifBit _ p q => preservesB i p && preservesB i q
  | loop j body => j != i && preservesB i body

theorem preserves_of_preservesB {i : Fin k} : ∀ {p : Prog k}, p.preservesB i = true → p.Preserves i
  | prim p, h => by simpa [preservesB, Preserves] using h
  | coin j, h => by simpa [preservesB, Preserves] using h
  | seq p q, h => by
    simp only [preservesB, Bool.and_eq_true] at h
    exact ⟨preserves_of_preservesB h.1, preserves_of_preservesB h.2⟩
  | ifBlank _ p q, h => by
    simp only [preservesB, Bool.and_eq_true] at h
    exact ⟨preserves_of_preservesB h.1, preserves_of_preservesB h.2⟩
  | ifBit _ p q, h => by
    simp only [preservesB, Bool.and_eq_true] at h
    exact ⟨preserves_of_preservesB h.1, preserves_of_preservesB h.2⟩
  | loop j body, h => by
    simp only [preservesB, Bool.and_eq_true, bne_iff_ne] at h
    exact ⟨h.1, preserves_of_preservesB h.2⟩

/-- `WF`, as a boolean. -/
def wfB : Prog k → Bool
  | prim _ | coin _ => true
  | seq p q => wfB p && wfB q
  | ifBlank _ p q => wfB p && wfB q
  | ifBit _ p q => wfB p && wfB q
  | loop i body => wfB body && preservesB i body

theorem wf_of_wfB : ∀ {p : Prog k}, p.wfB = true → p.WF
  | prim _, _ | coin _, _ => trivial
  | seq p q, h => by
    simp only [wfB, Bool.and_eq_true] at h; exact ⟨wf_of_wfB h.1, wf_of_wfB h.2⟩
  | ifBlank _ p q, h => by
    simp only [wfB, Bool.and_eq_true] at h; exact ⟨wf_of_wfB h.1, wf_of_wfB h.2⟩
  | ifBit _ p q, h => by
    simp only [wfB, Bool.and_eq_true] at h; exact ⟨wf_of_wfB h.1, wf_of_wfB h.2⟩
  | loop i body, h => by
    simp only [wfB, Bool.and_eq_true] at h
    exact ⟨wf_of_wfB h.1, preserves_of_preservesB h.2⟩

/-! ### Pure semantics -/

/-- The semantics of a coin-free program as a function (a coin is read as `false`). -/
def run : Prog k → Store k → Store k
  | prim p, s => p.apply s
  | coin i, s => Function.update s i [false]
  | seq p q, s => run q (run p s)
  | ifBlank i p q, s => if s i = [] then run p s else run q s
  | ifBit i p q, s => if hd (s i) = true then run p s else run q s
  | loop i body, s => (fun t => run body (tailAt i t))^[(s i).length] s

theorem run_prim (p : Prim k) (s : Store k) : run (prim p) s = p.apply s := rfl
@[simp] theorem run_seq (p q : Prog k) (s : Store k) : run (seq p q) s = run q (run p s) := rfl
theorem run_ifBlank (i : Fin k) (p q : Prog k) (s : Store k) :
    run (ifBlank i p q) s = if s i = [] then run p s else run q s := rfl
theorem run_ifBit (i : Fin k) (p q : Prog k) (s : Store k) :
    run (ifBit i p q) s = if hd (s i) = true then run p s else run q s := rfl
theorem run_loop (i : Fin k) (body : Prog k) (s : Store k) :
    run (loop i body) s = (fun t => run body (tailAt i t))^[(s i).length] s := rfl

theorem iterate_pure {σ : Type} (g : σ → σ) :
    ∀ (m : ℕ) (s : σ), OracleComp.iterate (spec := Cslib.unifSpec) m (fun t => pure (g t)) s =
      pure (g^[m] s)
  | 0, s => rfl
  | m + 1, s => by
    rw [OracleComp.iterate_succ_bind, pure_bind, iterate_pure g m (g s),
      Function.iterate_succ_apply]

/-- A program in the fragment denotes its pure semantics. -/
theorem denote_eq_run : ∀ (p : Prog k), p.NoGrow → ∀ s, p.denote s = pure (p.run s)
  | prim p, _, s => rfl
  | coin i, h, s => absurd h (by simp [NoGrow, noGrowB])
  | seq p q, h, s => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, denote_eq_run p h.1, pure_bind, denote_eq_run q h.2]; rfl
  | ifBlank i p q, h, s => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, run, denote_eq_run p h.1, denote_eq_run q h.2]; split_ifs <;> rfl
  | ifBit i p q, h, s => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [denote, run, denote_eq_run p h.1, denote_eq_run q h.2]
    simp only [head?_eq_some_true]
    split_ifs <;> rfl
  | loop i body, h, s => by
    have hb : body.NoGrow := h
    rw [denote, run]
    have : (fun t => denote body (tailAt i t)) = fun t => pure (run body (tailAt i t)) :=
      funext fun t => denote_eq_run body hb _
    rw [this]
    exact iterate_pure (fun t => run body (tailAt i t)) _ s

/-- **The law of a program of the fragment** is the point mass at its pure semantics. -/
theorem law_eq_run (p : Prog k) (hp : p.NoGrow) (s : Store k) : p.law s = PMF.pure (p.run s) := by
  rw [law, denote_eq_run p hp s, ProbComp.eval_pure]

/-! ### Loops -/

/-- **Loops on an abstract state.** If the body maps the store `G a` (with any word `w` on the
counter) to `G (step a)` (with the counter unchanged) whenever `I a`, the loop runs `step` once per
bit of the counter and leaves the counter blank. -/
theorem run_loop_iter {σ : Type} (i : Fin k) (body : Prog k) (G : σ → Store k) (step : σ → σ)
    (I : σ → Prop)
    (hstep : ∀ a w, I a → run body (Function.update (G a) i w) = Function.update (G (step a)) i w)
    (hI : ∀ a, I a → I (step a)) :
    ∀ (w : List Bool) (a : σ), I a →
      run (loop i body) (Function.update (G a) i w) = Function.update (G (step^[w.length] a)) i [] := by
  intro w
  induction w with
  | nil => intro a _; rw [run_loop, Function.update_self]; rfl
  | cons x w ih =>
    intro a ha
    rw [run_loop, Function.update_self, List.length_cons, Function.iterate_succ_apply]
    have h1 : run body (tailAt i (Function.update (G a) i (x :: w))) =
        Function.update (G (step a)) i w := by
      rw [tailAt, Function.update_self, Function.update_idem]; exact hstep a w ha
    have h2 := ih (step a) (hI a ha)
    rw [run_loop, Function.update_self] at h2
    rw [h1, h2, Function.iterate_succ_apply]

/-! ### Length and time bounds -/

theorem lenBound_eq : ∀ (p : Prog k), p.NoGrow → ∀ L, lenBound p L = L
  | prim p, h, L => by
    simp only [lenBound, Prim.grow_of_noGrowB (p := p) h, Nat.add_zero]
  | coin i, h, _ => absurd h (by simp [NoGrow, noGrowB])
  | seq p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [lenBound, lenBound_eq p h.1, lenBound_eq q h.2]
  | ifBlank i p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [lenBound, lenBound_eq p h.1, lenBound_eq q h.2, max_self]
  | ifBit i p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    rw [lenBound, lenBound_eq p h.1, lenBound_eq q h.2, max_self]
  | loop i body, h, L => by
    have hb : lenBound body = id := funext (lenBound_eq body h)
    rw [lenBound, hb, iterMax]
    simp only [Function.iterate_id, id]
    exact Finset.sup_const Finset.nonempty_range_add_one L

/-- The constant of the time bound, read off the syntax. -/
def tbC : Prog k → ℕ
  | prim _ | coin _ => 3
  | seq p q => tbC p + tbC q
  | ifBlank _ p q => tbC p + tbC q + 1
  | ifBit _ p q => tbC p + tbC q + 1
  | loop _ body => tbC body + 4

/-- The degree of the time bound: one plus the loop nesting depth. -/
def tbD : Prog k → ℕ
  | prim _ | coin _ => 1
  | seq p q => max (tbD p) (tbD q)
  | ifBlank _ p q => max (tbD p) (tbD q)
  | ifBit _ p q => max (tbD p) (tbD q)
  | loop _ body => tbD body + 1

theorem one_le_tbD : ∀ p : Prog k, 1 ≤ tbD p
  | prim _ | coin _ => le_rfl
  | seq p _ | ifBlank _ p _ | ifBit _ p _ => (one_le_tbD p).trans (le_max_left _ _)
  | loop _ body => by simp [tbD]

theorem pow_le_pow_max_left (L a b : ℕ) : (L + 1) ^ a ≤ (L + 1) ^ max a b :=
  Nat.pow_le_pow_right (by omega) (le_max_left _ _)

theorem pow_le_pow_max_right (L a b : ℕ) : (L + 1) ^ b ≤ (L + 1) ^ max a b :=
  Nat.pow_le_pow_right (by omega) (le_max_right _ _)

/-- **Time bound of the fragment**: `timeBound p L ≤ tbC p * (L + 1) ^ tbD p`. -/
theorem timeBound_le : ∀ (p : Prog k), p.NoGrow → ∀ L, timeBound p L ≤ tbC p * (L + 1) ^ tbD p
  | prim p, h, L => by
    simp only [timeBound, Prim.pad_of_noGrowB (p := p) h, tbC, tbD, pow_one]; omega
  | coin i, h, _ => absurd h (by simp [NoGrow, noGrowB])
  | seq p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    have hp := timeBound_le p h.1 L
    have hq := timeBound_le q h.2 L
    have h1 := pow_le_pow_max_left L (tbD p) (tbD q)
    have h2 := pow_le_pow_max_right L (tbD p) (tbD q)
    rw [timeBound, lenBound_eq p h.1, tbC, tbD, Nat.add_mul]
    exact Nat.add_le_add (hp.trans (Nat.mul_le_mul_left _ h1)) (hq.trans (Nat.mul_le_mul_left _ h2))
  | ifBlank i p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    have hp := timeBound_le p h.1 L
    have hq := timeBound_le q h.2 L
    have h1 := pow_le_pow_max_left L (tbD p) (tbD q)
    have h2 := pow_le_pow_max_right L (tbD p) (tbD q)
    have h3 : 1 ≤ (L + 1) ^ max (tbD p) (tbD q) := Nat.one_le_pow _ _ (by omega)
    rw [timeBound, tbC, tbD, Nat.add_mul, Nat.add_mul, one_mul]
    have := Nat.mul_le_mul_left (tbC p) h1
    have := Nat.mul_le_mul_left (tbC q) h2
    have := max_le_add_of_nonneg (Nat.zero_le (timeBound p L)) (Nat.zero_le (timeBound q L))
    omega
  | ifBit i p q, h, L => by
    simp only [NoGrow, noGrowB, Bool.and_eq_true] at h
    have hp := timeBound_le p h.1 L
    have hq := timeBound_le q h.2 L
    have h1 := pow_le_pow_max_left L (tbD p) (tbD q)
    have h2 := pow_le_pow_max_right L (tbD p) (tbD q)
    have h3 : 1 ≤ (L + 1) ^ max (tbD p) (tbD q) := Nat.one_le_pow _ _ (by omega)
    rw [timeBound, tbC, tbD, Nat.add_mul, Nat.add_mul, one_mul]
    have := Nat.mul_le_mul_left (tbC p) h1
    have := Nat.mul_le_mul_left (tbC q) h2
    have := max_le_add_of_nonneg (Nat.zero_le (timeBound p L)) (Nat.zero_le (timeBound q L))
    omega
  | loop i body, h, L => by
    have hb : body.NoGrow := h
    have hlen : lenBound body = id := funext (lenBound_eq body hb)
    have hX := timeBound_le body hb L
    set X := timeBound body L
    set a := tbC body
    set d := tbD body
    have hd : 1 ≤ d := one_le_tbD body
    have hsup : (Finset.range L).sup (fun j => roundTime (timeBound body) ((lenBound body)^[j] L))
        ≤ 2 * L + 3 + X :=
      Finset.sup_le fun j _ => by rw [hlen, Function.iterate_id, id, roundTime]
    rw [timeBound, tbC, tbD]
    have hP : (L + 1) ≤ (L + 1) ^ d := Nat.le_self_pow (by omega) _
    have hpow : (L + 1) ^ (d + 1) = (L + 1) ^ d * (L + 1) := pow_succ _ _
    have h1 : L * (2 * L + 3 + X + 1) + 2 ≤ (L + 1) * (2 * (L + 1)) + (L + 1) * X := by nlinarith
    have h2 : (L + 1) * X ≤ a * (L + 1) ^ (d + 1) := by
      rw [hpow]; nlinarith
    have h3 : (L + 1) * (2 * (L + 1)) ≤ 4 * (L + 1) ^ (d + 1) := by
      rw [hpow]; nlinarith
    calc L * ((Finset.range L).sup (fun j => roundTime (timeBound body) ((lenBound body)^[j] L)) + 1) + 2
        ≤ L * (2 * L + 3 + X + 1) + 2 := by
          have := Nat.mul_le_mul_left L (Nat.add_le_add_right hsup 1); omega
      _ ≤ (a + 4) * (L + 1) ^ (d + 1) := by rw [Nat.add_mul]; omega

/-! ### Relabelling -/

/-- Relabel the tapes of a program. -/
def map (u : Fin n → Fin k) : Prog n → Prog k
  | prim p => prim (p.map u)
  | coin i => coin (u i)
  | seq p q => seq (map u p) (map u q)
  | ifBlank i p q => ifBlank (u i) (map u p) (map u q)
  | ifBit i p q => ifBit (u i) (map u p) (map u q)
  | loop i body => loop (u i) (map u body)

section Map

variable (u : Fin n → Fin k)

theorem noGrowB_map : ∀ p : Prog n, (map u p).noGrowB = p.noGrowB
  | prim p => Prim.noGrowB_map u p
  | coin _ => rfl
  | seq p q | ifBlank _ p q | ifBit _ p q => by
    simp only [map, noGrowB, noGrowB_map p, noGrowB_map q]
  | loop _ body => noGrowB_map body

theorem NoGrow.map {p : Prog n} (hp : p.NoGrow) : (map u p).NoGrow := by
  rw [NoGrow, noGrowB_map]; exact hp

theorem lenBound_map : ∀ (p : Prog n) (L : ℕ), lenBound (map u p) L = lenBound p L
  | prim p, L => by simp only [map, lenBound, Prim.grow_map]
  | coin _, L => rfl
  | seq p q, L => by simp only [map, lenBound, lenBound_map p, lenBound_map q]
  | ifBlank _ p q, L | ifBit _ p q, L => by simp only [map, lenBound, lenBound_map p, lenBound_map q]
  | loop _ body, L => by
    have : lenBound (map u body) = lenBound body := funext (lenBound_map body)
    simp only [map, lenBound, this]

theorem timeBound_map : ∀ (p : Prog n) (L : ℕ), timeBound (map u p) L = timeBound p L
  | prim p, L => by simp only [map, timeBound, Prim.pad_map]
  | coin _, L => rfl
  | seq p q, L => by simp only [map, timeBound, timeBound_map p, timeBound_map q, lenBound_map]
  | ifBlank _ p q, L | ifBit _ p q, L => by
    simp only [map, timeBound, timeBound_map p, timeBound_map q]
  | loop _ body, L => by
    have h1 : timeBound (map u body) = timeBound body := funext (timeBound_map body)
    have h2 : lenBound (map u body) = lenBound body := funext (lenBound_map u body)
    simp only [map, timeBound, h1, h2]

theorem size_map : ∀ p : Prog n, size (map u p) = size p
  | prim p => by simp only [map, size, Prim.pad_map]
  | coin _ => rfl
  | seq p q | ifBlank _ p q | ifBit _ p q => by simp only [map, size, size_map p, size_map q]
  | loop _ body => by simp only [map, size, size_map body]

theorem tbC_map : ∀ p : Prog n, tbC (map u p) = tbC p
  | prim _ | coin _ => rfl
  | seq p q | ifBlank _ p q | ifBit _ p q => by simp only [map, tbC, tbC_map p, tbC_map q]
  | loop _ body => by simp only [map, tbC, tbC_map body]

theorem tbD_map : ∀ p : Prog n, tbD (map u p) = tbD p
  | prim _ | coin _ => rfl
  | seq p q | ifBlank _ p q | ifBit _ p q => by simp only [map, tbD, tbD_map p, tbD_map q]
  | loop _ body => by simp only [map, tbD, tbD_map body]

variable {u}

theorem preserves_map (hu : Function.Injective u) (i : Fin n) :
    ∀ p : Prog n, (map u p).Preserves (u i) ↔ p.Preserves i
  | prim p => by
    simp only [map, Preserves, Prim.writes_map, List.mem_map, not_exists, not_and]
    constructor
    · intro h hi; exact h i hi rfl
    · intro h j hj hji; exact h (hu hji ▸ hj)
  | coin j => by simp only [map, Preserves, ne_eq, hu.eq_iff]
  | seq p q | ifBlank _ p q | ifBit _ p q => by
    simp only [map, Preserves, preserves_map hu i p, preserves_map hu i q]
  | loop j body => by simp only [map, Preserves, ne_eq, hu.eq_iff, preserves_map hu i body]

/-- A relabelled program never writes a tape outside the image of the relabelling. -/
theorem preserves_map_of_not_mem {t : Fin k} (ht : ∀ m, u m ≠ t) :
    ∀ p : Prog n, (map u p).Preserves t
  | prim p => by
    simp only [map, Preserves, Prim.writes_map, List.mem_map, not_exists, not_and]
    intro m _ h; exact ht m h
  | coin j => ht j
  | seq p q | ifBlank _ p q | ifBit _ p q =>
    ⟨preserves_map_of_not_mem ht p, preserves_map_of_not_mem ht q⟩
  | loop j body => ⟨ht j, preserves_map_of_not_mem ht body⟩

theorem WF.map (hu : Function.Injective u) : ∀ {p : Prog n}, p.WF → (map u p).WF
  | prim _, _ | coin _, _ => trivial
  | seq _ _, h | ifBlank _ _ _, h | ifBit _ _ _, h => ⟨WF.map hu h.1, WF.map hu h.2⟩
  | loop i _, h => ⟨WF.map hu h.1, (preserves_map hu i _).mpr h.2⟩

/-- **Semantics of a relabelled program**: it acts on the tapes `u m` as the program does on the
tapes `m`, and leaves the other tapes alone. -/
theorem run_map (hu : Function.Injective u) :
    ∀ (p : Prog n) (s : Store k), run (map u p) s = Function.extend u (run p (s ∘ u)) s
  | prim p, s => Prim.apply_map hu p s
  | coin i, s => by
    simp only [map, run, extend_update hu, extend_comp_self]
  | seq p q, s => by
    rw [map, run_seq, run_map hu p, run_map hu q, extend_comp_of_inj hu, extend_extend hu]; rfl
  | ifBlank i p q, s => by
    simp only [map, run_ifBlank, run_map hu p, run_map hu q]
    show _ = Function.extend u (if s (u i) = [] then _ else _) s
    split_ifs <;> rfl
  | ifBit i p q, s => by
    simp only [map, run_ifBit, run_map hu p, run_map hu q]
    show _ = Function.extend u (if hd (s (u i)) = true then _ else _) s
    split_ifs <;> rfl
  | loop i body, s => by
    rw [map, run_loop, run_loop]
    have key : ∀ (m : ℕ) (v : Store n),
        (fun t => run (map u body) (tailAt (u i) t))^[m] (Function.extend u v s) =
          Function.extend u ((fun t => run body (tailAt i t))^[m] v) s := by
      intro m
      induction m with
      | zero => intro v; rfl
      | succ m ih =>
        intro v
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
        congr 1
        have ht : tailAt (u i) (Function.extend u v s) = Function.extend u (tailAt i v) s := by
          rw [tailAt, tailAt, extend_update hu, hu.extend_apply]
        rw [ht, run_map hu body, extend_comp_of_inj hu, extend_extend hu]
    have := key (s (u i)).length (s ∘ u)
    rw [extend_comp_self] at this
    exact this

/-- A relabelled program whose specification is an update of one tape. -/
theorem run_map_eq_update (hu : Function.Injective u) (p : Prog n) (s : Store k)
    (o : Fin n) (v : List Bool) (h : run p (s ∘ u) = Function.update (s ∘ u) o v) :
    run (map u p) s = Function.update s (u o) v := by
  rw [run_map hu, h, extend_update hu, extend_comp_self]

/-- The law of a relabelled program of the fragment whose specification is an update. -/
theorem law_map_eq_update (hu : Function.Injective u) (p : Prog n) (hp : p.NoGrow) (s : Store k)
    (o : Fin n) (v : List Bool) (h : run p (s ∘ u) = Function.update (s ∘ u) o v) :
    law (map u p) s = PMF.pure (Function.update s (u o) v) := by
  rw [law_eq_run _ (hp.map u), run_map_eq_update hu p s o v h]

end Map

/-- **The bounds of a program of the fragment**, from its syntactic constants: the length bound
is the identity, the time is at most `C (L + 1) ^ d`, and the machine has `S` states. Relabelling
changes none of them (`lenBound_map`, `timeBound_map`, `size_map`). -/
theorem bounds_of (p : Prog k) (hp : p.NoGrow) {C d S : ℕ} (hC : tbC p = C) (hd : tbD p = d)
    (hS : size p = S) (L : ℕ) :
    lenBound p L = L ∧ timeBound p L ≤ C * (L + 1) ^ d ∧ size p = S :=
  ⟨lenBound_eq p hp L, hC ▸ hd ▸ timeBound_le p hp L, hS⟩

/-! ### Small programs -/

/-- Shift in the bit `b`: the digit operation whose carry is the next digit (`sin`). -/
def sinOp (b : Bool) : DigitOp := fun x _ c => (xor c b, xor x b)

theorem carryOp_sinOp (b : Bool) (x : Bool) (xs ys : List Bool) :
    carryOp (sinOp b) (x :: xs) ys = (xor x b, xs ++ [b]) := by
  induction xs generalizing x ys with
  | nil => simp [carryOp, sinOp]
  | cons y xs ih => rw [carryOp, ih]; simp [sinOp]

theorem carryOp_sinOp_snd (b : Bool) (w ys : List Bool) :
    (carryOp (sinOp b) w ys).2 = (w ++ [b]).tail := by
  cases w with
  | nil => rfl
  | cons x xs => rw [carryOp_sinOp]; rfl

/-- The digit operation writing `false` everywhere. -/
def zeroOp : DigitOp := fun _ _ _ => (false, false)

theorem carryOp_zeroOp_snd (w ys : List Bool) :
    (carryOp zeroOp w ys).2 = List.replicate w.length false := by
  induction w generalizing ys with
  | nil => rfl
  | cons x xs ih => simp [carryOp, zeroOp, ih, List.replicate_succ]

/-- `i := (s i).tail ++ [b]`: shift the bit `b` in at the end, keeping the width. -/
def sin (b : Bool) (i : Fin k) : Prog k := prim (.carry (sinOp b) i i)

/-- `i := (s i).tail ++ [hd (s f)]`: shift in the first bit of tape `f`. -/
def push (i f : Fin k) : Prog k := ifBit f (sin true i) (sin false i)

/-- `f := (s a).take 1`. -/
def takeHead (f a : Fin k) : Prog k := seq (prim (.copy f a)) (prim (.pop f f))

/-- `i := 0…0`, keeping the width. -/
def setZero (i : Fin k) : Prog k := prim (.carry zeroOp i i)

/-- The program that does nothing. -/
def nop (i : Fin k) : Prog k := prim (.copy i i)

@[simp] theorem run_sin (b : Bool) (i : Fin k) (s : Store k) :
    run (sin b i) s = Function.update s i ((s i ++ [b]).tail) := by
  simp [sin, run_prim, Prim.apply, carryOp_sinOp_snd]

@[simp] theorem run_push (i f : Fin k) (s : Store k) :
    run (push i f) s = Function.update s i ((s i ++ [hd (s f)]).tail) := by
  simp only [push, run_ifBit, run_sin]
  cases hd (s f) <;> simp

@[simp] theorem run_takeHead (f a : Fin k) (s : Store k) :
    run (takeHead f a) s = Function.update s f ((s a).take 1) := by
  simp [takeHead, run_prim, Prim.apply]

@[simp] theorem run_setZero (i : Fin k) (s : Store k) :
    run (setZero i) s = Function.update s i (List.replicate (s i).length false) := by
  simp [setZero, run_prim, Prim.apply, carryOp_zeroOp_snd]

@[simp] theorem run_nop (i : Fin k) (s : Store k) : run (nop i) s = s := by
  simp [nop, run_prim, Prim.apply]

@[simp] theorem run_clear (i : Fin k) (s : Store k) :
    run (prim (.clear i)) s = Function.update s i [] := rfl
@[simp] theorem run_copy (i j : Fin k) (s : Store k) :
    run (prim (.copy i j)) s = Function.update s i (s j) := rfl
@[simp] theorem run_tail (i : Fin k) (s : Store k) :
    run (prim (.tail i)) s = Function.update s i (s i).tail := rfl
@[simp] theorem run_pop (i j : Fin k) (s : Store k) :
    run (prim (.pop i j)) s = Function.update (Function.update s i (s i).tail) j ((s i).take 1) := rfl

end Prog

end SigabaNeo.Tape
