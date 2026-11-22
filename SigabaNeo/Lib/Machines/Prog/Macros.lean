import SigabaNeo.Lib.Machines.Prog.BoundsT

/-!
# Straight-line macros of the tape language

Deterministic building blocks of `Prog k` with closed-form laws and bounds:

* `iter z p n`: `p` repeated `n` times (`z` only names the tape of the identity `copy z z` that
  ends the repetition); `law_iter`: a total deterministic `p` repeated is its function iterated.
* `moveFront n src dst tmp`: `dst := dst ++ take n src`, `src := drop n src` (one bit per round,
  through the blank tape `tmp`).
* `moveRev n src dst tmp`: `dst := reverse (take n src) ++ dst`, `src := drop n src`.
* `prependN n src dst t₁ t₂`: for `|src| = n`, `dst := src ++ dst` and `src := []`.
* `dropN n i`: `i := drop n i`.

Each comes with its law (a point mass), a per-tape length bound (`lenBoundT`) and a time bound
through the scalar bounds (`timeBound`, `lenBound`): `timeBoundT p ℓ ≤ timeBound p (supB ℓ)`
(`timeBoundT_le_timeBound`).
-/

namespace SigabaNeo.Tape

open Cslib

namespace Prog

variable {k : ℕ}

/-! ### Laws of the constructors -/

theorem law_prim (p : Prim k) (s : Store k) : law (prim p) s = PMF.pure (p.apply s) := by
  simp [law, denote]

theorem law_seq (p q : Prog k) (s : Store k) : law (seq p q) s = (law p s).bind (law q) := by
  simp [law, denote]; rfl

theorem law_ifBlank (i : Fin k) (p q : Prog k) (s : Store k) :
    law (ifBlank i p q) s = if s i = [] then law p s else law q s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_ifBit (i : Fin k) (p q : Prog k) (s : Store k) :
    law (ifBit i p q) s = if (s i).head? = some true then law p s else law q s := by
  simp only [law, denote]; split_ifs <;> rfl

theorem law_seq_pure {p q : Prog k} {s t : Store k} (hp : law p s = PMF.pure t) :
    law (seq p q) s = law q t := by
  rw [law_seq, hp, PMF.pure_bind]

/-- The global time bound dominates the per-tape one. -/
theorem timeBoundT_le_timeBound (p : Prog k) (ℓ : Fin k → ℕ) :
    timeBoundT p ℓ ≤ timeBound p (supB ℓ) :=
  (timeBoundT_mono p fun t => le_supB ℓ t).trans (timeBoundT_const_le p _)

/-! ### Repetition -/

/-- `p` repeated `n` times, then the identity `copy z z`. -/
def iter (z : Fin k) (p : Prog k) : ℕ → Prog k
  | 0 => prim (.copy z z)
  | n + 1 => seq p (iter z p n)

theorem apply_copy_self (z : Fin k) (s : Store k) : (Prim.copy z z).apply s = s := by
  simp [Prim.apply]

theorem law_iter (z : Fin k) (p : Prog k) (f : Store k → Store k)
    (hp : ∀ s, law p s = PMF.pure (f s)) : ∀ n s, law (iter z p n) s = PMF.pure (f^[n] s)
  | 0, s => by simp [iter, law_prim, apply_copy_self]
  | n + 1, s => by
    rw [iter, law_seq_pure (hp s), law_iter z p f hp n, Function.iterate_succ_apply]

theorem wf_iter (z : Fin k) (p : Prog k) (hp : p.WF) : ∀ n, (iter z p n).WF
  | 0 => trivial
  | n + 1 => ⟨hp, wf_iter z p hp n⟩

theorem lenBoundT_iter (z : Fin k) (p : Prog k) :
    ∀ n ℓ, lenBoundT (iter z p n) ℓ = (lenBoundT p)^[n] ℓ
  | 0, ℓ => by simp [iter, lenBoundT, Prim.lenT]
  | n + 1, ℓ => by
    rw [iter, lenBoundT, lenBoundT_iter z p n, Function.iterate_succ_apply]

theorem lenBound_iter_le (z : Fin k) (p : Prog k) {d : ℕ} (hd : ∀ L, lenBound p L ≤ L + d) :
    ∀ n L, lenBound (iter z p n) L ≤ L + n * d
  | 0, L => by show L + 0 ≤ L + 0 * d; omega
  | n + 1, L => by
    simp only [iter, lenBound]
    have h1 := lenBound_iter_le z p hd n (lenBound p L)
    have h2 := hd L
    nlinarith

theorem timeBound_iter_le (z : Fin k) (p : Prog k) {a c d : ℕ}
    (hd : ∀ L, lenBound p L ≤ L + d) (ht : ∀ L, timeBound p L ≤ a * L + c) :
    ∀ n L, timeBound (iter z p n) L ≤ n * (a * (L + n * d) + c) + 2 * (L + n * d) + 3
  | 0, L => by show 2 * (L + 0) + 3 ≤ _; omega
  | n + 1, L => by
    simp only [iter, timeBound]
    have h1 := timeBound_iter_le z p hd ht n (lenBound p L)
    have h2 := hd L
    have h3 := ht L
    have h4 : n * (a * (lenBound p L + n * d) + c) + 2 * (lenBound p L + n * d) + 3 ≤
        n * (a * (L + d + n * d) + c) + 2 * (L + d + n * d) + 3 := by
      have : a * (lenBound p L + n * d) ≤ a * (L + d + n * d) :=
        Nat.mul_le_mul_left _ (by omega)
      have := Nat.mul_le_mul_left n (Nat.add_le_add_right this c)
      omega
    have h5 : a * L + c + (n * (a * (L + d + n * d) + c) + 2 * (L + d + n * d) + 3) ≤
        (n + 1) * (a * (L + (n + 1) * d) + c) + 2 * (L + (n + 1) * d) + 3 := by
      ring_nf; nlinarith [Nat.zero_le (a * n * d), Nat.zero_le (a * d)]
    omega

/-! ### Moving bits one at a time -/

/-- One round of `moveFront`: `src := tail src`, `dst := dst ++ take 1 src`. -/
def stepF (src dst tmp : Fin k) : Prog k :=
  seq (prim (.pop src tmp)) (seq (prim (.snocHead dst tmp)) (prim (.clear tmp)))

/-- One round of `moveRev`: `src := tail src`, `dst := take 1 src ++ dst`. -/
def stepR (src dst tmp : Fin k) : Prog k :=
  seq (prim (.pop src tmp)) (seq (prim (.consHead dst tmp)) (prim (.clear tmp)))

/-- `dst := dst ++ take n src`, `src := drop n src`. -/
def moveFront (n : ℕ) (src dst tmp : Fin k) : Prog k := iter src (stepF src dst tmp) n

/-- `dst := reverse (take n src) ++ dst`, `src := drop n src`. -/
def moveRev (n : ℕ) (src dst tmp : Fin k) : Prog k := iter src (stepR src dst tmp) n

/-- `dst := src ++ dst` for `|src| = n`, through the blank tapes `t₁`, `t₂`. -/
def prependN (n : ℕ) (src dst t₁ t₂ : Fin k) : Prog k :=
  seq (moveRev n src t₁ t₂) (moveRev n t₁ dst t₂)

/-- `i := replicate n b ++ i`. -/
def consN (n : ℕ) (i : Fin k) (b : Bool) : Prog k := iter i (prim (.cons i b)) n

/-- `i := drop n i`. -/
def dropN (n : ℕ) (i : Fin k) : Prog k := iter i (prim (.tail i)) n

section Move

variable {src dst tmp : Fin k}

/-- The function of `stepF`. -/
def fF (src dst tmp : Fin k) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src (s src).tail) dst
    (s dst ++ (s src).take 1)) tmp []

/-- The function of `stepR`. -/
def fR (src dst tmp : Fin k) (s : Store k) : Store k :=
  Function.update (Function.update (Function.update s src (s src).tail) dst
    ((s src).take 1 ++ s dst)) tmp []

theorem law_stepF (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (s : Store k) :
    law (stepF src dst tmp) s = PMF.pure (fF src dst tmp s) := by
  simp only [stepF, law_seq, law_prim, PMF.pure_bind]
  congr 1
  funext j
  simp only [Prim.apply, fF, Function.update_apply]
  by_cases hj1 : j = tmp <;> by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;>
    simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem law_stepR (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (s : Store k) :
    law (stepR src dst tmp) s = PMF.pure (fR src dst tmp s) := by
  simp only [stepR, law_seq, law_prim, PMF.pure_bind]
  congr 1
  funext j
  simp only [Prim.apply, fR, Function.update_apply]
  by_cases hj1 : j = tmp <;> by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;>
    simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem take_one_append_take_tail (l : List Bool) (n : ℕ) :
    l.take 1 ++ l.tail.take n = l.take (n + 1) := by
  cases l <;> simp [List.take_succ_cons]

theorem reverse_take_one (l : List Bool) : (l.take 1).reverse = l.take 1 := by
  cases l <;> simp

theorem take_length_reverse (l : List Bool) : l.reverse.take l.length = l.reverse := by
  simp [List.take_of_length_le]

theorem iterate_fF (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) :
    ∀ n (s : Store k), s tmp = [] → (fF src dst tmp)^[n] s =
      Function.update (Function.update s src ((s src).drop n)) dst (s dst ++ (s src).take n)
  | 0, s, _ => by simp
  | n + 1, s, hs => by
    rw [Function.iterate_succ_apply, iterate_fF h1 h2 h3 n _ (by simp [fF])]
    funext j
    simp only [fF, Function.update_apply]
    by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;> by_cases hj1 : j = tmp <;>
      simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3, List.drop_tail, List.append_assoc,
        take_one_append_take_tail]

theorem iterate_fR (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) :
    ∀ n (s : Store k), s tmp = [] → (fR src dst tmp)^[n] s =
      Function.update (Function.update s src ((s src).drop n)) dst
        (((s src).take n).reverse ++ s dst)
  | 0, s, _ => by simp
  | n + 1, s, hs => by
    rw [Function.iterate_succ_apply, iterate_fR h1 h2 h3 n _ (by simp [fR])]
    funext j
    simp only [fR, Function.update_apply]
    by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;> by_cases hj1 : j = tmp <;>
      simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3, List.drop_tail, reverse_take_one,
        ← take_one_append_take_tail (s src) n]

/-- **Law of `moveFront`.** -/
theorem law_moveFront (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (s : Store k)
    (hs : s tmp = []) : law (moveFront n src dst tmp) s = PMF.pure
      (Function.update (Function.update s src ((s src).drop n)) dst (s dst ++ (s src).take n)) := by
  rw [moveFront, law_iter src _ _ (law_stepF h1 h2 h3), iterate_fF h1 h2 h3 n s hs]

/-- **Law of `moveRev`.** -/
theorem law_moveRev (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (s : Store k)
    (hs : s tmp = []) : law (moveRev n src dst tmp) s = PMF.pure
      (Function.update (Function.update s src ((s src).drop n)) dst
        (((s src).take n).reverse ++ s dst)) := by
  rw [moveRev, law_iter src _ _ (law_stepR h1 h2 h3), iterate_fR h1 h2 h3 n s hs]

/-- **Law of `prependN`.** -/
theorem law_prependN (n : ℕ) {t₁ t₂ : Fin k} (h12 : src ≠ dst) (h13 : src ≠ t₁) (h14 : src ≠ t₂)
    (h23 : dst ≠ t₁) (h24 : dst ≠ t₂) (h34 : t₁ ≠ t₂) (s : Store k) (hn : (s src).length = n)
    (ht₁ : s t₁ = []) (ht₂ : s t₂ = []) :
    law (prependN n src dst t₁ t₂) s =
      PMF.pure (Function.update (Function.update s src []) dst (s src ++ s dst)) := by
  rw [prependN, law_seq_pure (law_moveRev n h13 h14 h34 s ht₂),
    law_moveRev n (Ne.symm h23) h34 h24 _ (by simp [Ne.symm h14, Ne.symm h34, ht₂])]
  congr 1
  funext j
  simp only [Function.update_apply]
  subst hn
  by_cases hj1 : j = t₁ <;> by_cases hj2 : j = dst <;> by_cases hj3 : j = src <;>
    simp_all [Ne.symm h12, Ne.symm h13, Ne.symm h23, List.take_of_length_le]

/-- **Law of `dropN`.** -/
theorem law_dropN (n : ℕ) (i : Fin k) (s : Store k) :
    law (dropN n i) s = PMF.pure (Function.update s i ((s i).drop n)) := by
  rw [dropN, law_iter i _ (fun s => Function.update s i (s i).tail) (fun s => by
    rw [law_prim]; rfl)]
  congr 1
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp [List.drop_tail]

/-- **Law of `consN`.** -/
theorem law_consN (n : ℕ) (i : Fin k) (b : Bool) (s : Store k) :
    law (consN n i b) s = PMF.pure (Function.update s i (List.replicate n b ++ s i)) := by
  rw [consN, law_iter i _ (fun s => Function.update s i (b :: s i)) (fun s => by
    rw [law_prim]; rfl)]
  congr 1
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp [List.replicate_succ']

/-! ### Well-formedness -/

theorem wf_moveFront (n : ℕ) (src dst tmp : Fin k) : (moveFront n src dst tmp).WF :=
  wf_iter _ _ (by simp [stepF, WF]) n

theorem wf_moveRev (n : ℕ) (src dst tmp : Fin k) : (moveRev n src dst tmp).WF :=
  wf_iter _ _ (by simp [stepR, WF]) n

theorem wf_prependN (n : ℕ) (src dst t₁ t₂ : Fin k) : (prependN n src dst t₁ t₂).WF :=
  ⟨wf_moveRev _ _ _ _, wf_moveRev _ _ _ _⟩

theorem wf_dropN (n : ℕ) (i : Fin k) : (dropN n i).WF := wf_iter _ _ (by simp [WF]) n

theorem wf_consN (n : ℕ) (i : Fin k) (b : Bool) : (consN n i b).WF := wf_iter _ _ (by simp [WF]) n

/-! ### Scalar bounds -/

theorem lenBound_stepF (L : ℕ) : lenBound (stepF src dst tmp) L = L + 1 := by
  simp [stepF, lenBound, Prim.grow]

theorem timeBound_stepF (L : ℕ) : timeBound (stepF src dst tmp) L = 6 * L + 13 := by
  simp [stepF, timeBound, lenBound, Prim.grow, Prim.pad]; ring

theorem lenBound_stepR (L : ℕ) : lenBound (stepR src dst tmp) L = L + 1 := by
  simp [stepR, lenBound, Prim.grow]

theorem timeBound_stepR (L : ℕ) : timeBound (stepR src dst tmp) L = 6 * L + 13 := by
  simp [stepR, timeBound, lenBound, Prim.grow, Prim.pad]; ring

theorem lenBound_moveFront_le (n L : ℕ) : lenBound (moveFront n src dst tmp) L ≤ L + n := by
  have := lenBound_iter_le src (stepF src dst tmp) (d := 1)
    (fun L => (lenBound_stepF L).le) n L
  simpa [moveFront] using this

theorem timeBound_moveFront_le (n L : ℕ) :
    timeBound (moveFront n src dst tmp) L ≤ n * (6 * (L + n) + 13) + 2 * (L + n) + 3 := by
  have := timeBound_iter_le src (stepF src dst tmp) (a := 6) (c := 13) (d := 1)
    (fun L => (lenBound_stepF L).le) (fun L => (timeBound_stepF L).le) n L
  simpa [moveFront] using this

theorem lenBound_moveRev_le (n L : ℕ) : lenBound (moveRev n src dst tmp) L ≤ L + n := by
  have := lenBound_iter_le src (stepR src dst tmp) (d := 1)
    (fun L => (lenBound_stepR L).le) n L
  simpa [moveRev] using this

theorem timeBound_moveRev_le (n L : ℕ) :
    timeBound (moveRev n src dst tmp) L ≤ n * (6 * (L + n) + 13) + 2 * (L + n) + 3 := by
  have := timeBound_iter_le src (stepR src dst tmp) (a := 6) (c := 13) (d := 1)
    (fun L => (lenBound_stepR L).le) (fun L => (timeBound_stepR L).le) n L
  simpa [moveRev] using this

theorem lenBound_prependN_le (n L : ℕ) {t₁ t₂ : Fin k} :
    lenBound (prependN n src dst t₁ t₂) L ≤ L + 2 * n := by
  simp only [prependN, lenBound]
  have h1 := lenBound_moveRev_le (src := src) (dst := t₁) (tmp := t₂) n L
  have h2 := lenBound_moveRev_le (src := t₁) (dst := dst) (tmp := t₂) n
    (lenBound (moveRev n src t₁ t₂) L)
  omega

theorem timeBound_prependN_le (n L : ℕ) {t₁ t₂ : Fin k} :
    timeBound (prependN n src dst t₁ t₂) L ≤ 2 * (n * (6 * (L + 2 * n) + 13) + 2 * (L + 2 * n) + 3) := by
  simp only [prependN, timeBound]
  have h1 := timeBound_moveRev_le (src := src) (dst := t₁) (tmp := t₂) n L
  have h1' := lenBound_moveRev_le (src := src) (dst := t₁) (tmp := t₂) n L
  have h2 := timeBound_moveRev_le (src := t₁) (dst := dst) (tmp := t₂) n
    (lenBound (moveRev n src t₁ t₂) L)
  have h3 : n * (6 * (L + n) + 13) + 2 * (L + n) + 3 ≤
      n * (6 * (L + 2 * n) + 13) + 2 * (L + 2 * n) + 3 := by
    have : 6 * (L + n) + 13 ≤ 6 * (L + 2 * n) + 13 := by omega
    have := Nat.mul_le_mul_left n this
    omega
  have h4 : n * (6 * (lenBound (moveRev n src t₁ t₂) L + n) + 13) +
      2 * (lenBound (moveRev n src t₁ t₂) L + n) + 3 ≤
      n * (6 * (L + 2 * n) + 13) + 2 * (L + 2 * n) + 3 := by
    have : 6 * (lenBound (moveRev n src t₁ t₂) L + n) + 13 ≤ 6 * (L + 2 * n) + 13 := by omega
    have := Nat.mul_le_mul_left n this
    omega
  omega

theorem lenBound_dropN (n : ℕ) (i : Fin k) (L : ℕ) : lenBound (dropN n i) L ≤ L := by
  have := lenBound_iter_le i (prim (.tail i)) (d := 0) (fun L => Nat.le_refl _) n L
  simpa [dropN] using this

theorem timeBound_dropN (n : ℕ) (i : Fin k) (L : ℕ) :
    timeBound (dropN n i) L ≤ n * (2 * L + 3) + 2 * L + 3 := by
  have := timeBound_iter_le i (prim (.tail i)) (a := 2) (c := 3) (d := 0)
    (fun L => Nat.le_refl _) (fun L => by show 2 * (L + 0) + 3 ≤ _; omega) n L
  simpa [dropN] using this

theorem lenBound_consN (n : ℕ) (i : Fin k) (b : Bool) (L : ℕ) : lenBound (consN n i b) L ≤ L + n := by
  have := lenBound_iter_le i (prim (.cons i b)) (d := 1) (fun L => Nat.le_refl _) n L
  simpa [consN] using this

theorem timeBound_consN (n : ℕ) (i : Fin k) (b : Bool) (L : ℕ) :
    timeBound (consN n i b) L ≤ n * (2 * (L + n) + 5) + 2 * (L + n) + 3 := by
  have := timeBound_iter_le i (prim (.cons i b)) (a := 2) (c := 5) (d := 1)
    (fun L => Nat.le_refl _) (fun L => by show 2 * (L + 1) + 3 ≤ _; omega) n L
  simpa [consN] using this

/-! ### Per-tape bounds -/

theorem lenBoundT_moveFront_le (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (ℓ : Fin k → ℕ) : lenBoundT (moveFront n src dst tmp) ℓ ≤
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  rw [moveFront, lenBoundT_iter]
  induction n with
  | zero => intro t; simp [Function.update_apply]; split_ifs <;> simp_all
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (lenBoundT_mono _ ih).trans ?_
    intro t
    simp only [stepF, lenBoundT, Prim.lenT, Function.update_apply]
    by_cases ht1 : t = tmp <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
      (simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]; try omega)

theorem lenBoundT_moveRev_le (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (ℓ : Fin k → ℕ) : lenBoundT (moveRev n src dst tmp) ℓ ≤
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  rw [moveRev, lenBoundT_iter]
  induction n with
  | zero => intro t; simp [Function.update_apply]; split_ifs <;> simp_all
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (lenBoundT_mono _ ih).trans ?_
    intro t
    simp only [stepR, lenBoundT, Prim.lenT, Function.update_apply]
    by_cases ht1 : t = tmp <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
      (simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]; try omega)

theorem lenBoundT_prependN_le (n : ℕ) {t₁ t₂ : Fin k} (h12 : src ≠ dst) (h13 : src ≠ t₁)
    (h14 : src ≠ t₂) (h23 : dst ≠ t₁) (h24 : dst ≠ t₂) (h34 : t₁ ≠ t₂) (ℓ : Fin k → ℕ) :
    lenBoundT (prependN n src dst t₁ t₂) ℓ ≤
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  simp only [prependN, lenBoundT]
  refine (lenBoundT_mono _ (lenBoundT_moveRev_le n h13 h14 h34 ℓ)).trans ?_
  refine (lenBoundT_moveRev_le n (Ne.symm h23) h34 h24 _).trans ?_
  intro t
  simp only [Function.update_apply]
  by_cases ht1 : t = t₁ <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
    simp_all [Ne.symm h12, Ne.symm h13, Ne.symm h23]

theorem lenBoundT_dropN (n : ℕ) (i : Fin k) (ℓ : Fin k → ℕ) :
    lenBoundT (dropN n i) ℓ = Function.update ℓ i (ℓ i - n) := by
  rw [dropN, lenBoundT_iter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs <;> omega

end Move

end Prog

end SigabaNeo.Tape

namespace SigabaNeo.Tape.Prog

variable {k : ℕ}

theorem lenBoundT_consN (n : ℕ) (i : Fin k) (b : Bool) (ℓ : Fin k → ℕ) :
    lenBoundT (consN n i b) ℓ = Function.update ℓ i (ℓ i + n) := by
  rw [consN, lenBoundT_iter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [lenBoundT, Prim.lenT, Function.update_apply]
    split_ifs <;> omega

end SigabaNeo.Tape.Prog

/-! ### Primitive counts of loop-free programs -/

namespace SigabaNeo.Tape.Prog

variable {k : ℕ}

/-- The number of primitives and branchings of a program (loops count `0`). -/
def pcount : Prog k → ℕ
  | prim _ | coin _ => 1
  | seq p q => pcount p + pcount q
  | ifBlank _ p q | ifBit _ p q => pcount p + pcount q + 1
  | loop _ _ => 0

/-- The program has no loop. -/
def LoopFree : Prog k → Prop
  | prim _ | coin _ => True
  | seq p q | ifBlank _ p q | ifBit _ p q => p.LoopFree ∧ q.LoopFree
  | loop _ _ => False

theorem lenBound_le_pcount (p : Prog k) (hp : p.LoopFree) (L : ℕ) : lenBound p L ≤ L + pcount p := by
  induction p generalizing L with
  | prim q => cases q <;> simp [lenBound, pcount, Prim.grow]
  | coin i => simp [lenBound, pcount]
  | seq p q ihp ihq =>
    have h1 := ihp hp.1 L
    have h2 := ihq hp.2 (lenBound p L)
    simp only [lenBound, pcount]; omega
  | ifBlank i p q ihp ihq | ifBit i p q ihp ihq =>
    have h1 := ihp hp.1 L
    have h2 := ihq hp.2 L
    simp only [lenBound, pcount]; omega
  | loop i b ih => exact hp.elim

/-- **The time of a loop-free program**: at most `pcount · (2 (L + pcount) + 5)`. -/
theorem timeBound_le_pcount (p : Prog k) (hp : p.LoopFree) (L : ℕ) :
    timeBound p L ≤ pcount p * (2 * (L + pcount p) + 5) := by
  induction p generalizing L with
  | prim q => cases q <;> simp [timeBound, pcount, Prim.pad] <;> omega
  | coin i => simp [timeBound, pcount]; omega
  | seq p q ihp ihq =>
    have h1 := ihp hp.1 L
    have h2 := ihq hp.2 (lenBound p L)
    have h3 := lenBound_le_pcount p hp.1 L
    simp only [timeBound, pcount]
    have h4 : pcount q * (2 * (lenBound p L + pcount q) + 5) ≤
        pcount q * (2 * (L + pcount p + pcount q) + 5) := Nat.mul_le_mul_left _ (by omega)
    have h5 : pcount p * (2 * (L + pcount p) + 5) ≤ pcount p * (2 * (L + (pcount p + pcount q)) + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    have h6 : pcount p * (2 * (L + (pcount p + pcount q)) + 5) +
        pcount q * (2 * (L + pcount p + pcount q) + 5) =
        (pcount p + pcount q) * (2 * (L + (pcount p + pcount q)) + 5) := by ring
    omega
  | ifBlank i p q ihp ihq | ifBit i p q ihp ihq =>
    have h1 := ihp hp.1 L
    have h2 := ihq hp.2 L
    simp only [timeBound, pcount]
    have h4 : pcount q * (2 * (L + pcount q) + 5) ≤
        pcount q * (2 * (L + (pcount p + pcount q + 1)) + 5) := Nat.mul_le_mul_left _ (by omega)
    have h5 : pcount p * (2 * (L + pcount p) + 5) ≤
        pcount p * (2 * (L + (pcount p + pcount q + 1)) + 5) := Nat.mul_le_mul_left _ (by omega)
    have h6 : pcount p * (2 * (L + (pcount p + pcount q + 1)) + 5) +
        pcount q * (2 * (L + (pcount p + pcount q + 1)) + 5) + 1 ≤
        (pcount p + pcount q + 1) * (2 * (L + (pcount p + pcount q + 1)) + 5) := by ring_nf; omega
    have := max_le_add_of_nonneg (Nat.zero_le (timeBound p L)) (Nat.zero_le (timeBound q L))
    omega
  | loop i b ih => exact hp.elim

/-- The per-tape time of a loop-free program. -/
theorem timeBoundT_le_pcount (p : Prog k) (hp : p.LoopFree) (ℓ : Fin k → ℕ) {M : ℕ}
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT p ℓ ≤ pcount p * (2 * (M + pcount p) + 5) := by
  refine (timeBoundT_le_timeBound p ℓ).trans ((timeBound_le_pcount p hp _).trans ?_)
  have : supB ℓ ≤ M := Finset.sup_le fun t _ => hM t
  exact Nat.mul_le_mul_left _ (by omega)

theorem pcount_iter (z : Fin k) (p : Prog k) (n : ℕ) : pcount (iter z p n) = n * pcount p + 1 := by
  induction n with
  | zero => simp [iter, pcount]
  | succ n ih => simp only [iter, pcount, ih]; ring

theorem loopFree_iter (z : Fin k) (p : Prog k) (hp : p.LoopFree) : ∀ n, (iter z p n).LoopFree
  | 0 => trivial
  | n + 1 => ⟨hp, loopFree_iter z p hp n⟩

@[simp] theorem pcount_moveFront (n : ℕ) (src dst tmp : Fin k) :
    pcount (moveFront n src dst tmp) = 3 * n + 1 := by
  rw [moveFront, pcount_iter]; simp [stepF, pcount]; ring

@[simp] theorem pcount_moveRev (n : ℕ) (src dst tmp : Fin k) :
    pcount (moveRev n src dst tmp) = 3 * n + 1 := by
  rw [moveRev, pcount_iter]; simp [stepR, pcount]; ring

@[simp] theorem pcount_prependN (n : ℕ) (src dst t₁ t₂ : Fin k) :
    pcount (prependN n src dst t₁ t₂) = 6 * n + 2 := by
  simp [prependN, pcount]; ring

@[simp] theorem pcount_dropN (n : ℕ) (i : Fin k) : pcount (dropN n i) = n + 1 := by
  rw [dropN, pcount_iter]; simp [pcount]

@[simp] theorem pcount_consN (n : ℕ) (i : Fin k) (b : Bool) : pcount (consN n i b) = n + 1 := by
  rw [consN, pcount_iter]; simp [pcount]

theorem loopFree_moveFront (n : ℕ) (src dst tmp : Fin k) : (moveFront n src dst tmp).LoopFree :=
  loopFree_iter _ _ (by simp [stepF, LoopFree]) n

theorem loopFree_moveRev (n : ℕ) (src dst tmp : Fin k) : (moveRev n src dst tmp).LoopFree :=
  loopFree_iter _ _ (by simp [stepR, LoopFree]) n

theorem loopFree_prependN (n : ℕ) (src dst t₁ t₂ : Fin k) : (prependN n src dst t₁ t₂).LoopFree :=
  ⟨loopFree_moveRev _ _ _ _, loopFree_moveRev _ _ _ _⟩

theorem loopFree_dropN (n : ℕ) (i : Fin k) : (dropN n i).LoopFree :=
  loopFree_iter _ _ (by simp [LoopFree]) n

theorem loopFree_consN (n : ℕ) (i : Fin k) (b : Bool) : (consN n i b).LoopFree :=
  loopFree_iter _ _ (by simp [LoopFree]) n

/-! ### Exact per-tape bounds -/

section Exact

variable {src dst tmp : Fin k}

theorem lenBoundT_moveFront (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (ℓ : Fin k → ℕ) (hℓ : ℓ tmp = 0) : lenBoundT (moveFront n src dst tmp) ℓ =
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  rw [moveFront, lenBoundT_iter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [stepF, lenBoundT, Prim.lenT, Function.update_apply]
    by_cases ht1 : t = tmp <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
      (simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]; try omega)

theorem lenBoundT_moveRev (n : ℕ) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (ℓ : Fin k → ℕ) (hℓ : ℓ tmp = 0) : lenBoundT (moveRev n src dst tmp) ℓ =
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  rw [moveRev, lenBoundT_iter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [stepR, lenBoundT, Prim.lenT, Function.update_apply]
    by_cases ht1 : t = tmp <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
      (simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]; try omega)

theorem lenBoundT_prependN (n : ℕ) {t₁ t₂ : Fin k} (h12 : src ≠ dst) (h13 : src ≠ t₁)
    (h14 : src ≠ t₂) (h23 : dst ≠ t₁) (h24 : dst ≠ t₂) (h34 : t₁ ≠ t₂) (ℓ : Fin k → ℕ)
    (hℓ : ℓ t₂ = 0) : lenBoundT (prependN n src dst t₁ t₂) ℓ =
      Function.update (Function.update ℓ src (ℓ src - n)) dst (ℓ dst + n) := by
  simp only [prependN, lenBoundT]
  rw [lenBoundT_moveRev n h13 h14 h34 ℓ hℓ,
    lenBoundT_moveRev n (Ne.symm h23) h34 h24 _ (by simp [Ne.symm h14, Ne.symm h34, hℓ])]
  funext t
  simp only [Function.update_apply]
  by_cases ht1 : t = t₁ <;> by_cases ht2 : t = dst <;> by_cases ht3 : t = src <;>
    simp_all [Ne.symm h12, Ne.symm h13, Ne.symm h23]

end Exact

end SigabaNeo.Tape.Prog
