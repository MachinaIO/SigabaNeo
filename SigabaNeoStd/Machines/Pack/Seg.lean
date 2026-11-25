import SigabaNeoStd.Machines.Prog.Pass

/-!
# A store of words as one word, and the transducers that cut it

A logical store `S : Fin K → List Bool` is kept on one physical tape as the concatenation of the
frames of its words, `pkW S = frame (S 0) ++ … ++ frame (S (K-1))` (`frame u`: every bit `b` as
`[true, b]`, then `[false]`). The segment `j` is read and replaced by finite-state transducers
(cslib-frontier's `Turing.MultiTapeTM.Transducer`), which run in linear time on a tape
(`SigabaNeo.Tape.trPhase`):

* `getT j`: emits the word of frame `j` (`run_getT_pkW : (getT j).run _ (pkW S) = S j`);
* `preT j`, `sufT j`: emit the frames before / after the frame `j`, verbatim;
* `frT`: emits `frame u` on `u`.

`putW j u E = preT j (E) ++ frame u ++ sufT j (E)`, and **`putW_pkW`**:
`putW j u (pkW S) = pkW (update S j u)`.
-/

namespace SigabaNeo.Tape.Pack

open Turing Turing.MultiTapeTM

/-! ### The packed store -/

/-- The concatenation of the frames of a list of words. -/
def pkL (l : List (List Bool)) : List Bool := l.flatMap MultiTapeTM.frame

/-- **The packed store**: the frames of the words of a store, in order. -/
def pkW {K : ℕ} (S : Store K) : List Bool := pkL (List.ofFn S)

theorem pkL_nil : pkL [] = [] := rfl

theorem pkL_cons (u : List Bool) (l : List (List Bool)) :
    pkL (u :: l) = MultiTapeTM.frame u ++ pkL l := by simp [pkL]

theorem pkL_append (l l' : List (List Bool)) : pkL (l ++ l') = pkL l ++ pkL l' := by
  simp [pkL]

theorem length_frame' (u : List Bool) : (MultiTapeTM.frame u).length = 2 * u.length + 1 := by
  simp only [MultiTapeTM.frame, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil, List.length_singleton]
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem length_pkL (l : List (List Bool)) :
    (pkL l).length = (l.map fun u => 2 * u.length + 1).sum := by
  induction l with
  | nil => rfl
  | cons u l ih => rw [pkL_cons, List.length_append, length_frame', ih]; simp

/-- The length of the packed store: `Σ (2 |S i| + 1)`. -/
theorem length_pkW {K : ℕ} (S : Store K) :
    (pkW S).length = ∑ i, (2 * (S i).length + 1) := by
  rw [pkW, length_pkL, List.map_ofFn, List.sum_ofFn]
  rfl

theorem ofFn_update {K : ℕ} (S : Store K) (j : Fin K) (u : List Bool) :
    List.ofFn (Function.update S j u) = (List.ofFn S).set j u := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_set]
    by_cases h : (j : ℕ) = n
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne (fun h' => h (by rw [← h']))]

/-! ### Segment transducers -/

/-- The successor of a frame counter, capped at `j + 1`. -/
def capS (j : ℕ) (n : Fin (j + 2)) : Fin (j + 2) := ⟨min (n + 1) (j + 1), by omega⟩

/-- The emission of a symbol `a`, when `e n d a` holds (`n` the index of the current frame, `d`
whether `a` is a data bit). -/
def outE (e : ℕ → Bool → Bool → Bool) (n : ℕ) (d a : Bool) : List Bool :=
  if e n d a then [a] else []

theorem length_outE_le (e : ℕ → Bool → Bool → Bool) (n : ℕ) (d a : Bool) :
    (outE e n d a).length ≤ 2 := by
  unfold outE; split <;> simp

/-- The step of a segment transducer: the state is the index of the current frame (capped at
`j + 1`) and whether the next symbol is a data bit. -/
def segStep (j : ℕ) (e : ℕ → Bool → Bool → Bool) :
    Fin (j + 2) × Bool → Bool → (Fin (j + 2) × Bool) × List Bool
  | (n, true), a => ((n, false), outE e n true a)
  | (n, false), true => ((n, true), outE e n false true)
  | (n, false), false => ((capS j n, false), outE e n false false)

/-- A segment transducer, emitting the symbols selected by `e`. -/
def segT (j : ℕ) (e : ℕ → Bool → Bool → Bool) : Transducer Bool (Fin (j + 2) × Bool) where
  q₀ := (0, false)
  step := segStep j e
  final _ := []
  length_step_le q a := by
    obtain ⟨n, d⟩ := q
    cases d <;> cases a <;> simp only [segStep] <;> exact length_outE_le _ _ _ _
  length_final_le _ := by simp

/-- What a segment transducer emits on one frame. -/
def frameOut (e : ℕ → Bool → Bool → Bool) (n : ℕ) (u : List Bool) : List Bool :=
  u.flatMap (fun b => outE e n false true ++ outE e n true b) ++ outE e n false false

theorem segT_step_true (j : ℕ) (e : ℕ → Bool → Bool → Bool) (n : Fin (j + 2)) (a : Bool) :
    (segT j e).step (n, true) a = ((n, false), outE e n true a) := rfl

theorem segT_step_false_true (j : ℕ) (e : ℕ → Bool → Bool → Bool) (n : Fin (j + 2)) :
    (segT j e).step (n, false) true = ((n, true), outE e n false true) := rfl

theorem segT_step_false_false (j : ℕ) (e : ℕ → Bool → Bool → Bool) (n : Fin (j + 2)) :
    (segT j e).step (n, false) false = ((capS j n, false), outE e n false false) := rfl

theorem segT_run_nil (j : ℕ) (e : ℕ → Bool → Bool → Bool) (q : Fin (j + 2) × Bool) :
    (segT j e).run q [] = [] := rfl

theorem segT_final (j : ℕ) (e : ℕ → Bool → Bool → Bool) (q : Fin (j + 2) × Bool) :
    (segT j e).final q = [] := rfl

theorem run_segT_frame (j : ℕ) (e : ℕ → Bool → Bool → Bool) (n : Fin (j + 2)) (u r : List Bool) :
    (segT j e).run (n, false) (MultiTapeTM.frame u ++ r) =
      frameOut e n u ++ (segT j e).run (capS j n, false) r := by
  induction u with
  | nil =>
    show (segT j e).run (n, false) (false :: r) = _
    rw [Transducer.run_cons, segT_step_false_false]
    simp [frameOut]
  | cons b u ih =>
    have hf : MultiTapeTM.frame (b :: u) ++ r = true :: b :: (MultiTapeTM.frame u ++ r) := by
      simp [MultiTapeTM.frame]
    rw [hf, Transducer.run_cons, segT_step_false_true, Transducer.run_cons, segT_step_true]
    simp only
    rw [ih]
    simp [frameOut, List.append_assoc]

/-! ### Reading a segment -/

/-- Emits the data bits of the frame `j`. -/
def getT (j : ℕ) := segT j (fun n d _ => d && decide (n = j))

theorem frameOut_get (j n : ℕ) (u : List Bool) :
    frameOut (fun n d _ => d && decide (n = j)) n u = if n = j then u else [] := by
  induction u with
  | nil => simp [frameOut, outE]
  | cons b u ih =>
    simp only [frameOut, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [ih]
    by_cases h : n = j <;> simp [outE, h]

theorem run_getT (j : ℕ) : ∀ (l : List (List Bool)) (n : Fin (j + 2)),
    (getT j).run (n, false) (pkL l) = if (n : ℕ) ≤ j then l.getD (j - n) [] else []
  | [], n => by rw [pkL_nil]; simp [getT, segT_final]
  | u :: l, n => by
    rw [pkL_cons]
    show (segT j _).run (n, false) _ = _
    rw [run_segT_frame, frameOut_get]
    have ih := run_getT j l (capS j n)
    simp only [getT] at ih
    rw [ih]
    simp only [capS]
    have hn := n.isLt
    rcases Nat.lt_trichotomy (n : ℕ) j with h | h | h
    · have e1 : min ((n : ℕ) + 1) (j + 1) = n + 1 := by omega
      have e2 : j - (n : ℕ) = (j - (n + 1)) + 1 := by omega
      simp [e1, e2, show (n : ℕ) ≠ j by omega, show (n : ℕ) + 1 ≤ j by omega,
        show (n : ℕ) ≤ j by omega]
    · simp [h]
    · have e1 : min ((n : ℕ) + 1) (j + 1) = j + 1 := by omega
      simp [e1, show (n : ℕ) ≠ j by omega, show ¬ (n : ℕ) ≤ j by omega]

/-- **Reading a segment.** -/
theorem run_getT_pkW {K : ℕ} (S : Store K) (j : Fin K) :
    (getT j).run (getT j).q₀ (pkW S) = S j := by
  show (getT j).run (0, false) _ = _
  rw [pkW, run_getT]
  simp

/-! ### The frames before and after a segment -/

/-- Emits the frames before the frame `j`, verbatim. -/
def preT (j : ℕ) := segT j (fun n _ _ => decide (n < j))

/-- Emits the frames after the frame `j`, verbatim. -/
def sufT (j : ℕ) := segT j (fun n _ _ => decide (j < n))

theorem frameOut_const (e : ℕ → Bool → Bool → Bool) (P : Prop) [Decidable P] (n : ℕ)
    (he : ∀ d a, e n d a = decide P) (u : List Bool) :
    frameOut e n u = if P then MultiTapeTM.frame u else [] := by
  induction u with
  | nil => by_cases h : P <;> simp [frameOut, outE, he, h, MultiTapeTM.frame]
  | cons b u ih =>
    simp only [frameOut, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [ih]
    by_cases h : P <;> simp [outE, he, h, MultiTapeTM.frame]

theorem run_preT (j : ℕ) : ∀ (l : List (List Bool)) (n : Fin (j + 2)),
    (preT j).run (n, false) (pkL l) = pkL (l.take (j - n))
  | [], n => by rw [pkL_nil]; simp [preT, segT_final, pkL_nil]
  | u :: l, n => by
    rw [pkL_cons]
    show (segT j _).run (n, false) _ = _
    rw [run_segT_frame]
    have hf := frameOut_const (fun n _ _ => decide (n < j)) ((n : ℕ) < j) n (fun _ _ => rfl) u
    rw [hf]
    have ih := run_preT j l (capS j n)
    simp only [preT] at ih
    rw [ih]
    simp only [capS]
    have hn := n.isLt
    by_cases h : (n : ℕ) < j
    · rw [if_pos h, show j - (n : ℕ) = (j - min ((n : ℕ) + 1) (j + 1)) + 1 by omega,
        List.take_succ_cons, pkL_cons]
    · rw [if_neg h, show j - (n : ℕ) = 0 by omega, show j - min ((n : ℕ) + 1) (j + 1) = 0 by omega]
      simp [pkL]

theorem run_sufT (j : ℕ) : ∀ (l : List (List Bool)) (n : Fin (j + 2)),
    (sufT j).run (n, false) (pkL l) = pkL (l.drop (j + 1 - n))
  | [], n => by rw [pkL_nil]; simp [sufT, segT_final, pkL_nil]
  | u :: l, n => by
    rw [pkL_cons]
    show (segT j _).run (n, false) _ = _
    rw [run_segT_frame]
    have hf := frameOut_const (fun n _ _ => decide (j < n)) (j < (n : ℕ)) n (fun _ _ => rfl) u
    rw [hf]
    have ih := run_sufT j l (capS j n)
    simp only [sufT] at ih
    rw [ih]
    simp only [capS]
    have hn := n.isLt
    by_cases h : j < (n : ℕ)
    · rw [if_pos h, show j + 1 - (n : ℕ) = 0 by omega,
        show j + 1 - min ((n : ℕ) + 1) (j + 1) = 0 by omega]
      simp [pkL_cons]
    · rw [if_neg h, show j + 1 - (n : ℕ) = (j + 1 - min ((n : ℕ) + 1) (j + 1)) + 1 by omega,
        List.drop_succ_cons, List.nil_append]

/-- Emits the frame of its input. -/
def frT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := [false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem run_frT : ∀ u : List Bool, frT.run () u = MultiTapeTM.frame u
  | [] => rfl
  | b :: u => by
    rw [Transducer.run_cons, run_frT u]
    simp [frT, MultiTapeTM.frame]

/-! ### Replacing a segment -/

/-- The word with the frame `j` of `E` replaced by `frame u`. -/
def putW (j : ℕ) (u E : List Bool) : List Bool :=
  (preT j).run (preT j).q₀ E ++ MultiTapeTM.frame u ++ (sufT j).run (sufT j).q₀ E

theorem putW_pkL (j : ℕ) (u : List Bool) (l : List (List Bool)) (hj : j < l.length) :
    putW j u (pkL l) = pkL (l.set j u) := by
  show (preT j).run (0, false) _ ++ _ ++ (sufT j).run (0, false) _ = _
  rw [run_preT, run_sufT]
  simp only [Fin.val_zero, Nat.sub_zero]
  rw [List.set_eq_take_append_cons_drop, if_pos hj, pkL_append, pkL_cons, List.append_assoc]

/-- **Replacing a segment.** -/
theorem putW_pkW {K : ℕ} (S : Store K) (j : Fin K) (u : List Bool) :
    putW j u (pkW S) = pkW (Function.update S j u) := by
  rw [pkW, putW_pkL _ _ _ (by simp), ← ofFn_update]
  rfl

theorem length_outE_le_one (e : ℕ → Bool → Bool → Bool) (n : ℕ) (d a : Bool) :
    (outE e n d a).length ≤ 1 := by
  unfold outE; split <;> simp

/-- A segment transducer emits at most one symbol per symbol read. -/
theorem length_run_segT_le (j : ℕ) (e : ℕ → Bool → Bool → Bool) :
    ∀ (E : List Bool) (q : Fin (j + 2) × Bool), ((segT j e).run q E).length ≤ E.length
  | [], q => by simp [Transducer.run_nil, segT]
  | a :: E, ⟨n, d⟩ => by
    rw [Transducer.run_cons, List.length_append, List.length_cons]
    have ih := length_run_segT_le j e E ((segT j e).step (n, d) a).1
    have h1 : ((segT j e).step (n, d) a).2.length ≤ 1 := by
      cases d <;> cases a <;> simp only [segT, segStep] <;> exact length_outE_le_one _ _ _ _
    omega

end SigabaNeo.Tape.Pack
