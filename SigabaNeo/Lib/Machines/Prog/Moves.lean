import SigabaNeo.Lib.Machines.Prog.FrameOut

/-!
# Moving bits between tapes

Counted loops (`forN c t body`: `|s t|` rounds, counter `c`) whose body moves bits between tapes,
with their laws (point masses):

* `law_forN_det`: a counted loop whose body acts deterministically on an abstract state;
* `moveP r S c t`: `r := r ++ take n S`, `S := drop n S` (`n = |s t|`, **`law_moveP`**);
* `dropP S c t`: `S := drop n S` (`law_dropP`);
* `zerosP r c t`: `r := r ++ replicate n false` (`law_zerosP`);
* `unframeP W D c t`: reads `n` framed data bits `[true, b]` off the front of `W` and appends the
  bits `b` to `D` (`law_unframeP`): on `W = u.flatMap (fun b => [true, b]) ++ rest` with
  `|u| = n`, `D := D ++ u`, `W := rest`.
-/

namespace SigabaNeo.Tape

open Cslib Cslib.Probability

variable {k : ℕ}

namespace XProg

/-- **A counted loop with a deterministic body** acting on an abstract state. -/
theorem law_forN_det {σ : Type} {c t : Fin k} (body : XProg k) (G : σ → Store k) (f : σ → σ)
    (hb : ∀ a w, body.law (Function.update (G a) c w) = PMF.pure (Function.update (G (f a)) c w))
    (a : σ) (s : Store k) (hs : Function.update s c (s t) = Function.update (G a) c (s t)) :
    (forN c t body).law s = PMF.pure (Function.update (G (f^[(s t).length] a)) c []) := by
  rw [forN, law_seq, law_prim, PMF.pure_bind]
  simp only [Prim.apply]
  rw [hs, law_loop_iter c body G (fun a => PMF.pure (f a)) (fun a w => by rw [hb, PMF.pure_map]),
    kIter_pure, PMF.pure_map]

theorem iterate_move : ∀ (n : ℕ) (o sv : List Bool),
    (fun p : List Bool × List Bool => (p.1 ++ p.2.take 1, p.2.tail))^[n] (o, sv) =
      (o ++ sv.take n, sv.drop n)
  | 0, o, sv => by simp
  | n + 1, o, sv => by
    rw [Function.iterate_succ_apply, iterate_move n]
    cases sv <;> simp [List.take_succ_cons]

/-! ### Moving bits -/

/-- **Move the first `|s t|` bits of `S` to the end of `r`** (counter `c`). -/
def moveP (r S c t : Fin k) : XProg k :=
  forN c t (seq (prog (.prim (.snocHead r S))) (prog (.prim (.tail S))))

theorem law_moveP {r S c t : Fin k} (hrS : r ≠ S) (hrc : r ≠ c) (hSc : S ≠ c) (hct : c ≠ t)
    (s : Store k) (hc : s c = []) :
    (moveP r S c t).law s = PMF.pure (Function.update (Function.update s r
      (s r ++ (s S).take (s t).length)) S ((s S).drop (s t).length)) := by
  let G : List Bool × List Bool → Store k := fun p => Function.update (Function.update s r p.1) S p.2
  rw [moveP, law_forN_det _ G (fun p => (p.1 ++ p.2.take 1, p.2.tail)) _ (s r, s S) s, iterate_move]
  · congr 1
    funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = c
    · subst h1; simp [hrc.symm, hSc.symm, hc]
    · simp [h1]
  · funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = r <;> by_cases h2 : l = S <;> by_cases h3 : l = c <;> simp_all
  · intro p w
    rw [law_seq, law_prim, PMF.pure_bind, law_prim]
    congr 1
    funext l
    obtain ⟨o, sv⟩ := p
    simp only [Prim.apply, G, Function.update_apply]
    by_cases h1 : l = r <;> by_cases h2 : l = S <;> by_cases h3 : l = c <;> simp_all

theorem wf_moveP {r S c t : Fin k} (hrc : r ≠ c) (hSc : S ≠ c) : (moveP r S c t).WF :=
  ⟨trivial, ⟨trivial, trivial⟩, by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hrc],
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hSc]⟩

/-- **Drop the first `|s t|` bits of `S`** (counter `c`). -/
def dropP (S c t : Fin k) : XProg k := forN c t (prog (.prim (.tail S)))

theorem iterate_tail : ∀ (n : ℕ) (sv : List Bool), (List.tail)^[n] sv = sv.drop n
  | 0, sv => by simp
  | n + 1, sv => by
    rw [Function.iterate_succ_apply, iterate_tail n]
    cases sv <;> simp

theorem law_dropP {S c t : Fin k} (hSc : S ≠ c) (hct : c ≠ t) (s : Store k) (hc : s c = []) :
    (dropP S c t).law s = PMF.pure (Function.update s S ((s S).drop (s t).length)) := by
  let G : List Bool → Store k := fun v => Function.update s S v
  rw [dropP, law_forN_det _ G List.tail _ (s S) s, iterate_tail]
  · congr 1
    funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = c
    · subst h1; simp [hSc.symm, hc]
    · simp [h1]
  · funext l
    simp only [G, Function.update_apply]
    by_cases h2 : l = S <;> by_cases h3 : l = c <;> simp_all
  · intro v w
    rw [law_prim]
    congr 1
    funext l
    simp only [Prim.apply, G, Function.update_apply]
    by_cases h2 : l = S <;> by_cases h3 : l = c <;> simp_all

theorem wf_dropP {S c t : Fin k} (hSc : S ≠ c) : (dropP S c t).WF :=
  ⟨trivial, trivial, by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hSc]⟩

/-- **Append `|s t|` zeros to `r`** (counter `c`). -/
def zerosP (r c t : Fin k) : XProg k := forN c t (prog (.prim (.snoc r false)))

theorem iterate_snoc : ∀ (n : ℕ) (o : List Bool),
    (fun o : List Bool => o ++ [false])^[n] o = o ++ List.replicate n false
  | 0, o => by simp
  | n + 1, o => by
    rw [Function.iterate_succ_apply, iterate_snoc n, List.replicate_succ]
    simp

theorem law_zerosP {r c t : Fin k} (hrc : r ≠ c) (hct : c ≠ t) (s : Store k) (hc : s c = []) :
    (zerosP r c t).law s =
      PMF.pure (Function.update s r (s r ++ List.replicate (s t).length false)) := by
  let G : List Bool → Store k := fun v => Function.update s r v
  rw [zerosP, law_forN_det _ G (fun o => o ++ [false]) _ (s r) s, iterate_snoc]
  · congr 1
    funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = c
    · subst h1; simp [hrc.symm, hc]
    · simp [h1]
  · funext l
    simp only [G, Function.update_apply]
    by_cases h2 : l = r <;> by_cases h3 : l = c <;> simp_all
  · intro v w
    rw [law_prim]
    congr 1
    funext l
    simp only [Prim.apply, G, Function.update_apply]
    by_cases h2 : l = r <;> by_cases h3 : l = c <;> simp_all

theorem wf_zerosP {r c t : Fin k} (hrc : r ≠ c) : (zerosP r c t).WF :=
  ⟨trivial, trivial, by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hrc]⟩

/-! ### Reading framed bits -/

/-- **Read `|s t|` framed data bits** off the front of `W` into `D` (counter `c`). -/
def unframeP (W D c t : Fin k) : XProg k :=
  forN c t (seq (prog (.prim (.tail W))) (seq (prog (.prim (.snocHead D W))) (prog (.prim (.tail W)))))

/-- One round: drop the marker, move the data bit, drop it. -/
def ufStep (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1 ++ p.2.tail.take 1, p.2.tail.tail)

theorem iterate_ufStep : ∀ (u rest o : List Bool),
    ufStep^[u.length] (o, u.flatMap (fun b => [true, b]) ++ rest) = (o ++ u, rest)
  | [], rest, o => by simp
  | b :: u, rest, o => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [ufStep, List.flatMap_cons, List.cons_append, List.tail_cons, List.nil_append,
      List.take_succ_cons, List.take_zero]
    rw [iterate_ufStep u rest (o ++ [b])]
    simp

theorem law_unframeP {W D c t : Fin k} (hWD : W ≠ D) (hWc : W ≠ c) (hDc : D ≠ c) (hct : c ≠ t)
    (s : Store k) (hc : s c = []) (u rest : List Bool)
    (hW : s W = u.flatMap (fun b => [true, b]) ++ rest) (hn : (s t).length = u.length) :
    (unframeP W D c t).law s =
      PMF.pure (Function.update (Function.update s D (s D ++ u)) W rest) := by
  let G : List Bool × List Bool → Store k := fun p => Function.update (Function.update s D p.1) W p.2
  rw [unframeP, law_forN_det _ G ufStep _ (s D, s W) s, hn, hW, iterate_ufStep]
  · congr 1
    funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = c
    · subst h1; simp [hWc.symm, hDc.symm, hc]
    · simp [h1]
  · funext l
    simp only [G, Function.update_apply]
    by_cases h1 : l = D <;> by_cases h2 : l = W <;> by_cases h3 : l = c <;> simp_all
  · intro p w
    rw [law_seq, law_prim, PMF.pure_bind, law_seq, law_prim, PMF.pure_bind, law_prim]
    congr 1
    funext l
    obtain ⟨o, sv⟩ := p
    simp only [Prim.apply, G, ufStep, Function.update_apply]
    by_cases h1 : l = D <;> by_cases h2 : l = W <;> by_cases h3 : l = c <;> simp_all

theorem wf_unframeP {W D c t : Fin k} (hWc : W ≠ c) (hDc : D ≠ c) : (unframeP W D c t).WF :=
  ⟨trivial, ⟨trivial, trivial, trivial⟩,
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hWc],
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hDc],
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hWc]⟩

end XProg

end SigabaNeo.Tape
