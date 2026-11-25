import SigabaNeoStd.Machines.Prog.Sample
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic

/-!
# Writing framed words

cslib's tuple encoding (`encodeTuple`, `Turing.MultiTapeTM.encList`) is the concatenation of the
frames `frame u = u.flatMap (fun b => [true, b]) ++ [false]` of its fields. A machine whose output
is a tuple writes the frames of its fields one after the other:

* `frameApP r a S c : XProg k` appends `frame (s a)` to the tape `r` (scratch stream `S`, counter
  `c`), leaving the tape `a` alone (**`law_frameApP`**): `|s a|` rounds of `snoc r true`, then the
  head bit of the stream, then the end marker `false`;
* `wf_frameApP`.
-/

namespace SigabaNeo.Tape

open Cslib Cslib.Probability

variable {k : ℕ}

namespace XProg

/-- **Append the frame of tape `a` to tape `r`** (scratch stream `S`, counter `c`). -/
def frameApP (r a S c : Fin k) : XProg k :=
  seq (prog (.prim (.copy S a)))
    (seq (forN c a (seq (prog (.prim (.snoc r true)))
        (seq (prog (.prim (.snocHead r S))) (prog (.prim (.tail S))))))
      (seq (prog (.prim (.snoc r false))) (prog (.prim (.clear S)))))

/-- One step of the transfer: the marker `true`, then the head bit of the stream. -/
def frStep : List Bool × List Bool → List Bool × List Bool
  | (o, sv) => (o ++ (true :: sv.take 1), sv.tail)

theorem frStep_iter : ∀ (sv o : List Bool),
    frStep^[sv.length] (o, sv) = (o ++ sv.flatMap (fun b => [true, b]), [])
  | [], o => by simp
  | b :: sv, o => by
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [frStep, List.take_succ_cons, List.take_zero, List.tail_cons]
    rw [frStep_iter sv (o ++ [true, b])]
    simp

/-- **The law of `frameApP`**: `r := r ++ frame (s a)`, everything else unchanged. -/
theorem law_frameApP {r a S c : Fin k} (hra : r ≠ a) (hrS : r ≠ S) (hrc : r ≠ c) (haS : a ≠ S)
    (hac : a ≠ c) (hSc : S ≠ c) (s : Store k) (hS : s S = []) (hc : s c = []) :
    (frameApP r a S c).law s =
      PMF.pure (Function.update s r (s r ++ Turing.MultiTapeTM.frame (s a))) := by
  rw [frameApP, law_seq, law_prim, PMF.pure_bind, forN, law_seq, law_seq, law_prim,
    PMF.pure_bind]
  simp only [Prim.apply]
  let G : List Bool × List Bool → Store k := fun p =>
    Function.update (Function.update (Function.update s S (s a)) r p.1) S p.2
  have hstart : Function.update (Function.update s S (s a)) c
      (Function.update s S (s a) a) = Function.update (G (s r, s a)) c (s a) := by
    funext t
    simp only [G, Function.update_apply]
    by_cases h1 : t = a <;> by_cases h2 : t = S <;> by_cases h3 : t = r <;> by_cases h4 : t = c <;>
      simp_all
  rw [hstart, law_loop_iter c _ G (fun p => PMF.pure (frStep p))]
  · rw [kIter_pure, frStep_iter, PMF.pure_map, PMF.pure_bind, law_seq, law_prim, PMF.pure_bind,
      law_prim]
    congr 1
    funext t
    simp only [Prim.apply, G, Function.update_apply, Turing.MultiTapeTM.frame]
    by_cases h1 : t = a <;> by_cases h2 : t = S <;> by_cases h3 : t = r <;> by_cases h4 : t = c <;>
      simp_all
  · intro p w
    rw [law_seq, law_prim, PMF.pure_bind, law_seq, law_prim, PMF.pure_bind, law_prim, PMF.pure_map]
    congr 1
    funext t
    obtain ⟨o, sv⟩ := p
    have hSr : S ≠ r := Ne.symm hrS
    simp only [Prim.apply, G, frStep, Function.update_apply, hSr, ite_false]
    by_cases h1 : t = a <;> by_cases h2 : t = S <;> by_cases h3 : t = r <;> by_cases h4 : t = c <;>
      simp_all

theorem wf_frameApP {r a S c : Fin k} (hrc : r ≠ c) (hSc : S ≠ c) :
    (frameApP r a S c).WF :=
  ⟨trivial, ⟨trivial, ⟨trivial, trivial, trivial⟩,
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hrc],
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hrc],
    by simp [Preserves, Prog.Preserves, Prim.writes, Ne.symm hSc]⟩, trivial, trivial⟩

end XProg

end SigabaNeo.Tape
