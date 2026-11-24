import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMWF
import SigabaNeo.Lib.Machines.Prog.Sample

/-!
# Templates for the ring-word machine

A machine running `RingVM` code needs its constant words (templates `replicate n false` of many
lengths) on the register tapes before the code starts; they are built by doubling (`natP`, about
`log₂ n` states each). `tmplsP l` builds `replicate n false` on every tape `t` of the list `l` of
pairs `(t, n)` (counter tape `c`, blank before and after): **`law_tmplsP`**.
-/

namespace SigabaNeo.Tape

open XProg

variable {k : ℕ}

/-- `t := replicate n false` for every `(t, n)` of the list (counter tape `c`). -/
def tmplsP (c : Fin k) : List (Fin k × ℕ) → XProg k
  | [] => .prog (.prim (.copy c c))
  | p :: l => .seq (natP p.1 c p.2) (tmplsP c l)

/-- The store after the templates. -/
def tmplsS (l : List (Fin k × ℕ)) (s : Store k) : Store k :=
  l.foldl (fun s p => Function.update s p.1 (List.replicate p.2 false)) s

theorem law_tmplsP (c : Fin k) : ∀ (l : List (Fin k × ℕ)) (s : Store k), s c = [] →
    (∀ p ∈ l, p.1 ≠ c) → (tmplsP c l).law s = PMF.pure (tmplsS l s)
  | [], s, _, _ => by
    rw [tmplsP, law_prim]
    congr 1
    simp [Prim.apply, tmplsS]
  | p :: l, s, hc, hl => by
    have hp : p.1 ≠ c := hl p (by simp)
    rw [tmplsP, law_seq, law_natP hp.symm _ s hc, PMF.pure_bind,
      law_tmplsP c l _ (by rw [Function.update_of_ne hp.symm]; exact hc)
        (fun q hq => hl q (by simp [hq]))]
    rfl

theorem tmplsS_apply_of_not_mem (l : List (Fin k × ℕ)) (s : Store k) (t : Fin k)
    (h : ∀ p ∈ l, p.1 ≠ t) : tmplsS l s t = s t := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    simp only [tmplsS, List.foldl_cons]
    rw [show l.foldl _ _ = tmplsS l _ from rfl, ih _ (fun q hq => h q (by simp [hq])),
      Function.update_of_ne (h p (by simp)).symm]

theorem tmplsS_apply_of_mem (l : List (Fin k × ℕ)) (s : Store k) (t : Fin k) (n : ℕ)
    (hm : (t, n) ∈ l) (hu : ∀ p ∈ l, p.1 = t → p.2 = n) :
    tmplsS l s t = List.replicate n false := by
  induction l generalizing s with
  | nil => simp at hm
  | cons p l ih =>
    simp only [tmplsS, List.foldl_cons]
    rw [show l.foldl _ _ = tmplsS l _ from rfl]
    by_cases hl : ∃ q ∈ l, q.1 = t
    · obtain ⟨q, hq, hqt⟩ := hl
      have hq2 := hu q (by simp [hq]) hqt
      exact ih _ (by rw [← hqt, ← hq2]; exact hq) (fun r hr => hu r (by simp [hr]))
    · push_neg at hl
      rw [tmplsS_apply_of_not_mem l _ t hl]
      rcases List.mem_cons.mp hm with h | h
      · subst h; simp
      · exact absurd rfl (hl _ h)

end SigabaNeo.Tape
