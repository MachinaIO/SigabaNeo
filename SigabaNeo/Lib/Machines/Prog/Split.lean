import SigabaNeo.Lib.Machines.Prog.Stream

/-!
# Splitting a word into three parts and joining three words, as tape programs

Programs of the fragment `NoGrow`: the lengths of the parts come from templates.

* `splitP : Prog 10` (`0` `1` `2` the parts, `3` the word `u`, `4` `5` `6` templates of lengths
  `a`, `b`, `c`; scratch `7 8 9`): `0 := takeD a u`, `1 := takeD b (u.drop a)`,
  `2 := takeD c (u.drop (a + b))` (`run_splitP`).
* `joinP : Prog 11` (`0` the output, `1` `2` `3` the words `A`, `B`, `C`, `4` `5` `6` templates of
  lengths `a`, `b`, `c`, `7` a template of length `a + b + c`; scratch `8 9 10`):
  `0 := takeD a A ++ takeD b B ++ takeD c C` (`run_joinP`).

With exact lengths the two are inverse (`takeD` is `take`, `takeD_of_length'`).
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

def spA : Fin 5 → Fin 10 := ![7, 0, 8, 9, 4]
def spB : Fin 5 → Fin 10 := ![7, 1, 8, 9, 5]
def spC : Fin 5 → Fin 10 := ![7, 2, 8, 9, 6]
theorem spA_inj : Function.Injective spA := by decide
theorem spB_inj : Function.Injective spB := by decide
theorem spC_inj : Function.Injective spC := by decide

/-- **Split** the word on tape `3` into parts of the lengths of the templates `4`, `5`, `6`. -/
def splitP : Prog 10 :=
  cp 7 3 ⨾ cp 0 4 ⨾ map spA mvP ⨾ cp 1 5 ⨾ map spB mvP ⨾ cp 2 6 ⨾ map spC mvP ⨾ clr 7

theorem drop_append_takeD {r : List Bool} {n : ℕ} (h : r.length = n) (w : List Bool) :
    (r ++ takeD n w).drop n = takeD n w := by
  subst h; simp

theorem run_splitP (s : Store 10) (h7 : s 7 = []) (h8 : s 8 = []) (h9 : s 9 = []) :
    run splitP s = Function.update (Function.update (Function.update s 0
      (takeD (s 4).length (s 3))) 1 (takeD (s 5).length ((s 3).drop (s 4).length))) 2
      (takeD (s 6).length ((s 3).drop ((s 4).length + (s 5).length))) := by
  simp only [splitP, run_seq, run_copy, run_clear]
  rw [run_mvP_map spA_inj _ (by simp [spA, spB, spC, h8]) (by simp [spA, spB, spC, h9])]
  rw [run_mvP_map spB_inj _ (by simp [spA, spB, spC, h8]) (by simp [spA, spB, spC, h9])]
  rw [run_mvP_map spC_inj _ (by simp [spA, spB, spC, h8]) (by simp [spA, spB, spC, h9])]
  funext t
  fin_cases t <;> simp [spA, spB, spC, h7, drop_append_takeD, List.drop_drop, Nat.add_comm]

theorem run_splitP_map {u : Fin 10 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h7 : s (u 7) = []) (h8 : s (u 8) = []) (h9 : s (u 9) = []) :
    run (map u splitP) s = Function.update (Function.update (Function.update s (u 0)
      (takeD (s (u 4)).length (s (u 3)))) (u 1)
        (takeD (s (u 5)).length ((s (u 3)).drop (s (u 4)).length))) (u 2)
      (takeD (s (u 6)).length ((s (u 3)).drop ((s (u 4)).length + (s (u 5)).length))) := by
  rw [run_map hu, run_splitP _ h7 h8 h9, extend_update hu, extend_update hu, extend_update hu,
    extend_comp_self]
  rfl

def jnA : Fin 5 → Fin 11 := ![8, 0, 9, 10, 4]
def jnB : Fin 5 → Fin 11 := ![8, 0, 9, 10, 5]
def jnC : Fin 5 → Fin 11 := ![8, 0, 9, 10, 6]
theorem jnA_inj : Function.Injective jnA := by decide
theorem jnB_inj : Function.Injective jnB := by decide
theorem jnC_inj : Function.Injective jnC := by decide

/-- **Join** prefixes of the words `1`, `2`, `3` of the lengths of the templates `4`, `5`, `6`. -/
def joinP : Prog 11 :=
  cp 0 7 ⨾ cp 8 1 ⨾ map jnA mvP ⨾ cp 8 2 ⨾ map jnB mvP ⨾ cp 8 3 ⨾ map jnC mvP ⨾ clr 8

theorem run_joinP (s : Store 11) (h8 : s 8 = []) (h9 : s 9 = []) (h10 : s 10 = [])
    (hV : (s 7).length = (s 4).length + (s 5).length + (s 6).length) :
    run joinP s = Function.update s 0 (takeD (s 4).length (s 1) ++
      takeD (s 5).length (s 2) ++ takeD (s 6).length (s 3)) := by
  simp only [joinP, run_seq, run_copy, run_clear]
  rw [run_mvP_map jnA_inj _ (by simp [jnA, jnB, jnC, h9]) (by simp [jnA, jnB, jnC, h10])]
  rw [run_mvP_map jnB_inj _ (by simp [jnA, jnB, jnC, h9]) (by simp [jnA, jnB, jnC, h10])]
  rw [run_mvP_map jnC_inj _ (by simp [jnA, jnB, jnC, h9]) (by simp [jnA, jnB, jnC, h10])]
  have key : (((s 7 ++ takeD (s 4).length (s 1)).drop (s 4).length ++
      takeD (s 5).length (s 2)).drop (s 5).length ++ takeD (s 6).length (s 3)).drop
        (s 6).length = takeD (s 4).length (s 1) ++ takeD (s 5).length (s 2) ++
          takeD (s 6).length (s 3) := by
    have e1 := drop_append_drop (s 7) (takeD (s 4).length (s 1)) (takeD (s 5).length (s 2))
    simp only [length_takeD] at e1
    rw [e1]
    have e2 := drop_append_drop (s 7) (takeD (s 4).length (s 1) ++ takeD (s 5).length (s 2))
      (takeD (s 6).length (s 3))
    simp only [length_takeD, List.length_append] at e2
    rw [e2, ← hV, List.drop_left' rfl, List.append_assoc]
  funext t
  fin_cases t <;> simp [jnA, jnB, jnC, h8, key]

theorem run_joinP_map {u : Fin 11 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h8 : s (u 8) = []) (h9 : s (u 9) = []) (h10 : s (u 10) = [])
    (hV : (s (u 7)).length = (s (u 4)).length + (s (u 5)).length + (s (u 6)).length) :
    run (map u joinP) s = Function.update s (u 0) (takeD (s (u 4)).length (s (u 1)) ++
      takeD (s (u 5)).length (s (u 2)) ++ takeD (s (u 6)).length (s (u 3))) :=
  run_map_eq_update hu _ s 0 _ (run_joinP _ h8 h9 h10 hV)

theorem noGrow_splitP : splitP.NoGrow := rfl
theorem noGrow_joinP : joinP.NoGrow := rfl
theorem wf_splitP : splitP.WF := wf_of_wfB (by decide)
theorem wf_joinP : joinP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
