import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.VMDot

/-!
# Splitting the words of `sk` and `ct` into their fields (ring-word machine)

`splitC` cuts the word of `sk = mpk ++ k_F` (register `76`) into `B` (both rows, then row `2`
only, register `58`), `H` (`59`), `a` (`60`), `A₀` (`61`), `A^in` (`62`), `A^aut` (`63`), `d` (`64`),
the key (`65`), and the word of `ct` (register `77`) into `b` (`66`), `h` (`67`), `c^aut` (`68`), the
bottom rows of `C^in` (`69`), `c^in` (`70`), `c₀` (`71`), `c_m` (`72`), each field by one pop of the
width of its template (`exec_splitC`).
-/

namespace SigabaNeo.Tape

namespace RingVM

variable {N K : ℕ}

/-- Pop a field of the width of the template `t` from the stream `s` into `d`. -/
def popC (d s t : Fin 200) : Code := ofList [.cp d t, .mv d s t]

theorem exec_popC {d s t : Fin 200} (h : ¬(d = s ∨ d = t ∨ s = t)) (w : St) {v L : List Bool}
    (hv : v.length = (w t).length) (hs : w s = v ++ L) :
    exec N K (popC d s t) w = Function.update (Function.update (Function.update w d (w t)) s L) d v := by
  have hdt : d ≠ t := fun e => h (Or.inr (Or.inl e))
  have hds : d ≠ s := fun e => h (Or.inl e)
  have hst : s ≠ t := fun e => h (Or.inr (Or.inr e))
  show exec N K (.mv d s t) (Function.update w d (w t)) = _
  have e := exec_mv_pop (N := N) (K := K) (w := Function.update w d (w t)) (v := v) (L := L) h
    (by rw [Function.update_self, Function.update_of_ne hdt.symm])
    (by rw [Function.update_of_ne hdt.symm]; exact hv)
    (by rw [Function.update_of_ne hds.symm]; exact hs)
  rw [e]

/-- **The fields of `ct`** (register `77`; templates `16` (`b`), `19` (`h`), `186` (`c^aut`),
`182` (bottom rows), `187` (`c^in`), `6` (`c₀`)). -/
def splitCtC : Code := ofList [popC 66 77 16, popC 67 77 19, popC 68 77 186, popC 69 77 182,
  popC 70 77 187, popC 71 77 6, .cp 72 77]

/-- **The fields of `sk`** (register `76`; templates `180` (`B`), `181` (`H`), `182` (`a`), `7`
(`A₀`), `183` (`A^in`), `184` (`A^aut`), `185` (`d`)), then the second row of `B` (drop `|16|`). -/
def splitSkC : Code := ofList [popC 58 76 180, popC 59 76 181, popC 60 76 182, popC 61 76 7,
  popC 62 76 183, popC 63 76 184, popC 64 76 185, .cp 65 76, .drop 58 16]

theorem popC_facts {d s t : Fin 200} (h : ¬(d = s ∨ d = t ∨ s = t)) (w : St) {v L : List Bool}
    (hv : v.length = (w t).length) (hs : w s = v ++ L) :
    (exec N K (popC d s t) w) d = v ∧ (exec N K (popC d s t) w) s = L ∧
      ∀ j, j ≠ d → j ≠ s → (exec N K (popC d s t) w) j = w j := by
  rw [exec_popC h w hv hs]
  have hds : d ≠ s := fun e => h (Or.inl e)
  refine ⟨by simp, by rw [Function.update_of_ne hds.symm]; simp, fun j h1 h2 => ?_⟩
  rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h1]

theorem exec_splitCtC (w : St) {gb gh gca gcb gci gc0 gcm : List Bool}
    (h77 : w 77 = gb ++ (gh ++ (gca ++ (gcb ++ (gci ++ (gc0 ++ gcm))))))
    (l1 : gb.length = (w 16).length) (l2 : gh.length = (w 19).length)
    (l3 : gca.length = (w 186).length) (l4 : gcb.length = (w 182).length)
    (l5 : gci.length = (w 187).length) (l6 : gc0.length = (w 6).length) :
    (exec N K splitCtC w) 66 = gb ∧ (exec N K splitCtC w) 67 = gh ∧ (exec N K splitCtC w) 68 = gca ∧
      (exec N K splitCtC w) 69 = gcb ∧ (exec N K splitCtC w) 70 = gci ∧
      (exec N K splitCtC w) 71 = gc0 ∧ (exec N K splitCtC w) 72 = gcm ∧
      ∀ j : Fin 200, j.val < 66 ∨ 77 < j.val → (exec N K splitCtC w) j = w j := by
  have ne : ∀ (j a : Fin 200), j.val < 66 ∨ 77 < j.val → 66 ≤ a.val → a.val ≤ 77 →
      j ≠ a := fun j a hj h1 h2 e => by subst e; omega
  obtain ⟨a1, b1, c1⟩ := popC_facts (N := N) (K := K) (d := 66) (s := 77) (t := 16) (by decide) w l1 h77
  set u1 := exec N K (popC 66 77 16) w
  obtain ⟨a2, b2, c2⟩ := popC_facts (N := N) (K := K) (d := 67) (s := 77) (t := 19) (by decide) u1
    (by rw [c1 19 (by decide) (by decide)]; exact l2) b1
  set u2 := exec N K (popC 67 77 19) u1
  obtain ⟨a3, b3, c3⟩ := popC_facts (N := N) (K := K) (d := 68) (s := 77) (t := 186) (by decide) u2
    (by rw [c2 186 (by decide) (by decide), c1 186 (by decide) (by decide)]; exact l3) b2
  set u3 := exec N K (popC 68 77 186) u2
  obtain ⟨a4, b4, c4⟩ := popC_facts (N := N) (K := K) (d := 69) (s := 77) (t := 182) (by decide) u3
    (by rw [c3 182 (by decide) (by decide), c2 182 (by decide) (by decide),
      c1 182 (by decide) (by decide)]; exact l4) b3
  set u4 := exec N K (popC 69 77 182) u3
  obtain ⟨a5, b5, c5⟩ := popC_facts (N := N) (K := K) (d := 70) (s := 77) (t := 187) (by decide) u4
    (by rw [c4 187 (by decide) (by decide), c3 187 (by decide) (by decide),
      c2 187 (by decide) (by decide), c1 187 (by decide) (by decide)]; exact l5) b4
  set u5 := exec N K (popC 70 77 187) u4
  obtain ⟨a6, b6, c6⟩ := popC_facts (N := N) (K := K) (d := 71) (s := 77) (t := 6) (by decide) u5
    (by rw [c5 6 (by decide) (by decide), c4 6 (by decide) (by decide), c3 6 (by decide) (by decide),
      c2 6 (by decide) (by decide), c1 6 (by decide) (by decide)]; exact l6) b5
  set u6 := exec N K (popC 71 77 6) u5
  have e : exec N K splitCtC w = Function.update u6 72 (u6 77) := rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [b6], fun j hj => ?_⟩
  · rw [Function.update_of_ne (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      c4 _ (by decide) (by decide), c3 _ (by decide) (by decide), c2 _ (by decide) (by decide), a1]
  · rw [Function.update_of_ne (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      c4 _ (by decide) (by decide), c3 _ (by decide) (by decide), a2]
  · rw [Function.update_of_ne (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      c4 _ (by decide) (by decide), a3]
  · rw [Function.update_of_ne (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      a4]
  · rw [Function.update_of_ne (by decide), c6 _ (by decide) (by decide), a5]
  · rw [Function.update_of_ne (by decide), a6]
  · rw [Function.update_of_ne (ne j 72 hj (by decide) (by decide)),
      c6 j (ne j 71 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide)),
      c5 j (ne j 70 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide)),
      c4 j (ne j 69 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide)),
      c3 j (ne j 68 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide)),
      c2 j (ne j 67 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide)),
      c1 j (ne j 66 hj (by decide) (by decide)) (ne j 77 hj (by decide) (by decide))]

theorem exec_splitSkC (w : St) {fB0 fB1 fH fa fA0 fAin fAaut fd fk : List Bool}
    (h76 : w 76 = (fB0 ++ fB1) ++ (fH ++ (fa ++ (fA0 ++ (fAin ++ (fAaut ++ (fd ++ fk)))))))
    (l0 : (fB0 ++ fB1).length = (w 180).length) (l0' : fB0.length = (w 16).length)
    (l1 : fH.length = (w 181).length) (l2 : fa.length = (w 182).length)
    (l3 : fA0.length = (w 7).length) (l4 : fAin.length = (w 183).length)
    (l5 : fAaut.length = (w 184).length) (l6 : fd.length = (w 185).length) :
    (exec N K splitSkC w) 58 = fB1 ∧ (exec N K splitSkC w) 59 = fH ∧ (exec N K splitSkC w) 60 = fa ∧
      (exec N K splitSkC w) 61 = fA0 ∧ (exec N K splitSkC w) 62 = fAin ∧
      (exec N K splitSkC w) 63 = fAaut ∧ (exec N K splitSkC w) 64 = fd ∧
      (exec N K splitSkC w) 65 = fk ∧
      ∀ j : Fin 200, j.val < 58 ∨ 76 < j.val → (exec N K splitSkC w) j = w j := by
  have ne : ∀ (j a : Fin 200), j.val < 58 ∨ 76 < j.val → 58 ≤ a.val → a.val ≤ 76 →
      j ≠ a := fun j a hj h1 h2 e => by subst e; omega
  obtain ⟨a1, b1, c1⟩ := popC_facts (N := N) (K := K) (d := 58) (s := 76) (t := 180) (by decide) w l0 h76
  set u1 := exec N K (popC 58 76 180) w
  obtain ⟨a2, b2, c2⟩ := popC_facts (N := N) (K := K) (d := 59) (s := 76) (t := 181) (by decide) u1
    (by rw [c1 181 (by decide) (by decide)]; exact l1) b1
  set u2 := exec N K (popC 59 76 181) u1
  obtain ⟨a3, b3, c3⟩ := popC_facts (N := N) (K := K) (d := 60) (s := 76) (t := 182) (by decide) u2
    (by rw [c2 182 (by decide) (by decide), c1 182 (by decide) (by decide)]; exact l2) b2
  set u3 := exec N K (popC 60 76 182) u2
  obtain ⟨a4, b4, c4⟩ := popC_facts (N := N) (K := K) (d := 61) (s := 76) (t := 7) (by decide) u3
    (by rw [c3 7 (by decide) (by decide), c2 7 (by decide) (by decide),
      c1 7 (by decide) (by decide)]; exact l3) b3
  set u4 := exec N K (popC 61 76 7) u3
  obtain ⟨a5, b5, c5⟩ := popC_facts (N := N) (K := K) (d := 62) (s := 76) (t := 183) (by decide) u4
    (by rw [c4 183 (by decide) (by decide), c3 183 (by decide) (by decide),
      c2 183 (by decide) (by decide), c1 183 (by decide) (by decide)]; exact l4) b4
  set u5 := exec N K (popC 62 76 183) u4
  obtain ⟨a6, b6, c6⟩ := popC_facts (N := N) (K := K) (d := 63) (s := 76) (t := 184) (by decide) u5
    (by rw [c5 184 (by decide) (by decide), c4 184 (by decide) (by decide),
      c3 184 (by decide) (by decide), c2 184 (by decide) (by decide),
      c1 184 (by decide) (by decide)]; exact l5) b5
  set u6 := exec N K (popC 63 76 184) u5
  obtain ⟨a7, b7, c7⟩ := popC_facts (N := N) (K := K) (d := 64) (s := 76) (t := 185) (by decide) u6
    (by rw [c6 185 (by decide) (by decide), c5 185 (by decide) (by decide),
      c4 185 (by decide) (by decide), c3 185 (by decide) (by decide), c2 185 (by decide) (by decide),
      c1 185 (by decide) (by decide)]; exact l6) b6
  set u7 := exec N K (popC 64 76 185) u6
  have h16 : u7 16 = w 16 := by
    rw [c7 16 (by decide) (by decide), c6 16 (by decide) (by decide), c5 16 (by decide) (by decide),
      c4 16 (by decide) (by decide), c3 16 (by decide) (by decide), c2 16 (by decide) (by decide),
      c1 16 (by decide) (by decide)]
  have h58 : u7 58 = fB0 ++ fB1 := by
    rw [c7 58 (by decide) (by decide), c6 58 (by decide) (by decide), c5 58 (by decide) (by decide),
      c4 58 (by decide) (by decide), c3 58 (by decide) (by decide), c2 58 (by decide) (by decide), a1]
  have e : exec N K splitSkC w = Function.update (Function.update u7 65 (u7 76)) 58
      ((Function.update u7 65 (u7 76) 58).drop (Function.update u7 65 (u7 76) 16).length) := by
    show exec N K (.drop 58 16) (exec N K (.cp 65 76) u7) = _
    simp only [exec, show ¬((58 : Fin 200) = 16) by decide, ↓reduceIte]
  rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [Function.update_self, Function.update_of_ne (show (58 : Fin 200) ≠ 65 by decide),
      Function.update_of_ne (show (16 : Fin 200) ≠ 65 by decide), h58, h16]
    rw [List.drop_left' l0']
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      c7 _ (by decide) (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      c4 _ (by decide) (by decide), c3 _ (by decide) (by decide), a2]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      c7 _ (by decide) (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide),
      c4 _ (by decide) (by decide), a3]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      c7 _ (by decide) (by decide), c6 _ (by decide) (by decide), c5 _ (by decide) (by decide), a4]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      c7 _ (by decide) (by decide), c6 _ (by decide) (by decide), a5]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      c7 _ (by decide) (by decide), a6]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), a7]
  · rw [Function.update_of_ne (by decide), Function.update_self, b7]
  · rw [Function.update_of_ne (ne j 58 hj (by decide) (by decide)),
      Function.update_of_ne (ne j 65 hj (by decide) (by decide)),
      c7 j (ne j 64 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c6 j (ne j 63 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c5 j (ne j 62 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c4 j (ne j 61 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c3 j (ne j 60 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c2 j (ne j 59 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide)),
      c1 j (ne j 58 hj (by decide) (by decide)) (ne j 76 hj (by decide) (by decide))]

end RingVM

end SigabaNeo.Tape
