import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenRep

/-!
# Generating gate tapes: one term of an output coefficient

`termStepC`: the register code of `termStep` — the indices of the two operands in the lists of
the representations (`10` for `repA`, `11` for `repB`), the AND of the coefficient by the digit,
then the modular subtraction or addition into the running sum.

Registers: `2 = k`, `5 = N`, `6 = 2`, `7 = 0` (constants), `43 … 46` the output position
`(a, (c1, c2), t)`, `47 … 49` the term `((r, e12), e2)`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {E : Env}

/-- The index phase: `36 :=` the digit `repB (r, (c1, c2), e12, e2)`, `17 :=` the coefficient
`repA (a, (r, e12), ·, j')`. -/
def tsIdxC : Code :=
  .seq (.mov 50 47) <| .seq (maddC 50 6 44 53) <| .seq (maddC 50 2 45 53) <|
  .seq (maddC 50 5 49 53) <| .seq (maddC 50 2 48 53) <| .seq (fetchC 36 11 50 20) <|
  .seq (.ifLt 46 49 (.seq (.mov 51 5) (.seq (.add 51 46) (.sub 51 49))) (.seq (.mov 51 46)
    (.sub 51 49))) <|
  .seq (.mov 52 43) <| .seq (maddC 52 6 47 53) <| .seq (maddC 52 2 48 53) <|
  .seq (maddC 52 5 51 53) <| .seq (maddC 52 2 7 53) (sliceC 17 10 52 2 19)

/-- The column index of the coefficient of a term. -/
def jIdx {N : ℕ} (t e2 : Fin N) : ℕ := if e2.val ≤ t.val then t.val - e2.val else N + t.val - e2.val

set_option maxHeartbeats 10000000 in
theorem exec_tsIdxC {N k : ℕ} (σ : St) (hI : Inv E σ) (a r c1 : Fin 2) (c2 e12 : Fin k)
    (t e2 : Fin N) (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N) (h6 : σ.sc 6 = 2) (h7 : σ.sc 7 = 0)
    (h43 : σ.sc 43 = a.val) (h44 : σ.sc 44 = c1.val) (h45 : σ.sc 45 = c2.val)
    (h46 : σ.sc 46 = t.val) (h47 : σ.sc 47 = r.val) (h48 : σ.sc 48 = e12.val)
    (h49 : σ.sc 49 = e2.val) (RA RB : List ℕ) (h10 : σ.ls 10 = RA) (h11 : σ.ls 11 = RB)
    (hRA : RA.length = 4 * k * N * k) (hM : 4 * k * N * k + 2 * N ≤ E.M) (hC : k ≤ E.C) :
    ∃ sc', exec E tsIdxC σ = setSL σ sc' (Function.update (Function.update (Function.update
        σ.ls 20 ((RB.drop (oIdx ((r, (c1, c2), e2) : OI N k) * k + e12.val)).tail)) 19
        ((RA.drop (oIdx ((a, (r, e12), ⟨jIdx t e2, by unfold jIdx; split_ifs <;> omega⟩) :
          OI N k) * k)).drop k)) 17
        ((RA.drop (oIdx ((a, (r, e12), ⟨jIdx t e2, by unfold jIdx; split_ifs <;> omega⟩) :
          OI N k) * k)).take k)) ∧
      sc' 36 = RB.getD (oIdx ((r, (c1, c2), e2) : OI N k) * k + e12.val) 0 ∧
      Fr [36, 41, 50, 51, 52, 53] σ.sc sc' := by
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by subst h; exact c2.elim0)
  have hN : 0 < N := Nat.pos_of_ne_zero (fun h => by subst h; exact t.elim0)
  have ha := a.isLt; have hr := r.isLt; have hc1 := c1.isLt; have hc2 := c2.isLt
  have he12 := e12.isLt; have ht := t.isLt; have he2 := e2.isLt
  unfold tsIdxC
  have hO := oIdx_lt ((r, (c1, c2), e2) : OI N k)
  have hv4' : oIdx ((r, (c1, c2), e2) : OI N k) =
      ((r.val * 2 + c1.val) * k + c2.val) * N + e2.val := rfl
  have hv4 : oIdx ((r, (c1, c2), e2) : OI N k) * k + e12.val < 4 * k * N * k := by nlinarith
  have hb3 : ((r.val * 2 + c1.val) * k + c2.val) * N + e2.val ≤ E.M := by
    rw [← hv4']; nlinarith
  have hb4 : (((r.val * 2 + c1.val) * k + c2.val) * N + e2.val) * k + e12.val ≤ E.M := by
    rw [← hv4']; omega
  -- 1: `50 := r`
  set s1 := setSL σ (Function.update σ.sc 50 r.val) σ.ls
  rw [exec_seq, show exec E (.mov 50 47) σ = s1 by simp [exec, s1, setSL, h47]]
  -- 2–5: `50 := ((r·2 + c1)·k + c2)·N + e2)·k + e12`
  have e2' := exec_maddC (E := E) 50 6 44 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s1 (by simp [s1, setSL, h6, h44]; omega)
  set s2 := setSL s1 (Function.update (Function.update s1.sc 53 (s1.sc 50)) 50
    (s1.sc 50 * s1.sc 6 + s1.sc 44)) s1.ls
  rw [exec_seq, e2']
  have e3' := exec_maddC (E := E) 50 2 45 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s2 (by simp [s2, s1, setSL, h6, h44, h2, h45, Function.update_apply]; nlinarith)
  set s3 := setSL s2 (Function.update (Function.update s2.sc 53 (s2.sc 50)) 50
    (s2.sc 50 * s2.sc 2 + s2.sc 45)) s2.ls
  rw [exec_seq, e3']
  have e4' := exec_maddC (E := E) 50 5 49 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s3 (by simp [s3, s2, s1, setSL, h6, h44, h2, h45, h5, h49, Function.update_apply]; nlinarith)
  set s4 := setSL s3 (Function.update (Function.update s3.sc 53 (s3.sc 50)) 50
    (s3.sc 50 * s3.sc 5 + s3.sc 49)) s3.ls
  rw [exec_seq, e4']
  have e5' := exec_maddC (E := E) 50 2 48 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s4 (by simp [s4, s3, s2, s1, setSL, h6, h44, h2, h45, h5, h49, h48,
      Function.update_apply]; nlinarith)
  set s5 := setSL s4 (Function.update (Function.update s4.sc 53 (s4.sc 50)) 50
    (s4.sc 50 * s4.sc 2 + s4.sc 48)) s4.ls
  rw [exec_seq, e5']
  have h50 : s5.sc 50 = oIdx ((r, (c1, c2), e2) : OI N k) * k + e12.val := by
    simp [s5, s4, s3, s2, s1, setSL, h6, h44, h2, h45, h5, h49, h48, Function.update_apply, hv4']
  -- 6: fetch the digit
  obtain ⟨scF, eF, dF, fF⟩ := exec_fetchC (E := E) 36 11 50 20 s5
  rw [exec_seq, eF]
  set s6 := setSL s5 scF (Function.update s5.ls 20 ((s5.ls 11).drop (s5.sc 50)).tail)
  -- 7: `51 := j'`
  have hj : jIdx t e2 ≤ N + N := by unfold jIdx; split_ifs <;> omega
  set s7 := setSL s6 (Function.update s6.sc 51 (jIdx t e2)) s6.ls
  have h46' : s6.sc 46 = t.val := by
    simp only [s6, setSL]; rw [fF 46 (by decide)]; simp [s5, s4, s3, s2, s1, setSL, h46,
      Function.update_apply]
  have h49' : s6.sc 49 = e2.val := by
    simp only [s6, setSL]; rw [fF 49 (by decide)]; simp [s5, s4, s3, s2, s1, setSL, h49,
      Function.update_apply]
  have h5' : s6.sc 5 = N := by
    simp only [s6, setSL]; rw [fF 5 (by decide)]; simp [s5, s4, s3, s2, s1, setSL, h5,
      Function.update_apply]
  have e7 : exec E (.ifLt 46 49 (.seq (.mov 51 5) (.seq (.add 51 46) (.sub 51 49)))
      (.seq (.mov 51 46) (.sub 51 49))) s6 = s7 := by
    simp only [exec, h46', h49', h5', s7, setSL, jIdx]
    split_ifs with h1 h2 h2
    · omega
    · simp only [Function.update_self, Function.update_idem, Function.update_of_ne
        (by decide : (46 : SR) ≠ 51), Function.update_of_ne (by decide : (49 : SR) ≠ 51), h46',
        h49', h5']
      rw [min_eq_left (by omega)]
    · simp [Function.update_of_ne (by decide : (49 : SR) ≠ 51), h46', h49']
    · omega
  rw [exec_seq, e7]
  -- 8–12: `52 := oIdx (a, (r, e12), j') · k`
  have hf : ∀ x : SR, x ∉ ([36, 41, 51] : List SR) → s7.sc x = s5.sc x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [s7, s6, setSL]; rw [Function.update_of_ne hx.2.2, fF x (by simp [hx.1, hx.2.1])]
  have g : ∀ x : SR, x ∉ ([36, 41, 50, 51, 53] : List SR) → s7.sc x = σ.sc x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [hf x (by simp [hx.1, hx.2.1, hx.2.2.2.1])]
    simp [s5, s4, s3, s2, s1, setSL, Function.update_of_ne hx.2.2.1, Function.update_of_ne hx.2.2.2.2]
  have ja := jIdx t e2
  set j' : Fin N := ⟨jIdx t e2, by unfold jIdx; split_ifs <;> omega⟩
  have hO2 := oIdx_lt ((a, (r, e12), j') : OI N k)
  have hv5 : oIdx ((a, (r, e12), j') : OI N k) = ((a.val * 2 + r.val) * k + e12.val) * N +
      jIdx t e2 := rfl
  have hb5 : ((a.val * 2 + r.val) * k + e12.val) * N + jIdx t e2 ≤ E.M := by
    rw [← hv5]; nlinarith
  have hb6 : (((a.val * 2 + r.val) * k + e12.val) * N + jIdx t e2) * k ≤ E.M := by
    rw [← hv5]; nlinarith
  set s8 := setSL s7 (Function.update s7.sc 52 a.val) s7.ls
  rw [exec_seq, show exec E (.mov 52 43) s7 = s8 by
    simp [exec, s8, setSL, g 43 (by decide), h43]]
  have e9 := exec_maddC (E := E) 52 6 47 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s8 (by simp [s8, setSL, g 6 (by decide), g 47 (by decide), h6, h47]; omega)
  set s9 := setSL s8 (Function.update (Function.update s8.sc 53 (s8.sc 52)) 52
    (s8.sc 52 * s8.sc 6 + s8.sc 47)) s8.ls
  rw [exec_seq, e9]
  have e10 := exec_maddC (E := E) 52 2 48 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s9 (by simp [s9, s8, setSL, Function.update_apply, g 6 (by decide),
      g 47 (by decide), g 2 (by decide), g 48 (by decide), h6, h47, h2, h48]; nlinarith)
  set s10 := setSL s9 (Function.update (Function.update s9.sc 53 (s9.sc 52)) 52
    (s9.sc 52 * s9.sc 2 + s9.sc 48)) s9.ls
  rw [exec_seq, e10]
  have h51 : s7.sc 51 = jIdx t e2 := by simp [s7, setSL]
  have q11 : s10.sc 52 * s10.sc 5 + s10.sc 51 ≤ E.M := by
    simp [s10, s9, s8, setSL, Function.update_apply, g 6 (by decide),
      g 47 (by decide), g 2 (by decide), g 48 (by decide), g 5 (by decide), h6, h47, h2, h48, h5,
      h51]
    nlinarith
  have e11 := exec_maddC (E := E) 52 5 51 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s10 q11
  set s11 := setSL s10 (Function.update (Function.update s10.sc 53 (s10.sc 52)) 52
    (s10.sc 52 * s10.sc 5 + s10.sc 51)) s10.ls
  rw [exec_seq, e11]
  have q12 : s11.sc 52 * s11.sc 2 + s11.sc 7 ≤ E.M := by
    simp [s11, s10, s9, s8, setSL, Function.update_apply, g 6 (by decide),
      g 47 (by decide), g 2 (by decide), g 48 (by decide), g 5 (by decide), g 7 (by decide), h6,
      h47, h2, h48, h5, h51, h7]
    nlinarith
  have e12' := exec_maddC (E := E) 52 2 7 53 (by decide) (by decide) (by decide) (by decide)
    (by decide) s11 q12
  set s12 := setSL s11 (Function.update (Function.update s11.sc 53 (s11.sc 52)) 52
    (s11.sc 52 * s11.sc 2 + s11.sc 7)) s11.ls
  rw [exec_seq, e12']
  have h52 : s12.sc 52 = oIdx ((a, (r, e12), j') : OI N k) * k := by
    simp [s12, s11, s10, s9, s8, setSL, Function.update_apply, g 6 (by decide), g 47 (by decide),
      g 2 (by decide), g 48 (by decide), g 5 (by decide), g 7 (by decide), h6, h47, h2, h48, h5,
      h51, h7, hv5]
  -- 13: the slice
  have hls12 : s12.ls = Function.update σ.ls 20 ((RB.drop (oIdx ((r, (c1, c2), e2) : OI N k) * k
      + e12.val)).tail) := by
    simp only [s12, s11, s10, s9, s8, s7, s6, setSL]
    rw [h50]; simp [s5, s4, s3, s2, s1, setSL, h11]
  have hsrc : s12.src = σ.src := by
    simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setSL]
  have hI12 : Inv E s12 := by
    refine ⟨fun l => ?_, by rw [hsrc]; exact hI.2⟩
    rw [hls12]
    by_cases hl : l = 20
    · subst hl; simp only [Function.update_self]
      refine ⟨?_, fun x hx => ?_⟩
      · have := (hI.1 11).1; rw [h11] at this; simp; omega
      · exact (hI.1 11).2 x (by rw [h11]; exact List.mem_of_mem_drop (List.mem_of_mem_tail hx))
    · rw [Function.update_of_ne hl]; exact hI.1 l
  have h2' : s12.sc 2 = k := by
    simp [s12, s11, s10, s9, s8, setSL, Function.update_apply, g 2 (by decide), h2]
  have hl10 : s12.ls 10 = RA := by rw [hls12]; simp [h10]
  obtain ⟨scS, eS, fS⟩ := exec_sliceC (E := E) 17 10 52 2 19 (by decide) s12 hI12
    (by rw [h2', h52, hl10, hRA]; nlinarith) (by decide) (by rw [h2']; exact hC)
  rw [eS]
  refine ⟨scS, ?_, ?_, ?_⟩
  · rw [hls12, h52, h2']
    simp only [Function.update_of_ne (by decide : (10 : LR) ≠ 20), h10]
    rfl
  · rw [fS 36 (by decide)]
    simp only [s12, s11, s10, s9, s8, s7, s6, setSL]
    simp only [Function.update_of_ne (by decide : (36 : SR) ≠ 52),
      Function.update_of_ne (by decide : (36 : SR) ≠ 53), Function.update_of_ne (by decide : (36 : SR) ≠ 51)]
    rw [dF, h50]; simp [s5, s4, s3, s2, s1, setSL, h11]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [fS x (by simp [hx.2.1])]
    simp only [s12, s11, s10, s9, s8, setSL]
    rw [Function.update_of_ne hx.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2,
      Function.update_of_ne hx.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2,
      Function.update_of_ne hx.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2,
      Function.update_of_ne hx.2.2.2.2.1, Function.update_of_ne hx.2.2.2.2.2,
      Function.update_of_ne hx.2.2.2.2.1]
    exact g x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.2])

end FhatGen

end SigabaNeo.Lattices
