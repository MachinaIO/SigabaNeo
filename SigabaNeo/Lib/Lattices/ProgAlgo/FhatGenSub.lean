import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenMod

/-!
# Generating gate tapes: modular subtraction

The register code of `modSub` (`modSubC`, `exec_modSubC`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- **`modSub` as register code**: the operands in the lists `0`, `1`, the result in `2`
(scratch: the lists `3 … 9`, the registers `16 … 42`). -/
def modSubC : Code :=
  .seq (.lnil 3) <| .seq (notLC 2 1 9 3) <| .seq (.lnil 4) <| .seq (.mov 18 rONE) <|
  .seq (rippleAddC 2 0 3 4) <| .seq (.lnil 5) <| .seq (takeC 2 4 5) <| .seq (.lpop 36 4) <|
  .seq (.lmov 6 5) <| .seq (constC 2 7 (qConstBody 7)) <| .seq (.lnil 8) <| .seq (.mov 18 rZ) <|
  .seq (rippleAddC 2 5 7 8) <| .seq (.lnil 3) <| .seq (takeC 2 8 3) <| .seq (.lnil 2)
    (muxLC 2 6 3 2)

theorem exec_modSubC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {k K : ℕ}
    (as bs : List (Wire ι)) (P : SLP ι) (σ : St) (hc : Cst (E := E) k K σ)
    (hI : Inv E σ) (hS : ScOK E σ) (hA : σ.ls 0 = as.map (pos E ix))
    (hB : σ.ls 1 = bs.map (pos E ix)) (hla : as.length = k) (hlb : bs.length = k)
    (hcap : k + 3 ≤ E.C) (hkM : k + 2 ≤ E.M)
    (hM : E.n + (exec E modSubC (mk E ix P σ)).t ≤ E.M) :
    ∃ sc' ls', exec E modSubC (mk E ix P σ) =
        mk E ix (modSub (.gate 0) (2 ^ K) k P as bs).1 (setSL σ sc' ls') ∧
      ls' 2 = (modSub (.gate 0) (2 ^ K) k P as bs).2.map (pos E ix) ∧
      (∀ r : SR, r.val < 16 ∨ 42 < r.val → sc' r = σ.sc r) ∧ (∀ l : LR, 9 < l.val → ls' l = σ.ls l) := by
  have hnM' : E.n ≤ E.M := by omega
  simp only [modSubC, exec_seq] at hM ⊢
  -- 1, 2: `lnil 3`, `notL bs` into `3`
  set σ1 := setSL σ σ.sc (Function.update σ.ls 3 [])
  have e1 : exec E (.lnil 3) (mk E ix P σ) = mk E ix P σ1 := rfl
  have hIS1 := is_exec hnM' hWM (τ := mk E ix P σ) e1 ⟨hI, hS⟩
  rw [e1] at hM ⊢
  obtain ⟨sc2, h2, f2⟩ := exec_notLC (lA := 1) (lB := 9) (lR := 3) (n := 2) hnM' hWM hix
    (by decide) (by decide) (by decide) bs P σ1 [] hc.1 hIS1.1 hIS1.2 (by simp [σ1, setSL, hB])
    (by simp [σ1, setSL]) (by simp [σ1, setSL, hc.2.1, hlb]) (by decide) (by simp; omega)
    (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  set r1 := notL P bs
  have hl1 : r1.2.length = k := by rw [(length_notL P bs).2, hlb]
  set ls2 := ls3 σ1.ls 1 9 3 ([] ++ r1.2.map (pos E ix))
  have e2 : ({ σ1 with sc := sc2, ls := ls2 } : St) = setSL σ sc2 ls2 := rfl
  rw [e2] at h2
  have hIS2 := is_exec hnM' hWM h2 hIS1
  rw [h2] at hM ⊢
  have fr2 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc2 r = σ.sc r := fun r hr => by
    rw [f2 r (not_mem_of_out _ (by decide) hr)]; rfl
  -- 3, 4, 5: `lnil 4`, `mov 18 1`, `rippleAdd as r1 1` into `4`
  set σ4 := setSL σ (Function.update sc2 18 E.n) (Function.update ls2 4 [])
  have e4 : exec E (.mov 18 rONE) (exec E (.lnil 4) (mk E ix r1.1 (setSL σ sc2 ls2))) =
      mk E ix r1.1 σ4 := by
    have h1 : sc2 rONE = E.n := by rw [fr2 0 (by decide)]; exact hc.1.1
    simp only [exec, mk, σ4, setSL, h1]
  have hIS4 := is_exec hnM' hWM (c := .seq (.lnil 4) (.mov 18 rONE)) e4 hIS2
  rw [e4] at hM ⊢
  have fr4 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → σ4.sc r = σ.sc r := fun r hr => by
    simp only [σ4, setSL]
    rw [Function.update_of_ne (fun h => by subst h; revert hr; decide)]; exact fr2 r hr
  have hc4 : Consts E σ4 := ⟨by rw [← hc.1.1]; exact fr4 0 (by decide),
    by rw [← hc.1.2]; exact fr4 1 (by decide)⟩
  obtain ⟨sc5, h5, f5⟩ := exec_rippleAddC (lA := 0) (lB := 3) (lR := 4) (n := 2) hnM' hWM hix
    (by decide) (by decide) (by decide) as r1.2 r1.1 σ4 .one [] (by omega) hc4 hIS4.1 hIS4.2
    (by simp [σ4, setSL, ls2, ls3, σ1, Function.update_apply, hA])
    (by simp [σ4, setSL, ls2, ls3, Function.update_apply]) (by simp [σ4, setSL])
    (by simp [σ4, setSL, pos]) (by rw [fr4 2 (by decide), hc.2.1, hla]) (by simp; omega)
    (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  set r2 := rippleAdd r1.1 as r1.2 .one
  have hl2 : r2.2.length = k + 1 := by rw [length_rippleAdd_eq _ _ _ _ (by omega), hla]
  set ls5 := ls3 σ4.ls 0 3 4 ([] ++ r2.2.map (pos E ix))
  have e5 : ({ σ4 with sc := sc5, ls := ls5 } : St) = setSL σ sc5 ls5 := rfl
  rw [e5] at h5
  have hIS5 := is_exec hnM' hWM h5 hIS4
  rw [h5] at hM ⊢
  have fr5 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc5 r = σ.sc r := fun r hr => by
    rw [f5 r (not_mem_of_out _ (by decide) hr)]; exact fr4 r hr
  -- 6, 7: `lnil 5`, the first `k` wires of `r2` into `5`
  have hsplit : r2.2.map (pos E ix) = (r2.2.take k).map (pos E ix) ++
      (r2.2.drop k).map (pos E ix) := by rw [← List.map_append, List.take_append_drop]
  obtain ⟨sc7, h7, f7⟩ := exec_takeC (E := E) (n := 2) (lA := 4) (lR := 5) (by decide)
    ((r2.2.take k).map (pos E ix)) ((r2.2.drop k).map (pos E ix)) []
    (exec E (.lnil 5) (setSL σ sc5 ls5)) (by exact (is_exec hnM' hWM (c := .lnil 5) rfl hIS5).1)
    (by show (Function.update ls5 5 []) 4 = _
        rw [Function.update_of_ne (by decide)]
        simp only [ls5, ls3, Function.update_self]; rw [List.nil_append, hsplit])
    (by simp [exec])
    (by simp [exec, setSL]; rw [fr5 2 (by decide), hc.2.1]; simp [hl2]) (by simp; omega)
  rw [exec_mk_noNand (.lnil 5) trivial, exec_mk_noNand (takeC 2 4 5)
    (by simp [NoNand, takeC]), h7] at hM ⊢
  set τ6 := exec E (.lnil 5) (setSL σ sc5 ls5)
  set ls7 := Function.update (Function.update τ6.ls 4
    ((r2.2.drop k).map (pos E ix))) 5 ([] ++ (r2.2.take k).map (pos E ix))
  have e7 : ({ out := τ6.out, t := τ6.t, sc := sc7, ls := ls7, src := τ6.src } : St) =
      setSL σ sc7 ls7 := rfl
  rw [e7] at hM ⊢
  have hIS7 : Inv E (mk E ix r2.1 (setSL σ sc7 ls7)) ∧ ScOK E (mk E ix r2.1 (setSL σ sc7 ls7)) :=
    is_exec hnM' hWM (c := .seq (.lnil 5) (takeC 2 4 5)) (τ := mk E ix r2.1 (setSL σ sc5 ls5))
      (by rw [exec_seq, exec_mk_noNand (.lnil 5) trivial, exec_mk_noNand (takeC 2 4 5)
        (by simp [NoNand, takeC]), h7, e7]) hIS5
  have fr7 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc7 r = σ.sc r := fun r hr => by
    rw [f7 r (not_mem_of_out _ (by decide) hr)]; exact fr5 r hr
  -- 8, 9: the carry into `36`, copy `5` into `6`
  set w36 := r2.2.getD k .one
  have hY : r2.2.drop k = [w36] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
    simp only [w36, List.getD_eq_getElem _ _ (show k < r2.2.length by omega)]
  set σ9 := setSL σ (Function.update sc7 36 (pos E ix w36)) (Function.update (Function.update
    ls7 4 []) 6 ([] ++ (r2.2.take k).map (pos E ix)))
  have e9 : exec E (.lmov 6 5) (exec E (.lpop 36 4) (mk E ix r2.1 (setSL σ sc7 ls7))) =
      mk E ix r2.1 σ9 := by
    rw [exec_mk_noNand (.lpop 36 4) trivial, exec_mk_noNand (.lmov 6 5) trivial]
    have h4 : ls7 4 = [pos E ix w36] := by simp [ls7, hY]
    simp only [exec, σ9, setSL, h4, List.headD_cons, List.tail_cons]
    congr 3
  have hIS9 := is_exec hnM' hWM (c := .seq (.lpop 36 4) (.lmov 6 5)) e9 hIS7
  rw [e9] at hM ⊢
  have fr9 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → σ9.sc r = σ.sc r := fun r hr => by
    simp only [σ9, setSL]
    rw [Function.update_of_ne (fun h => by subst h; revert hr; decide)]; exact fr7 r hr
  have hc9 : Cst (E := E) k K σ9 := ⟨⟨by rw [← hc.1.1]; exact fr9 0 (by decide),
    by rw [← hc.1.2]; exact fr9 1 (by decide)⟩, by rw [← hc.2.1]; exact fr9 2 (by decide),
    by rw [← hc.2.2.1]; exact fr9 3 (by decide), by rw [← hc.2.2.2]; exact fr9 4 (by decide)⟩
  -- 10: the constant `2^K` into `7`
  have h10 := exec_constC (E := E) (l := 7) (cnt := 2) (Q := Cst (E := E) k K) (by decide)
    (fun σ h v ls' => cst_setSL h (by decide) v ls')
    (fun σ i hq hi hl => exec_qConstBody (E := E) hnM 7 σ i hq hi hl) σ9 hc9
    (by rw [hc9.2.1]; omega) (by rw [hc9.2.1]; omega)
  have hIS10 := is_exec hnM' hWM (c := constC 2 7 (qConstBody 7)) (τ := mk E ix r2.1 σ9)
    (by rw [exec_mk_noNand _ (by simp [NoNand, constC, qConstBody]), h10]) hIS9
  rw [exec_mk_noNand _ (by simp [NoNand, constC, qConstBody]), h10] at hM ⊢
  set KQ : List (Wire ι) := constL (.gate 0) k (2 ^ K)
  have hKQ : (List.range (σ9.sc 2)).map (fun i => if i = K then E.n else E.n + 1) =
      KQ.map (pos E ix) := by
    rw [hc9.2.1, show KQ = _ from constL_eq_map _ _ _, List.map_map]
    apply List.map_congr_left; intro i _
    simp only [Function.comp, Nat.testBit_two_pow]
    by_cases h : K = i
    · subst h; simp [pos]
    · simp [h, pos, Ne.symm h]
  rw [hKQ] at hM ⊢ hIS10
  set sc10 := Function.update σ9.sc 42 (σ9.sc 2)
  set ls10 := Function.update σ9.ls 7 (KQ.map (pos E ix))
  have e10 : setSL σ9 sc10 ls10 = setSL σ sc10 ls10 := rfl
  rw [e10] at hM ⊢ hIS10
  -- 11, 12: `lnil 8`, `mov 18 z`
  set σ12 := setSL σ (Function.update sc10 18 (E.n + 1)) (Function.update ls10 8 [])
  have e12 : exec E (.mov 18 rZ) (exec E (.lnil 8) (mk E ix r2.1 (setSL σ sc10 ls10))) =
      mk E ix r2.1 σ12 := by
    have hz : sc10 rZ = E.n + 1 := by
      simp only [sc10]; rw [Function.update_of_ne (by decide)]; exact hc9.1.2
    simp only [exec, mk, σ12, setSL, hz]
  have hIS12 := is_exec hnM' hWM (c := .seq (.lnil 8) (.mov 18 rZ)) e12 hIS10
  rw [e12] at hM ⊢
  have fr12 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → σ12.sc r = σ.sc r := fun r hr => by
    simp only [σ12, setSL, sc10]
    rw [Function.update_of_ne (fun h => by subst h; revert hr; decide),
      Function.update_of_ne (fun h => by subst h; revert hr; decide)]
    exact fr9 r hr
  have hc12 : Consts E σ12 := ⟨by rw [← hc.1.1]; exact fr12 0 (by decide),
    by rw [← hc.1.2]; exact fr12 1 (by decide)⟩
  -- 13: `rippleAdd (take k r2) KQ z` into `8`
  have hKQl : KQ.length = k := constL_length _ _ _
  obtain ⟨sc13, h13, f13⟩ := exec_rippleAddC (lA := 5) (lB := 7) (lR := 8) (n := 2) hnM' hWM hix
    (by decide) (by decide) (by decide) (r2.2.take k) KQ r2.1 σ12 (.gate 0) [] (by simp; omega)
    hc12 hIS12.1 hIS12.2
    (by simp [σ12, setSL, ls10, σ9, ls7, Function.update_apply])
    (by simp [σ12, setSL, ls10, Function.update_apply]) (by simp [σ12, setSL])
    (by simp [σ12, setSL, pos]) (by rw [fr12 2 (by decide), hc.2.1]; simp; omega)
    (by simp; omega) (le_trans (Nat.add_le_add_left (by t_chain) _) hM)
  set r3 := rippleAdd r2.1 (r2.2.take k) KQ (.gate 0)
  have hl3 : r3.2.length = k + 1 := by rw [length_rippleAdd_eq _ _ _ _ (by simp; omega)]; simp; omega
  set ls13 := ls3 σ12.ls 5 7 8 ([] ++ r3.2.map (pos E ix))
  have e13 : ({ σ12 with sc := sc13, ls := ls13 } : St) = setSL σ sc13 ls13 := rfl
  rw [e13] at h13
  have hIS13 := is_exec hnM' hWM h13 hIS12
  rw [h13] at hM ⊢
  have fr13 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc13 r = σ.sc r := fun r hr => by
    rw [f13 r (not_mem_of_out _ (by decide) hr)]; exact fr12 r hr
  -- 14, 15: `lnil 3`, the first `k` wires of `r3` into `3`
  obtain ⟨sc15, h15, f15⟩ := exec_takeC (E := E) (n := 2) (lA := 8) (lR := 3) (by decide)
    ((r3.2.take k).map (pos E ix)) ((r3.2.drop k).map (pos E ix)) []
    (exec E (.lnil 3) (setSL σ sc13 ls13)) (by exact (is_exec hnM' hWM (c := .lnil 3) rfl hIS13).1)
    (by show (Function.update ls13 3 []) 8 = _
        rw [Function.update_of_ne (by decide)]
        simp only [ls13, ls3, Function.update_self]
        rw [List.nil_append, ← List.map_append, List.take_append_drop])
    (by simp [exec])
    (by simp [exec, setSL]; rw [fr13 2 (by decide), hc.2.1]; simp; omega) (by simp; omega)
  rw [exec_mk_noNand (.lnil 3) trivial, exec_mk_noNand (takeC 2 8 3)
    (by simp [NoNand, takeC]), h15] at hM ⊢
  set τ14 := exec E (.lnil 3) (setSL σ sc13 ls13)
  set ls15 := Function.update (Function.update τ14.ls 8
    ((r3.2.drop k).map (pos E ix))) 3 ([] ++ (r3.2.take k).map (pos E ix))
  have e15 : ({ out := τ14.out, t := τ14.t, sc := sc15, ls := ls15, src := τ14.src } : St) =
      setSL σ sc15 ls15 := rfl
  rw [e15] at hM ⊢
  have hIS15 : Inv E (mk E ix r3.1 (setSL σ sc15 ls15)) ∧ ScOK E (mk E ix r3.1 (setSL σ sc15 ls15)) :=
    is_exec hnM' hWM (c := .seq (.lnil 3) (takeC 2 8 3)) (τ := mk E ix r3.1 (setSL σ sc13 ls13))
      (by rw [exec_seq, exec_mk_noNand (.lnil 3) trivial, exec_mk_noNand (takeC 2 8 3)
        (by simp [NoNand, takeC]), h15, e15]) hIS13
  have fr15 : ∀ r : SR, r.val < 16 ∨ 42 < r.val → sc15 r = σ.sc r := fun r hr => by
    rw [f15 r (not_mem_of_out _ (by decide) hr)]; exact fr13 r hr
  -- 16, 17: `lnil 2`, the mux into `2`
  set σ16 := setSL σ sc15 (Function.update ls15 2 [])
  have e16 : exec E (.lnil 2) (mk E ix r3.1 (setSL σ sc15 ls15)) = mk E ix r3.1 σ16 := rfl
  have hIS16 := is_exec hnM' hWM e16 hIS15
  rw [e16] at hM ⊢
  have hc16 : Consts E σ16 := ⟨by rw [← hc.1.1]; exact fr15 0 (by decide),
    by rw [← hc.1.2]; exact fr15 1 (by decide)⟩
  obtain ⟨sc17, h17, f17⟩ := exec_muxLC (lA := 6) (lB := 3) (lR := 2) (n := 2) hnM' hWM hix
    (by decide) (by decide) (by decide) w36 (r2.2.take k) (r3.2.take k) r3.1 σ16 []
    (by simp; omega) hc16 hIS16.1 hIS16.2
    (by simp only [σ16, setSL]; rw [f15 36 (by decide)]
        show sc13 36 = _
        rw [f13 36 (by decide)]
        simp [σ12, setSL, sc10, σ9, Function.update_apply])
    (by simp [σ16, setSL, ls15, τ14, exec, ls13, ls3, σ12, ls10, σ9, Function.update_apply])
    (by simp [σ16, setSL, ls15, Function.update_apply]) (by simp [σ16, setSL])
    (by rw [show σ16.sc 2 = sc15 2 from rfl, fr15 2 (by decide), hc.2.1]; simp; omega)
    (by decide) (by simp; omega) hM
  rw [h17]
  refine ⟨sc17, _, rfl, by simp [ls3, modSub]; rfl, fun r hr => ?_, fun l hl => ?_⟩
  · rw [f17 r (not_mem_of_out _ (by decide) hr)]; exact fr15 r hr
  · have hne : ∀ j : LR, j.val ≤ 9 → l ≠ j := fun j hj h => by subst h; omega
    simp [ls3, σ16, setSL, ls15, τ14, exec, ls13, σ12, ls10, σ9, ls7, τ6, ls5, σ4, ls2, σ1,
      Function.update_apply, hne 0 (by decide), hne 1 (by decide), hne 2 (by decide),
      hne 3 (by decide), hne 4 (by decide), hne 5 (by decide), hne 6 (by decide),
      hne 7 (by decide), hne 8 (by decide), hne 9 (by decide)]

end FhatGen

end SigabaNeo.Lattices
