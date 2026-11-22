import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenTerm

/-!
# Generating gate tapes: `termStep`

`termStepC`: the index phase `tsIdxC`, the AND of the coefficient by the digit (`andLC`) into the
list `1`, then `modSub` (if `e2 ≤ t`) or `modAdd` of the running sum (list `0`) and the product,
into the list `2` (`exec_termStepC`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- **`termStep` as register code.** -/
def termStepC : Code :=
  .seq tsIdxC (.seq (.lnil 1) (.seq (andLC 2 17 18 1) (.ifLt 46 49 modAddC modSubC)))

/-- The constant registers of a NAND block: `Cst k K`, `5 = N`, `6 = 2`, `7 = 0`. -/
def CstB (k K N : ℕ) (σ : St) : Prop := Cst (E := E) k K σ ∧ σ.sc 5 = N ∧ σ.sc 6 = 2 ∧ σ.sc 7 = 0

theorem nm_of {x : SR} (L : List SR) (Q : SR → Prop) [DecidablePred Q] (h : ∀ y ∈ L, ¬ Q y)
    (hx : Q x) : x ∉ L := fun hm => h x hm hx

theorem noNand_tsIdxC : NoNand tsIdxC := by
  simp [NoNand, tsIdxC, maddC, fetchC, sliceC, dropC, takeC]

theorem exec_ifLt (a b : SR) (p q : Code) (σ : St) :
    exec E (.ifLt a b p q) σ = if σ.sc a < σ.sc b then exec E p σ else exec E q σ := rfl

theorem exec_termStepC (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {N k K : ℕ} (hK : K ≤ k + 1) (repA repB : BI N k → Wire ι) (a : Fin 2) (col : Fin 2 × Fin k)
    (t : Fin N) (e : (Fin 2 × Fin k) × Fin N) (P : SLP ι) (acc : List (Wire ι)) (σ : St)
    (hc : CstB (E := E) k K N σ) (hI : Inv E σ) (hS : ScOK E σ)
    (h43 : σ.sc 43 = a.val) (h44 : σ.sc 44 = col.1.val) (h45 : σ.sc 45 = col.2.val)
    (h46 : σ.sc 46 = t.val) (h47 : σ.sc 47 = e.1.1.val) (h48 : σ.sc 48 = e.1.2.val)
    (h49 : σ.sc 49 = e.2.val) (h10 : σ.ls 10 = repList E ix repA)
    (h11 : σ.ls 11 = repList E ix repB) (h0 : σ.ls 0 = acc.map (pos E ix)) (hacc : acc.length = k)
    (hcap : k + 3 ≤ E.C) (hbig : 4 * k * N * k + 2 * N + k + 2 ≤ E.M)
    (hM : E.n + (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e).1.length ≤ E.M) :
    ∃ sc' ls', exec E termStepC (mk E ix P σ) =
        mk E ix (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e).1 (setSL σ sc' ls') ∧
      ls' 2 = (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e).2.map (pos E ix) ∧
      (∀ r : SR, r.val < 16 ∨ (43 ≤ r.val ∧ r.val ≤ 49) ∨ 53 < r.val → sc' r = σ.sc r) ∧
      (∀ l : LR, (10 ≤ l.val ∧ l.val ≤ 16) ∨ 20 < l.val → ls' l = σ.ls l) := by
  have hnM' : E.n ≤ E.M := by omega
  obtain ⟨⟨⟨hc0, hc1⟩, hc2, hc3, hc4⟩, hc5, hc6, hc7⟩ := hc
  obtain ⟨⟨r, e12⟩, e2⟩ := e
  obtain ⟨c1, c2⟩ := col
  simp only at h44 h45 h47 h48 h49
  have hlenA := length_repList E ix repA
  -- the index phase
  obtain ⟨sc1, e1, d1, f1⟩ := exec_tsIdxC (E := E) σ hI a r c1 c2 e12 t e2 hc2 hc5 hc6 hc7 h43 h44
    h45 h46 h47 h48 h49 _ _ h10 h11 hlenA (by omega) (by omega)
  set j' : Fin N := ⟨jIdx t e2, by unfold jIdx; split_ifs <;> omega⟩ with hj'
  set coef : List (Wire ι) := List.ofFn fun i : Fin k => repA (a, (r, e12), i, j')
  set wd : Wire ι := repB (r, (c1, c2), e12, e2)
  set ls1 := Function.update (Function.update (Function.update σ.ls 20
    (((repList E ix repB).drop (oIdx ((r, (c1, c2), e2) : OI N k) * k + e12.val)).tail)) 19
    (((repList E ix repA).drop (oIdx ((a, (r, e12), j') : OI N k) * k)).drop k)) 17
    (((repList E ix repA).drop (oIdx ((a, (r, e12), j') : OI N k) * k)).take k)
  have hf1 : ∀ x : SR, x.val < 36 ∨ (42 < x.val ∧ x.val < 50) ∨ 53 < x.val → sc1 x = σ.sc x :=
    fun x hx => f1 x (nm_of _ (fun x : SR => x.val < 36 ∨ (42 < x.val ∧ x.val < 50) ∨ 53 < x.val)
      (by decide) hx)
  set τ2 := setSL σ sc1 (Function.update ls1 1 [])
  have e2' : exec E (.seq tsIdxC (.lnil 1)) (mk E ix P σ) = mk E ix P τ2 := by
    rw [exec_seq, exec_mk_noNand _ noNand_tsIdxC, e1]; rfl
  have hIS2 := is_exec hnM' hWM e2' ⟨hI, hS⟩
  unfold termStepC
  rw [exec_seq, exec_seq, ← exec_seq (p := tsIdxC) (q := .lnil 1), e2', exec_seq]
  -- the AND of the coefficient by the digit, into `1`
  have hslice := repList_slice E ix repA ((a, (r, e12), j') : OI N k)
  have hgetB := repList_getD E ix repB ((r, (c1, c2), e2) : OI N k) e12
  have hcl : coef.length = k := List.length_ofFn
  have hc2' : Consts E τ2 := ⟨by rw [← hc0]; exact hf1 0 (by decide),
    by rw [← hc1]; exact hf1 1 (by decide)⟩
  have hcoefW0 : ∀ (j : Fin N), j.val = jIdx t e2 → coefW repA a (r, e12) j = coef := by
    intro j hj; have : j = j' := Fin.ext hj; subst this; rfl
  have hTa : ¬ e2.val ≤ t.val → termStep (.gate 0) (2 ^ K) k repA repB a (c1, c2) t (P, acc)
      ((r, e12), e2) = modAdd (.gate 0) (2 ^ K) k (andL wd P coef).1 acc (andL wd P coef).2 :=
    fun h => by
      simp only [termStep, dif_neg h]
      rw [hcoefW0 _ (by simp [jIdx]; omega)]
  have hTs : e2.val ≤ t.val → termStep (.gate 0) (2 ^ K) k repA repB a (c1, c2) t (P, acc)
      ((r, e12), e2) = modSub (.gate 0) (2 ^ K) k (andL wd P coef).1 acc (andL wd P coef).2 :=
    fun h => by
      simp only [termStep, dif_pos h]
      rw [hcoefW0 _ (by simp [jIdx]; omega)]
  have hMa : E.n + (andL wd P coef).1.length ≤ E.M := by
    refine le_trans (Nat.add_le_add_left ?_ _) hM
    by_cases h : e2.val ≤ t.val
    · rw [hTs h]; exact le_length_modSub _ _ _ _ _ _
    · rw [hTa h]; exact le_length_modAdd _ _ _ _ _ _
  obtain ⟨sc3, h3, f3⟩ := exec_andLC (n := 2) (lA := 17) (lB := 18) (lR := 1) hnM' hWM hix
    (by decide) (by decide) (by decide) wd coef P τ2 [] hc2' hIS2.1 hIS2.2
    (by show sc1 36 = _; rw [d1, hgetB])
    (by show (Function.update ls1 1 []) 17 = _
        rw [Function.update_of_ne (by decide)]; simp only [ls1, Function.update_self]
        rw [hslice])
    (by simp [τ2, setSL]) (by show sc1 2 = _; rw [hf1 2 (by decide), hc2, hcl]) (by decide)
    (by simp; omega) hMa
  set Pa := (andL wd P coef).1
  set ls3' := ls3 τ2.ls 17 18 1 ([] ++ (andL wd P coef).2.map (pos E ix))
  have e3 : ({ τ2 with sc := sc3, ls := ls3' } : St) = setSL σ sc3 ls3' := rfl
  rw [e3] at h3
  have hIS3 := is_exec hnM' hWM h3 hIS2
  rw [h3]
  have hf3 : ∀ x : SR, x.val < 33 ∨ (42 < x.val ∧ x.val < 50) ∨ 53 < x.val → sc3 x = σ.sc x :=
    fun x hx => by
      rw [f3 x (nm_of _ (fun x : SR => x.val < 33 ∨ (42 < x.val ∧ x.val < 50) ∨ 53 < x.val)
        (by decide) hx)]
      exact hf1 x (by omega)
  -- the modular subtraction or addition, into `2`
  have hcst : Cst (E := E) k K (setSL σ sc3 ls3') := ⟨⟨by rw [← hc0]; exact hf3 0 (by decide),
    by rw [← hc1]; exact hf3 1 (by decide)⟩, by rw [← hc2]; exact hf3 2 (by decide),
    by rw [← hc3]; exact hf3 3 (by decide), by rw [← hc4]; exact hf3 4 (by decide)⟩
  have hA0 : (setSL σ sc3 ls3').ls 0 = acc.map (pos E ix) := by
    simp [setSL, ls3', ls3, τ2, ls1, Function.update_apply, h0]
  have hB1 : (setSL σ sc3 ls3').ls 1 = (andL wd P coef).2.map (pos E ix) := by
    simp [setSL, ls3', ls3]
  have hlb : (andL wd P coef).2.length = k := by rw [(length_andL wd P coef).2, hcl]
  have ht46 : sc3 46 = t.val := by rw [hf3 46 (by decide), h46]
  have ht49 : sc3 49 = e2.val := by rw [hf3 49 (by decide), h49]
  have hcoefW : ∀ (j : Fin N), j.val = jIdx t e2 → coefW repA a (r, e12) j = coef := by
    intro j hj; have : j = j' := Fin.ext hj; subst this; rfl
  rw [exec_ifLt]
  by_cases hlt : t.val < e2.val
  · rw [if_pos (by simp [setSL, ht46, ht49, hlt])]
    rw [hTa (by omega)] at hM
    obtain ⟨sc4, ls4, h4, d4, f4, g4⟩ := exec_modAddC hnM hWM hix hK acc (andL wd P coef).2 Pa
      (setSL σ sc3 ls3') hcst hIS3.1 hIS3.2 hA0 hB1 hacc hlb hcap (by omega) hM
    have hT : termStep (.gate 0) (2 ^ K) k repA repB a (c1, c2) t (P, acc) ((r, e12), e2) =
        modAdd (.gate 0) (2 ^ K) k Pa acc (andL wd P coef).2 := by
      simp only [termStep, dif_neg (show ¬ e2.val ≤ t.val by omega)]
      rw [hcoefW _ (by simp [jIdx]; omega)]
    rw [h4, hT]
    refine ⟨sc4, ls4, rfl, d4, fun x hx => ?_, fun l hl => ?_⟩
    · rw [f4 x (by omega)]; exact hf3 x (by omega)
    · rw [g4 l (by omega)]
      have hne : ∀ j : LR, j.val ≤ 9 ∨ (16 < j.val ∧ j.val ≤ 20) → l ≠ j := fun j hj h => by
        subst h; omega
      simp [setSL, ls3', ls3, τ2, ls1, Function.update_apply, hne 1 (by decide),
        hne 17 (by decide), hne 18 (by decide), hne 19 (by decide), hne 20 (by decide)]
  · rw [if_neg (by simp [setSL, ht46, ht49, hlt])]
    rw [hTs (by omega)] at hM
    obtain ⟨sc4, ls4, h4, d4, f4, g4⟩ := exec_modSubC hnM hWM hix acc (andL wd P coef).2 Pa
      (setSL σ sc3 ls3') hcst hIS3.1 hIS3.2 hA0 hB1 hacc hlb hcap (by omega) hM
    have hT : termStep (.gate 0) (2 ^ K) k repA repB a (c1, c2) t (P, acc) ((r, e12), e2) =
        modSub (.gate 0) (2 ^ K) k Pa acc (andL wd P coef).2 := by
      simp only [termStep, dif_pos (show e2.val ≤ t.val by omega)]
      rw [hcoefW _ (by simp [jIdx]; omega)]
    rw [h4, hT]
    refine ⟨sc4, ls4, rfl, d4, fun x hx => ?_, fun l hl => ?_⟩
    · rw [f4 x (by omega)]; exact hf3 x (by omega)
    · rw [g4 l (by omega)]
      have hne : ∀ j : LR, j.val ≤ 9 ∨ (16 < j.val ∧ j.val ≤ 20) → l ≠ j := fun j hj h => by
        subst h; omega
      simp [setSL, ls3', ls3, τ2, ls1, Function.update_apply, hne 1 (by decide),
        hne 17 (by decide), hne 18 (by decide), hne 19 (by decide), hne 20 (by decide)]

end FhatGen

end SigabaNeo.Lattices
