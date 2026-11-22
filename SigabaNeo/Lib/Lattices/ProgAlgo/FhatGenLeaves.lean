import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenTerm2

/-!
# Generating gate tapes: the terms of an output coefficient

`leavesC`: one round of `termStepC` per term `e` of `enumT` (from the running sum `constL z k 0`),
appending its `k` output wires to the list `12`; the term is held in the registers `47 … 49` and
advanced by an odometer (`odoC`). `exec_leavesC`: it is `leaves`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-! ### Lengths -/

theorem length_modAdd_eq (z : Wire ι) (q k : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length = k) (hb : bs.length = k) : (modAdd z q k p as bs).2.length = k := by
  have h1 : (rippleAdd p as bs z).2.length = k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by omega), ha]
  have h2 : (rippleAdd (rippleAdd p as bs z).1 (rippleAdd p as bs z).2
      (constL z (k + 1) (2 ^ (k + 1) - q)) z).2.length = k + 2 := by
    rw [length_rippleAdd_eq _ _ _ _ (by rw [h1, constL_length]), h1]
  show (List.take k (muxL _ _ _ _).2).length = k
  rw [List.length_take, length_muxL_eq _ _ _ _ (by rw [List.length_take, h2, h1]; omega),
    List.length_take, h2]
  omega

theorem length_modSub_eq (z : Wire ι) (q k : ℕ) (p : SLP ι) (as bs : List (Wire ι))
    (ha : as.length = k) (hb : bs.length = k) : (modSub z q k p as bs).2.length = k := by
  have h1 := (length_notL p bs).2
  have h2 : (rippleAdd (notL p bs).1 as (notL p bs).2 .one).2.length = k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by omega), ha]
  have h3 : (rippleAdd (rippleAdd (notL p bs).1 as (notL p bs).2 .one).1
      ((rippleAdd (notL p bs).1 as (notL p bs).2 .one).2.take k) (constL z k q) z).2.length =
      k + 1 := by
    rw [length_rippleAdd_eq _ _ _ _ (by rw [List.length_take, h2, constL_length]; omega),
      List.length_take, h2]; omega
  show (muxL _ _ _ _).2.length = k
  rw [length_muxL_eq _ _ _ _ (by rw [List.length_take, List.length_take, h2, h3]),
    List.length_take, h2]
  omega

theorem length_termStep {N k K : ℕ} (repA repB : BI N k → Wire ι) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (P : SLP ι) (acc : List (Wire ι)) (hacc : acc.length = k)
    (e : (Fin 2 × Fin k) × Fin N) :
    (termStep (.gate 0) (2 ^ K) k repA repB a col t (P, acc) e).2.length = k := by
  unfold termStep
  split_ifs
  · exact length_modSub_eq _ _ _ _ _ _ hacc (by rw [(length_andL _ _ _).2]; simp [coefW, bitsL])
  · exact length_modAdd_eq _ _ _ _ _ _ hacc (by rw [(length_andL _ _ _).2]; simp [coefW, bitsL])

/-! ### The order of the terms -/

theorem enumT_getElem? {N k : ℕ} (x : Fin 2) (y : Fin k) (z : Fin N) :
    (enumT N k)[(x.val * k + y.val) * N + z.val]? = some ((x, y), z) := by
  have e0 := getElem?_product (List.finRange k) (List.finRange 2) x.val y.val
    (by simpa using x.isLt) (by simpa using y.isLt)
  simp only [List.length_finRange] at e0
  have hc : x.val * k + y.val < (List.finRange 2 ×ˢ List.finRange k).length := by
    simp [List.length_product]; nlinarith [x.isLt, y.isLt]
  have e0' : (List.finRange 2 ×ˢ List.finRange k)[x.val * k + y.val] = (x, y) := by
    have := (List.getElem?_eq_some_iff.mp e0).2
    simpa using this
  have e1 := getElem?_product (List.finRange N) (List.finRange 2 ×ˢ List.finRange k)
    (x.val * k + y.val) z.val hc (by simpa using z.isLt)
  simp only [List.length_finRange] at e1
  rw [e0'] at e1
  simp only [enumT]
  rw [e1]; simp

theorem length_enumT {N k : ℕ} : (enumT N k).length = 2 * k * N := by
  simp [enumT, List.length_product]

/-! ### Repeated pushes and the odometer -/

theorem iter_push (l : LR) (r : SR) : ∀ (m : ℕ) (σ : St), (σ.ls l).length + m ≤ E.C →
    σ.sc r ≤ E.M → (exec E (.lpush l r))^[m] σ =
      { σ with ls := Function.update σ.ls l (σ.ls l ++ List.replicate m (σ.sc r)) }
  | 0, σ, _, _ => by simp
  | m + 1, σ, hC, hr => by
    rw [Function.iterate_succ_apply, exec_lpush_lt σ l r (by omega) hr,
      iter_push l r m { σ with ls := Function.update σ.ls l (σ.ls l ++ [σ.sc r]) }
        (by simp; omega) hr]
    simp [List.replicate_succ, List.append_assoc]

/-- The odometer of the terms `((r, e12), e2)` in the registers `47 48 49` (moduli `k = 2`,
`N = 5`). -/
def odoC : Code := .seq (.inc 49) (.ifLt 49 5 .skip (.seq (.zero 49) (.seq (.inc 48)
  (.ifLt 48 2 .skip (.seq (.zero 48) (.inc 47))))))

theorem exec_odoC {N k : ℕ} (σ : St) (x y z : ℕ) (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N)
    (h47 : σ.sc 47 = x) (h48 : σ.sc 48 = y) (h49 : σ.sc 49 = z) (hy : y < k) (hz : z < N)
    (hM : x + 1 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) :
    ∃ x' y' z', exec E odoC σ = setSL σ (Function.update (Function.update (Function.update σ.sc
        47 x') 48 y') 49 z') σ.ls ∧ (x' * k + y') * N + z' = (x * k + y) * N + z + 1 ∧
      y' < k ∧ z' < N := by
  by_cases hz' : z + 1 < N
  · refine ⟨x, y, z + 1, ?_, by ring, hy, hz'⟩
    simp only [odoC, exec_seq, exec_ifLt]
    simp [exec, h49, h5, h47, h48, min_eq_left (show z + 1 ≤ E.M by omega), hz', setSL,
      Function.update_apply]
    funext v; simp only [Function.update_apply]; split_ifs <;> simp_all
  · by_cases hy' : y + 1 < k
    · refine ⟨x, y + 1, 0, ?_, by have : z + 1 = N := by omega
                                  rw [← this]; ring, hy', by omega⟩
      simp only [odoC, exec_seq, exec_ifLt]
      simp [exec, h49, h5, h47, h48, h2, min_eq_left (show z + 1 ≤ E.M by omega),
        min_eq_left (show y + 1 ≤ E.M by omega), hz', hy', setSL, Function.update_apply]
      funext v; simp only [Function.update_apply]; split_ifs <;> simp_all
    · have e1 : N = z + 1 := by omega
      have e2 : k = y + 1 := by omega
      refine ⟨x + 1, 0, 0, ?_, by subst e1; subst e2; ring, by omega, by omega⟩
      simp only [odoC, exec_seq, exec_ifLt]
      simp [exec, h49, h5, h47, h48, h2, min_eq_left (show z + 1 ≤ E.M by omega),
        min_eq_left (show y + 1 ≤ E.M by omega), min_eq_left hM, hz', hy', setSL,
        Function.update_apply]
      funext v; simp only [Function.update_apply]; split_ifs <;> simp_all

end FhatGen

end SigabaNeo.Lattices
