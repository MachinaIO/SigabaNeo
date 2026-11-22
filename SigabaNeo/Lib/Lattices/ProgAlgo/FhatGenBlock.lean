import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenCoef

/-!
# Generating gate tapes: a NAND block

`blockC`: one `coefC` per output position `o` of `enumO` (held in the registers `43 … 46`,
advanced by the odometer `odoO`), appending its `k` wires to the list `21`; the list is then the
representation list (`repList`) of the block's output (`exec_blockC`: it is `nandBlockL`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-! ### Lengths -/

theorem foldl_modAdd_length {k K : ℕ} : ∀ (L : List (List (Wire ι))) (st : SLP ι × List (Wire ι)),
    st.2.length = k → (∀ a ∈ L, a.length = k) →
    (L.foldl (fun st b => modAdd (.gate 0) (2 ^ K) k st.1 st.2 b) st).2.length = k
  | [], st, h, _ => h
  | b :: L, st, h, hL => foldl_modAdd_length L _ (length_modAdd_eq _ _ _ _ _ _ h (hL b (by simp)))
      (fun x hx => hL x (by simp [hx]))

theorem foldSum_length {k K : ℕ} (P : SLP ι) (L : List (List (Wire ι)))
    (hL : ∀ a ∈ L, a.length = k) : (foldSum (.gate 0) (2 ^ K) k P L).2.length = k := by
  rcases L with _ | ⟨a, L⟩
  · simp [foldSum, constL_length]
  · exact foldl_modAdd_length L (P, a) (hL a (by simp)) (fun x hx => hL x (by simp [hx]))

theorem rounds_lengths {k K : ℕ} : ∀ (h : ℕ) (P : SLP ι) (L : List (List (Wire ι))),
    (∀ a ∈ L, a.length = k) → ∀ x ∈ (rounds (.gate 0) (2 ^ K) k h P L).2, x.length = k
  | 0, P, L, hL => hL
  | h + 1, P, L, hL => rounds_lengths h _ _ (pairRound_lengths P L hL)

theorem coefCircuitL_length {N k K : ℕ} (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2)
    (col : Fin 2 × Fin k) (t : Fin N) (P : SLP ι) :
    (coefCircuitL (ordT₀ N k) (.gate 0) (2 ^ K) repA repB Gv a col t P).2.length = k := by
  unfold coefCircuitL
  apply foldSum_length
  apply rounds_lengths
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact constL_length _ _ _
  · exact (leaves_lengths (K := K) repA repB a col t P (ordT₀ N k)).1 x hx

/-! ### The odometer of the output positions -/

/-- The odometer of `(a, (c1, c2), t)` in `43 … 46` (moduli `2 = 6`, `2 = 6`, `k = 2`, `N = 5`). -/
def odoO : Code := .seq (.inc 46) (.ifLt 46 5 .skip (.seq (.zero 46) (.seq (.inc 45)
  (.ifLt 45 2 .skip (.seq (.zero 45) (.seq (.inc 44) (.ifLt 44 6 .skip (.seq (.zero 44)
    (.inc 43)))))))))

theorem exec_odoO {N k : ℕ} (σ : St) (a c1 c2 t : ℕ) (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N)
    (h6 : σ.sc 6 = 2) (h43 : σ.sc 43 = a) (h44 : σ.sc 44 = c1) (h45 : σ.sc 45 = c2)
    (h46 : σ.sc 46 = t) (hc1 : c1 < 2) (hc2 : c2 < k) (ht : t < N)
    (hM : a + 1 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) (h2M : 2 ≤ E.M) :
    ∃ a' c1' c2' t', exec E odoO σ = setSL σ (Function.update (Function.update (Function.update
        (Function.update σ.sc 43 a') 44 c1') 45 c2') 46 t') σ.ls ∧
      ((a' * 2 + c1') * k + c2') * N + t' = ((a * 2 + c1) * k + c2) * N + t + 1 ∧
      c1' < 2 ∧ c2' < k ∧ t' < N := by
  have upd : ∀ (f : SR → ℕ) (x y z w : ℕ), Function.update (Function.update (Function.update
      (Function.update f 43 x) 44 y) 45 z) 46 w = fun r => if r = 46 then w else if r = 45 then z
        else if r = 44 then y else if r = 43 then x else f r := by
    intro f x y z w; funext r; simp only [Function.update_apply]
  by_cases ht' : t + 1 < N
  · refine ⟨a, c1, c2, t + 1, ?_, by ring, hc1, hc2, ht'⟩
    simp only [odoC, odoO, exec_seq, exec_ifLt]
    simp [exec, h46, h5, min_eq_left (show t + 1 ≤ E.M by omega), ht', setSL, upd, h43, h44, h45]
    funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
  · have eN : N = t + 1 := by omega
    by_cases hc2' : c2 + 1 < k
    · refine ⟨a, c1, c2 + 1, 0, ?_, by subst eN; ring, hc1, hc2', by omega⟩
      simp only [odoO, exec_seq, exec_ifLt]
      simp [exec, h46, h5, h45, h2, min_eq_left (show t + 1 ≤ E.M by omega),
        min_eq_left (show c2 + 1 ≤ E.M by omega), ht', hc2', setSL, h43, h44]
      funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
    · have ek : k = c2 + 1 := by omega
      by_cases hc1' : c1 + 1 < 2
      · refine ⟨a, c1 + 1, 0, 0, ?_, by subst eN; subst ek; ring, hc1', by omega, by omega⟩
        simp only [odoO, exec_seq, exec_ifLt]
        simp [exec, h46, h5, h45, h2, h44, h6, min_eq_left (show t + 1 ≤ E.M by omega),
          min_eq_left (show c2 + 1 ≤ E.M by omega), min_eq_left (show c1 + 1 ≤ E.M by omega),
          ht', hc2', hc1', setSL, h43]
        funext r; simp only [Function.update_apply]; split_ifs <;> simp_all
      · have e2 : c1 = 1 := by omega
        refine ⟨a + 1, 0, 0, 0, ?_, by subst eN; subst ek; subst e2; ring, by omega, by omega,
          by omega⟩
        subst e2
        simp only [odoO, exec_seq, exec_ifLt]
        simp [exec, h46, h5, h45, h2, h44, h6, h43, min_eq_left (show t + 1 ≤ E.M by omega),
          min_eq_left (show c2 + 1 ≤ E.M by omega), min_eq_left (show 1 + 1 ≤ E.M by omega),
          min_eq_left hM, ht', hc2', setSL]
        funext r; simp only [Function.update_apply]; split_ifs <;> simp_all

end FhatGen

end SigabaNeo.Lattices
