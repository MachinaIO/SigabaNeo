import SigabaNeoStd.Lattices.ProgAlgo.CoefBits

/-!
# BGG+ encodings of bits as a tape program

`bggEncP : Prog 72` computes, for a stream of bits `z_j`, a stream of rows `B_j` and a stream of
error rows `e_j` (rows of `L` ring words), the encodings `c_j = s · (B_j − z_j G̲) + e_j` (the
row `B_j`, minus the gadget row `G̲` when `z_j = 1`, times the ring word `s` (`matMulP`), plus the
error (`addRWP`)), shifted one after the other into the output register.

Tapes: `0` the output register; `1` the bits, `2` the rows `B_j`, `3` the errors (streams);
`4` `s`; `5` `G̲`; templates `6` (`K`), `7` (`N`), `8` (`N K`), `9` (length `1`), `10` (`L`),
`11` (`1 · L · N K`), `12` (`L · N`), `13` (the number of encodings), `22` (length `1`);
scratch `14 … 21`, `23 … 71`, blank before and after.

**`run_bggEncP`**: the output register receives `jStepE` iterated.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

/-- One encoding: (output register, bits, rows, errors). -/
def jStepE (N K L : ℕ) (sw ga : List Bool)
    (a : List Bool × List Bool × List Bool × List Bool) :
    List Bool × List Bool × List Bool × List Bool :=
  let R0 := takeD (1 * L * (N * K)) a.2.2.1
  let R := if hd a.2.1 = true then matSubW N K L R0 ga else R0
  let O := addRW (L * N) K (matMulW N K 1 1 L sw R) (takeD (1 * L * (N * K)) a.2.2.2)
  ((a.1 ++ takeD (1 * L * (N * K)) O).drop (1 * L * (N * K)), a.2.1.tail,
    a.2.2.1.drop (1 * L * (N * K)), a.2.2.2.drop (1 * L * (N * K)))

def mvBJ : Fin 5 → Fin 72 := ![2, 15, 20, 21, 11]
def mvEJ : Fin 5 → Fin 72 := ![3, 18, 20, 21, 11]
def mvOJ : Fin 5 → Fin 72 := ![19, 0, 20, 21, 11]
def vSubJ : Fin 28 → Fin 72 := ![16, 15, 5, 6, 12, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
def vAddJ : Fin 28 → Fin 72 := ![19, 17, 18, 6, 12, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]
def vMMJ : Fin 59 → Fin 72 := ![17, 4, 15, 6, 7, 8, 9, 22, 10, 11, 23, 24, 25, 26, 27, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54,
  55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71]

theorem mvBJ_inj : Function.Injective mvBJ := by decide
theorem mvEJ_inj : Function.Injective mvEJ := by decide
theorem mvOJ_inj : Function.Injective mvOJ := by decide
theorem vSubJ_inj : Function.Injective vSubJ := by decide
theorem vAddJ_inj : Function.Injective vAddJ := by decide
theorem vMMJ_inj : Function.Injective vMMJ := by decide

/-- One encoding. -/
def jBodyE : Prog 72 :=
  cp 15 11 ⨾ map mvBJ mvP ⨾ ifBit 1 (map vSubJ subRWP ⨾ cp 15 16 ⨾ clr 16) (nop 16) ⨾ tl 1 ⨾
    map vMMJ matMulP ⨾ cp 18 11 ⨾ map mvEJ mvP ⨾ map vAddJ addRWP ⨾ map mvOJ mvP ⨾ clr 15 ⨾
    clr 17 ⨾ clr 18 ⨾ clr 19

/-- **The BGG+ encodings of a stream of bits.** -/
def bggEncP : Prog 72 := forN 14 13 jBodyE

theorem noGrow_bggEncP : bggEncP.NoGrow := rfl
theorem wf_bggEncP : bggEncP.WF := wf_of_wfB (by decide)

def jGE (S : Store 72) : List Bool × List Bool × List Bool × List Bool → Store 72
  | (out, zs, bjs, ejs) =>
    Function.update (Function.update (Function.update (Function.update S 0 out) 1 zs) 2 bjs) 3 ejs

/-- The scratch is blank. -/
def JEClean (S : Store 72) : Prop := ∀ i : Fin 72, (14 ≤ i.val ∧ i.val ≤ 21) ∨ 23 ≤ i.val → S i = []

set_option maxHeartbeats 8000000 in
theorem run_jBodyE {N K L : ℕ} (S : Store 72) (hS : JEClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : (S 8).length = N * K) (h9 : (S 9).length = 1)
    (h22 : (S 22).length = 1) (hL : (S 10).length = L) (hR : (S 11).length = 1 * L * (N * K))
    (hLN : (S 12).length = L * N) (hs : (S 4).length = N * K) (hg : (S 5).length = L * N * K)
    (a) (w : List Bool) :
    run jBodyE (Function.update (jGE S a) 14 w) =
      Function.update (jGE S (jStepE N K L (S 4) (S 5) a)) 14 w := by
  obtain ⟨out, zs, bjs, ejs⟩ := a
  have hS : ∀ i : Fin 72, (14 ≤ i.val ∧ i.val ≤ 21) ∨ 23 ≤ i.val → S i = [] := hS
  have hRL : 1 * L * (N * K) = L * N * K := by ring
  have hRl' : (S 11).length = L * N * K := by rw [hR, hRL]
  simp only [jBodyE, run_seq, run_copy, run_clear, run_tail, run_ifBit]
  rw [run_mvP_map mvBJ_inj _ (by simp [mvBJ, jGE, hS]) (by simp [mvBJ, jGE, hS])]
  have hR0 : (S 11 ++ takeD (S 11).length bjs).drop (S 11).length = takeD (1 * L * (N * K)) bjs := by
    rw [List.drop_left' rfl, hR]
  have hE0 : (S 11 ++ takeD (S 11).length ejs).drop (S 11).length = takeD (1 * L * (N * K)) ejs := by
    rw [List.drop_left' rfl, hR]
  have hlR0 : (takeD (1 * L * (N * K)) bjs).length = L * N * K := by rw [length_takeD, hRL]
  have hms : (matSubW N K L (takeD (L * N * K) bjs) (S 5)).length = L * N * K := by
    rw [matSubW_eq_subRW, length_subRW (L * N) K (by simp)]
  by_cases hz : hd zs = true
  · simp only [mvBJ, jGE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Function.update_apply, hz, ↓reduceIte]
    rw [run_subRWP_mat_map vSubJ_inj (K := K) (N := N) (L := L) _ ?_ ?_ ?_ ?_ ?_]
    rw [run_matMulP_map vMMJ_inj (K := K) (N := N) (m := 1) (n := 1) (l := L) _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_]
    rw [run_mvP_map mvEJ_inj _ ?_ ?_]
    rw [run_addRWP_map vAddJ_inj (K := K) (N := L * N) _ ?_ ?_ ?_ ?_ ?_]
    rw [run_mvP_map mvOJ_inj _ ?_ ?_]
    · funext t
      fin_cases t <;> simp [mvEJ, mvOJ, vSubJ, vMMJ, vAddJ, jStepE, hz, hS, hR, hR0, hE0]
    all_goals first
      | exact hms
      | (rw [hRL]; exact hms)
      | (intro i hi; fin_cases i <;> simp [mvEJ, mvOJ, vSubJ, vMMJ, vAddJ, hS, hz] at hi ⊢)
      | (simp [mvEJ, mvOJ, vSubJ, vMMJ, vAddJ, hS, hK, hN, hNK, h9, h22, hL, hR, hLN, hs, hg, hR0,
          hE0, hRL, length_matMulW, hms, hz]; done)
      | (simp [mvEJ, mvOJ, vSubJ, vMMJ, vAddJ, hS, hK, hN, hNK, h9, h22, hL, hR, hLN, hs, hg, hR0,
          hE0, hRL, length_matMulW, hz]
         first
          | exact hms
          | (rw [matSubW_eq_subRW, length_subRW (L * N) K (by simp; ring)]; try ring)
          | (ring_nf; done))
  · simp only [mvBJ, jGE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Function.update_apply, hz, ↓reduceIte, run_nop]
    rw [run_matMulP_map vMMJ_inj (K := K) (N := N) (m := 1) (n := 1) (l := L) _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_]
    rw [run_mvP_map mvEJ_inj _ ?_ ?_]
    rw [run_addRWP_map vAddJ_inj (K := K) (N := L * N) _ ?_ ?_ ?_ ?_ ?_]
    rw [run_mvP_map mvOJ_inj _ ?_ ?_]
    · funext t
      fin_cases t <;> simp [mvEJ, mvOJ, vMMJ, vAddJ, jStepE, hz, hS, hR, hR0, hE0]
    all_goals first
      | (intro i hi; fin_cases i <;> simp [mvEJ, mvOJ, vMMJ, vAddJ, hS, hz] at hi ⊢)
      | (simp [mvEJ, mvOJ, vMMJ, vAddJ, hS, hK, hN, hNK, h9, h22, hL, hR, hLN, hs, hg, hR0,
          hE0, hRL, length_matMulW, hz]; try ring_nf)

/-- **The BGG+ encodings**: after `|s 13|` rounds. -/
theorem run_bggEncP {N K L : ℕ} (S : Store 72) (hS : JEClean S) (hK : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : (S 8).length = N * K) (h9 : (S 9).length = 1)
    (h22 : (S 22).length = 1) (hL : (S 10).length = L) (hR : (S 11).length = 1 * L * (N * K))
    (hLN : (S 12).length = L * N) (hs : (S 4).length = N * K) (hg : (S 5).length = L * N * K) :
    run bggEncP S = jGE S ((jStepE N K L (S 4) (S 5))^[(S 13).length] (S 0, S 1, S 2, S 3)) := by
  have h := run_forN 14 13 jBodyE (jGE S) (jStepE N K L (S 4) (S 5))
    (fun a w => run_jBodyE S hS hK hN hNK h9 h22 hL hR hLN hs hg a w) (S 0, S 1, S 2, S 3) S
    (by funext t; simp only [jGE]; fin_cases t <;> simp)
  rw [bggEncP, h]
  have hS : ∀ i : Fin 72, (14 ≤ i.val ∧ i.val ≤ 21) ∨ 23 ≤ i.val → S i = [] := hS
  funext t
  simp only [jGE]
  fin_cases t <;> simp [hS]

end Prog

end SigabaNeo.Tape
