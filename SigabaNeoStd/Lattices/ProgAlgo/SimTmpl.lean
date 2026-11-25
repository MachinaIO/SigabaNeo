import SigabaNeoStd.Lattices.ProgAlgo.SimSLP

/-!
# The content templates of the simulation step

`simTmplP : Prog 31` writes the content templates of `simStepP` (`SimPre`): the gadget rows
`gadW N K k` (top-row gadget, tape `0`) and `gswGadW N K k` (Ring-GSW gadget, tape `1`, built as
`gadW ++ zeroW (k N K) ++ (gadW).take (k N K)` by shifting into a register, `gswGadW_eq`), the zero
word `zeroW Lw` (tape `2`) and the one word `oneW N K` (tape `3`) (`run_simTmplP`).

Tapes: outputs `0` … `3`; templates `4` … `11` of lengths `K`, `N`, `N K`, `k`, `2k N K`,
`2 · 2k N K`, `k N K`, `Lw`; scratch `12` … `30`, blank before and after.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

variable {k : ℕ}

def tmG : Fin 21 → Fin 31 := ![0, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
def tmMv1 : Fin 5 → Fin 31 := ![27, 1, 12, 13, 8]
def tmFl : Fin 3 → Fin 31 := ![1, 12, 10]
def tmMv2 : Fin 5 → Fin 31 := ![27, 1, 12, 13, 10]
def tmOne : Fin 11 → Fin 31 := ![29, 30, 28, 4, 12, 13, 14, 15, 16, 17, 18]
def tmC : Fin 12 → Fin 31 := ![3, 29, 30, 4, 5, 6, 12, 13, 14, 15, 16, 17]
theorem tmG_inj : Function.Injective tmG := by decide
theorem tmMv1_inj : Function.Injective tmMv1 := by decide
theorem tmFl_inj : Function.Injective tmFl := by decide
theorem tmMv2_inj : Function.Injective tmMv2 := by decide
theorem tmOne_inj : Function.Injective tmOne := by decide
theorem tmC_inj : Function.Injective tmC := by decide

attribute [local simp] tmG tmMv1 tmFl tmMv2 tmOne tmC

/-- **The content templates** of the simulation step. -/
def simTmplP : Prog 31 :=
  map tmG gadP ⨾ cp 1 9 ⨾ cp 27 0 ⨾ map tmMv1 mvP ⨾ map tmFl (fillP false) ⨾ cp 27 0 ⨾
    map tmMv2 mvP ⨾ clr 27 ⨾ cp 2 11 ⨾ setZero 2 ⨾ cp 28 4 ⨾ setZero 28 ⨾
    map tmOne (zipW oneOp true) ⨾ map tmC monoWP ⨾ clr 28 ⨾ clr 29

theorem serF_oneOp_powW (K : ℕ) (y : List Bool) :
    serF oneOp true (List.replicate K false) y = powW K 0 := by
  rw [serF_oneOp, powW_zero]
  cases K with
  | zero => rfl
  | succ K => rw [List.replicate_succ]; simp [bitW, zeroW]

/-- The Ring-GSW gadget row, shifted into a register of its length. -/
theorem gsw_shift (N K k : ℕ) (T : List Bool) (hT : T.length = 2 * (2 * k) * (N * K)) :
    (((T ++ takeD (2 * k * (N * K)) (gadW N K k)).drop (2 * k * (N * K)) ++
        List.replicate (k * (N * K)) false).drop (k * (N * K)) ++
      takeD (k * (N * K)) (gadW N K k)).drop (k * (N * K)) = gswGadW N K k := by
  have hg := length_gadW N K k
  set a := 2 * k * (N * K)
  set b := k * (N * K)
  have ha : a = b + b := by simp only [a, b]; ring
  have hT' : T.length = a + a := by rw [hT]; ring
  have e1 : (T ++ takeD a (gadW N K k)).drop a = T.drop a ++ gadW N K k := by
    rw [List.drop_append_of_le_length (by omega), takeD_of_length' hg]
  have e2 : (T.drop a ++ gadW N K k ++ List.replicate b false).drop b =
      (T.drop a).drop b ++ (gadW N K k ++ List.replicate b false) := by
    rw [List.append_assoc, List.drop_append_of_le_length (by simp; omega)]
  have e3 : ((T.drop a).drop b ++ (gadW N K k ++ List.replicate b false) ++
      takeD b (gadW N K k)).drop b =
      gadW N K k ++ List.replicate b false ++ takeD b (gadW N K k) := by
    rw [List.append_assoc, List.drop_left' (by simp; omega), List.append_assoc]
  rw [e1, e2, e3, takeD_eq_take (by rw [hg]; omega), gswGadW_eq]
  simp [zeroW, b]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **`simTmplP` writes the templates** `gadW`, `gswGadW`, `zeroW Lw`, `oneW`. -/
theorem run_simTmplP {N K k Lw : ℕ} (s : Store 31) (hb : ∀ t : Fin 31, 12 ≤ t.val → s t = [])
    (h4 : (s 4).length = K) (h5 : (s 5).length = N) (h6 : (s 6).length = N * K)
    (h7 : (s 7).length = k) (h8 : (s 8).length = 2 * k * (N * K))
    (h9 : (s 9).length = 2 * (2 * k) * (N * K)) (h10 : (s 10).length = k * (N * K))
    (h11 : (s 11).length = Lw) :
    run simTmplP s = Function.update (Function.update (Function.update (Function.update s 0
      (gadW N K k)) 1 (gswGadW N K k)) 2 (zeroW Lw)) 3 (oneW N K) := by
  simp only [simTmplP, run_seq, run_copy, run_clear, run_setZero]
  rw [run_map_eq_update tmG_inj gadP _ 0 _ (run_gadP (N := N) (K := K) (k := k) _
    (fun t ht => by fin_cases t <;> simp at ht ⊢ <;> (apply hb; decide))
    (by simp [h4]) (by simp [h5]) (by simp [h6]) (by simp [h7]) (by simp [h8]))]
  rw [run_mvP_map tmMv1_inj _ (by simp [hb 12 (by decide)]) (by simp [hb 13 (by decide)])]
  rw [run_fillP_map tmFl_inj _ _ (by simp [hb 12 (by decide)])]
  rw [run_mvP_map tmMv2_inj _ (by simp [hb 12 (by decide)]) (by simp [hb 13 (by decide)])]
  rw [run_zipW_map tmOne_inj _ _ _ (fun t ht => by fin_cases t <;> simp at ht ⊢ <;> (apply hb; decide))
    (by simp [hb 30 (by decide)])]
  rw [run_map_eq_update tmC_inj monoWP _ 0 _ (run_monoWP_const (N := N) (K := K) _
    (fun t ht => by fin_cases t <;> simp at ht ⊢ <;> (apply hb; decide))
    (by simp [h4, serF_oneOp_powW, length_powW]) (by simp [hb 30 (by decide)]) (by simp [h4])
    (by simp [h5]) (by simp [h6]))]
  funext t
  fin_cases t <;> simp [h8, h10, h11, h4, zeroW, serF_oneOp_powW, powW_zero, oneW]
  · exact gsw_shift N K k (s 9) h9
  all_goals (apply hb; decide)

end Prog

end SigabaNeo.Tape
