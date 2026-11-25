import SigabaNeoStd.Lattices.ProgAlgo.Gadget
import SigabaNeoStd.Lattices.ProgAlgo.MatMul

/-!
# The BGG+ NAND of public keys on words as a tape program

`nandP : Prog 65` computes `nandPKW N K k a b = G̲ − a · G̲⁻¹(b)` (`run_nandP`), composing `gadP`,
`ginvP`, `matMulP` and `subRWP`. Tapes: `0` output, `1` `a`, `2` `b` (rows of `2k` ring entries),
templates `3` … `11` of lengths `K`, `N`, `N · K`, `k`, `2k`, `1`, `2k · N`, `2k · N · K`,
`2k · 2k · N · K`; scratch `12 … 64`, blank before and after.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

theorem length_digitRW (N K i : ℕ) (w : List Bool) : (digitRW N K i w).length = N * K :=
  length_concatN fun _ _ => length_bitW K _

theorem length_ginvW (N K k : ℕ) (b : List Bool) :
    (ginvW N K k b).length = 2 * k * (2 * k * (N * K)) := by
  rw [ginvW_eq, List.length_append, length_concatN (K := 2 * k * N * K)
    (fun r _ => length_digitRW _ _ _ _), List.length_replicate]
  ring

theorem length_gadW (N K k : ℕ) : (gadW N K k).length = 2 * k * (N * K) := by
  rw [gadW_eq, List.length_append, length_concatN (K := N * K)
    (fun p _ => Prog.length_constW (Prog.length_powW K p)), List.length_replicate]
  ring

theorem length_matMulW (N K m n l : ℕ) (x y : List Bool) :
    (matMulW N K m n l x y).length = m * l * (N * K) :=
  length_concatN fun _ _ => length_sumLoop _ _ _ _

namespace Prog

open scoped Prog

theorem run_gadP_map {u : Fin 21 → Fin k} (hu : Function.Injective u) {K N k' : ℕ} (s : Store k)
    (hs : ∀ i : Fin 21, 6 ≤ i.val → s (u i) = []) (hK : (s (u 1)).length = K)
    (hN : (s (u 2)).length = N) (hNK : (s (u 3)).length = N * K) (hk : (s (u 4)).length = k')
    (hO : (s (u 5)).length = 2 * k' * (N * K)) :
    run (map u gadP) s = Function.update s (u 0) (gadW N K k') :=
  run_map_eq_update hu _ s 0 _ (run_gadP (s ∘ u) hs hK hN hNK hk hO)

theorem run_ginvP_map {u : Fin 35 → Fin k} (hu : Function.Injective u) {K N k' : ℕ} (s : Store k)
    (hs : ∀ i : Fin 35, 6 ≤ i.val → s (u i) = []) (hK : (s (u 2)).length = K)
    (hB : (s (u 3)).length = 2 * k' * N) (hk : (s (u 4)).length = k')
    (hO : (s (u 5)).length = 2 * k' * (2 * k' * (N * K)))
    (hb : (s (u 1)).length = 2 * k' * (N * K)) :
    run (map u ginvP) s = Function.update s (u 0) (ginvW N K k' (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_ginvP (s ∘ u) hs hK hB hk hO hb)

theorem run_matMulP_map {u : Fin 59 → Fin k} (hu : Function.Injective u) {K N m n l : ℕ}
    (s : Store k) (hs : ∀ i : Fin 59, 10 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hNK : (s (u 5)).length = N * K) (hm : (s (u 6)).length = m)
    (hn : (s (u 7)).length = n) (hl : (s (u 8)).length = l)
    (hO : (s (u 9)).length = m * l * (N * K)) (hx : (s (u 1)).length = m * n * (N * K))
    (hy : (s (u 2)).length = n * l * (N * K)) :
    run (map u matMulP) s = Function.update s (u 0) (matMulW N K m n l (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_matMulP (s ∘ u) hs hK hN hNK hm hn hl hO hx hy)

theorem run_subRWP_mat_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N L : ℕ}
    (s : Store k) (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hLN : (s (u 4)).length = L * N) (hx : (s (u 1)).length = L * N * K)
    (hy : (s (u 2)).length = L * N * K) :
    run (map u subRWP) s = Function.update s (u 0) (matSubW N K L (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_subRWP_mat (s ∘ u) hs hK hLN hx hy)

def vGad : Fin 21 → Fin 65 := ![12, 3, 4, 5, 6, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
def vGinv : Fin 35 → Fin 65 := ![13, 2, 3, 9, 6, 11, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def vMat : Fin 59 → Fin 65 := ![14, 1, 13, 3, 4, 5, 8, 7, 15, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]
def vSubN : Fin 28 → Fin 65 := ![0, 12, 14, 3, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
theorem vGad_inj : Function.Injective vGad := by decide
theorem vGinv_inj : Function.Injective vGinv := by decide
theorem vMat_inj : Function.Injective vMat := by decide
theorem vSubN_inj : Function.Injective vSubN := by decide

/-- **The BGG+ NAND of public keys.** Tapes `12` `G̲`, `13` `G̲⁻¹(b)`, `14` the product, `15` a copy
of the template of length `2k`; `16 … 64` scratch. -/
def nandP : Prog 65 :=
  map vGad gadP ⨾ map vGinv ginvP ⨾ cp 15 7 ⨾ map vMat matMulP ⨾ map vSubN subRWP ⨾ clr 12 ⨾
    clr 13 ⨾ clr 14 ⨾ clr 15

set_option linter.unusedSimpArgs false in
theorem run_nandP {K N k' : ℕ} (s : Store 65) (hs : ∀ i : Fin 65, 12 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hk : (s 6).length = k') (h2k : (s 7).length = 2 * k') (h1 : (s 8).length = 1)
    (hB : (s 9).length = 2 * k' * N) (hRow : (s 10).length = 2 * k' * (N * K))
    (hSq : (s 11).length = 2 * k' * (2 * k' * (N * K))) (ha : (s 1).length = 2 * k' * (N * K))
    (hb : (s 2).length = 2 * k' * (N * K)) :
    run nandP s = Function.update s 0 (nandPKW N K k' (s 1) (s 2)) := by
  simp only [nandP, run_seq, run_copy, run_clear]
  rw [run_gadP_map vGad_inj (K := K) (N := N) (k' := k') _ ?_ ?_ ?_ ?_ ?_ ?_,
    run_ginvP_map vGinv_inj (K := K) (N := N) (k' := k') _ ?_ ?_ ?_ ?_ ?_ ?_,
    run_matMulP_map vMat_inj (K := K) (N := N) (m := 1) (n := 2 * k') (l := 2 * k') _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_,
    run_subRWP_mat_map vSubN_inj (K := K) (N := N) (L := 1 * (2 * k')) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    fin_cases t <;> simp [vGad, vGinv, vMat, vSubN, hs, nandPKW]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vGad, vGinv, vMat, vSubN, hs] at hi ⊢)
    | (simp [vGad, vGinv, vMat, vSubN, hs, hK, hN, hNK, hk, h2k, h1, hB, hRow, hSq, ha, hb,
        length_gadW, length_ginvW, length_matMulW]; try ring)

theorem noGrow_nandP : nandP.NoGrow := rfl
theorem wf_nandP : nandP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
