import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncDigits
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncGc
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncCb

/-!
# The phases of `Enc` modulo `2^K − 1` for one exponent `t`

* **`hBlkP : Prog 69`** (`run_hBlkP`): the two helper rows of `g_t^{±1}`:
  `s H_k − (σ^{T}(s), 1) G + e_k` for `T = |5|` then `T = |6|` (`σ = σ_g`, `g = |4|`), from the
  matrix stream `2` and the error stream `3` (consumed), shifted into the output register `0`.
  Tapes: `0` output, `1` `s`, `2` `H`, `3` `e`, `4` `g`, `5` `T₁`, `6` `T₂`, `7` the word of `1`,
  templates `8` (`K`), `9` (`N`), `10` (`N K`), `11` (`2 K`), `12` (`K − 1`), `13` (`2 K · N K`),
  `14` (`2 K · N K`), `15` (`4 K · N K`); scratch `16 … 68`.
* **`autBlkP : Prog 85`** (`run_autBlkP`): the digit encodings of `C_t = σ^{T₁}(H') − [0; σ^{T₁}(h')]`
  (`H'` the second matrix of the stream `2`, `h'` its helper row `s H' − (σ^{T₂}(s), 1) G + e'`, `e'`
  the second row of the stream `3`) under the secret `σ^{T₁}(s)`, with the matrix stream `4` and the
  error stream `5` (`deP`). Tapes: `0` output, `1` `s`, `2` `H`, `3` `e_h`, `4` `A`, `5` `E`, `6` `g`,
  `7` `T₁`, `8` `T₂`, `9` the word of `1`, templates `10` (`K`), `11` (`N`), `12` (`N K`), `13`
  (`2 K`), `14` (`K − 1`), `15` (`2 K · N K`), `16` (`2 K · N K`), `17` (`4 K · N K`), `18` (length
  `1`), `19` (`4 K`); scratch `20 … 84`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The helper row with secret word `sk`: `rowW` with the gadget term of `(sk, 1)`. -/
def hRow (N K : ℕ) (s sk one H E : List Bool) : List Bool :=
  rowW N K (K + K) s H (H.drop ((K + K) * (N * K))) (Prog.zStream N K one sk) E

namespace Prog

open scoped Prog

theorem run_mrowP_map {u : Fin 66 → Fin k} (hu : Function.Injective u) {K N L : ℕ} (hK : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 66, 14 ≤ i.val → s (u i) = []) (hK' : (s (u 6)).length = K)
    (hN : (s (u 7)).length = N) (hNK : (s (u 8)).length = N * K) (hL : (s (u 9)).length = L)
    (hK1 : (s (u 10)).length = K - 1) (h11 : (s (u 11)).length = (K + K) * (N * K))
    (h12 : (s (u 12)).length = L * (N * K)) (h13 : (s (u 13)).length = (L + L) * (N * K))
    (h1 : (s (u 1)).length = N * K) (hu' : (s (u 3)).length = N * K) :
    run (map u mrowP) s = Function.update (Function.update (Function.update s (u 0)
      ((s (u 0) ++ rowW N K L (s (u 1)) (s (u 4)) ((s (u 4)).drop (L * (N * K)))
        (zStream N K (s (u 3)) (s (u 2))) (s (u 5))).drop (L * (N * K)))) (u 4)
          ((s (u 4)).drop ((L + L) * (N * K)))) (u 5) ((s (u 5)).drop (L * (N * K))) := by
  rw [run_map hu, run_mrowP hK (s ∘ u) hs hK' hN hNK hL hK1 h11 h12 h13 h1 hu',
    extend_update hu, extend_update hu, extend_update hu, extend_comp_self]
  rfl

/-! ### The helper rows -/

def hA1 : Fin 27 → Fin 69 := ![16, 4, 5, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
  30, 31, 32, 33, 34, 35, 36, 37, 38]
def hA2 : Fin 27 → Fin 69 := ![16, 4, 6, 8, 9, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
  30, 31, 32, 33, 34, 35, 36, 37, 38]
def hR : Fin 66 → Fin 69 := ![0, 1, 16, 7, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21,
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
  46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
def hR2 : Fin 66 → Fin 69 := ![0, 1, 16, 7, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21,
  22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
  46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]

set_option maxRecDepth 10000 in
theorem hA1_inj : Function.Injective hA1 := by decide
set_option maxRecDepth 10000 in
theorem hA2_inj : Function.Injective hA2 := by decide
set_option maxRecDepth 10000 in
theorem hR_inj : Function.Injective hR := by decide
set_option maxRecDepth 10000 in
theorem hR2_inj : Function.Injective hR2 := by decide

/-- **The two helper rows of one exponent.** -/
def hBlkP : Prog 69 :=
  cp 16 1 ⨾ map hA1 autItP ⨾ map hR mrowP ⨾ cp 16 1 ⨾ map hA2 autItP ⨾ map hR2 mrowP ⨾ clr 16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_hBlkP {K N : ℕ} (hK : 0 < K) (hN0 : 0 < N) (s : Store 69)
    (hs : ∀ i : Fin 69, 16 ≤ i.val → s i = []) (hK' : (s 8).length = K) (hN : (s 9).length = N)
    (hNK : (s 10).length = N * K) (h11 : (s 11).length = K + K) (hK1 : (s 12).length = K - 1)
    (h13 : (s 13).length = (K + K) * (N * K)) (h14 : (s 14).length = (K + K) * (N * K))
    (h15 : (s 15).length = (K + K + (K + K)) * (N * K)) (h1 : (s 1).length = N * K)
    (h7 : (s 7).length = N * K) :
    run hBlkP s = Function.update (Function.update (Function.update s 0
      ((((s 0 ++ hRow N K (s 1) (autTW N K (s 4).length (s 5).length (s 1)) (s 7) (s 2) (s 3)).drop
        ((K + K) * (N * K))) ++ hRow N K (s 1) (autTW N K (s 4).length (s 6).length (s 1)) (s 7)
          ((s 2).drop ((K + K + (K + K)) * (N * K))) ((s 3).drop ((K + K) * (N * K)))).drop
            ((K + K) * (N * K)))) 2 (((s 2).drop ((K + K + (K + K)) * (N * K))).drop
              ((K + K + (K + K)) * (N * K)))) 3 (((s 3).drop ((K + K) * (N * K))).drop
                ((K + K) * (N * K))) := by
  have l1 := length_autTW (g := (s 4).length) hN0 h1 (s 5).length
  have l2 := length_autTW (g := (s 4).length) hN0 h1 (s 6).length
  simp only [autTW] at l1 l2
  simp only [hBlkP, run_seq, run_copy, run_clear]
  rw [run_autItP_map hA1_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [hA1, hs] at hi ⊢
  · simp [hA1, hK']
  · simp [hA1, hN]
  · simp [hA1, h1]
  rw [run_mrowP_map hR_inj (K := K) (N := N) (L := K + K) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [hR, hA1, hs] at hi ⊢
  all_goals try (simp [hR, hA1, hK', hN, hNK, h11, hK1, h13, h14, h15, h1, h7]; done)
  rw [run_autItP_map hA2_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [hA2, hR, hA1, hs] at hi ⊢
  · simp [hA2, hR, hA1, hK']
  · simp [hA2, hR, hA1, hN]
  · simp [hA2, hR, hA1, h1]
  rw [run_mrowP_map hR2_inj (K := K) (N := N) (L := K + K) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [hR2, hR, hA2, hA1, hs] at hi ⊢
  all_goals try (simp [hR2, hR, hA2, hA1, hK', hN, hNK, h11, hK1, h13, h14, h15, h1, h7]; done)
  funext t
  fin_cases t <;> simp [hR2, hR, hA2, hA1, hs, hRow, autTW]

theorem noGrow_hBlkP : hBlkP.NoGrow := rfl
set_option maxRecDepth 100000 in
theorem wf_hBlkP : hBlkP.WF := wf_of_wfB (by decide)

/-! ### The digit encodings of `C_t` -/

theorem run_gcAutP_map {u : Fin 60 → Fin k} (hu : Function.Injective u) {K N : ℕ} (hK : 0 < K)
    (hN0 : 0 < N) (s : Store k) (hs : ∀ i : Fin 60, 9 ≤ i.val → s (u i) = [])
    (hK' : (s (u 5)).length = K) (hN : (s (u 6)).length = N) (hNK : (s (u 7)).length = N * K) :
    run (map u gcAutP) s =
      let c0 := (gc0Step N K (s (u 3)).length (s (u 4)).length)^[(s (u 8)).length] (s (u 0), s (u 1))
      let c1 := (gc1Step N K (s (u 3)).length (s (u 4)).length)^[(s (u 8)).length]
        (c0.1, c0.2, s (u 2))
      Function.update (Function.update (Function.update s (u 0) c1.1) (u 1) c1.2.1) (u 2) c1.2.2 := by
  rw [run_map hu, run_gcAutP hK hN0 (s ∘ u) hs hK' hN hNK]
  simp only [Function.comp_apply]
  generalize (gc1Step N K (s (u 3)).length (s (u 4)).length)^[(s (u 8)).length]
    (((gc0Step N K (s (u 3)).length (s (u 4)).length)^[(s (u 8)).length] (s (u 0), s (u 1))).1,
     ((gc0Step N K (s (u 3)).length (s (u 4)).length)^[(s (u 8)).length] (s (u 0), s (u 1))).2,
      s (u 2)) = r
  obtain ⟨C, H, h⟩ := r
  simp only [g1G]
  rw [extend_update hu, extend_update hu, extend_update hu, extend_comp_self]

theorem run_deP_map {u : Fin 74 → Fin k} (hu : Function.Injective u) {K N L : ℕ} (hK : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 74, 15 ≤ i.val → s (u i) = [])
    (hK' : (s (u 5)).length = K) (hN : (s (u 6)).length = N) (hNK : (s (u 7)).length = N * K)
    (hL : (s (u 8)).length = L) (hK1 : (s (u 9)).length = K - 1)
    (h10 : (s (u 10)).length = (K + K) * (N * K)) (h11 : (s (u 11)).length = L * (N * K))
    (h12 : (s (u 12)).length = (L + L) * (N * K)) (h13 : (s (u 13)).length = 1)
    (h1 : (s (u 1)).length = N * K) :
    run (map u deP) s =
      let r := (deOut N K L (s (u 1)))^[(s (u 14)).length] (s (u 2), s (u 0), s (u 3), s (u 4))
      Function.update (Function.update (Function.update (Function.update s (u 2) r.1) (u 0) r.2.1)
        (u 3) r.2.2.1) (u 4) r.2.2.2 := by
  rw [run_map hu, run_deP hK (s ∘ u) hs hK' hN hNK hL hK1 h10 h11 h12 h13 h1]
  simp only [Function.comp_apply]
  generalize (deOut N K L (s (u 1)))^[(s (u 14)).length] (s (u 2), s (u 0), s (u 3), s (u 4)) = r
  obtain ⟨C, o, A, E⟩ := r
  simp only [eG]
  rw [extend_update hu, extend_update hu, extend_update hu, extend_update hu, extend_comp_self]

def aD1 : Fin 3 → Fin 85 := ![2, 25, 17]
def aD2 : Fin 3 → Fin 85 := ![3, 25, 16]
def aAk : Fin 27 → Fin 85 := ![21, 6, 8, 10, 11, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
def aR : Fin 66 → Fin 85 := ![22, 1, 21, 9, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]
def aAt : Fin 27 → Fin 85 := ![23, 6, 7, 10, 11, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
def aG : Fin 60 → Fin 85 := ![24, 20, 22, 6, 7, 10, 11, 12, 13, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75]
def aDE : Fin 74 → Fin 85 := ![0, 23, 24, 4, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83]

set_option maxRecDepth 10000 in
theorem aD1_inj : Function.Injective aD1 := by decide
set_option maxRecDepth 10000 in
theorem aD2_inj : Function.Injective aD2 := by decide
set_option maxRecDepth 10000 in
theorem aAk_inj : Function.Injective aAk := by decide
set_option maxRecDepth 10000 in
theorem aR_inj : Function.Injective aR := by decide
set_option maxRecDepth 10000 in
theorem aAt_inj : Function.Injective aAt := by decide
set_option maxRecDepth 10000 in
theorem aG_inj : Function.Injective aG := by decide
set_option maxRecDepth 10000 in
theorem aDE_inj : Function.Injective aDE := by decide

/-- **The digit encodings of `C_t`.** -/
def autBlkP : Prog 85 :=
  map aD1 dropP ⨾ map aD2 dropP ⨾ cp 20 2 ⨾ cp 21 1 ⨾ map aAk autItP ⨾ cp 22 15 ⨾ map aR mrowP ⨾
    cp 23 1 ⨾ map aAt autItP ⨾ cp 24 17 ⨾ map aG gcAutP ⨾ map aDE deP ⨾ clr 20 ⨾ clr 21 ⨾ clr 22 ⨾
    clr 23 ⨾ clr 24

/-- The output of `autBlkP` (output register, the four streams). -/
def autOut (N K g T₁ T₂ : ℕ) (s one H Eh z2 z4 nE out A E : List Bool) :
    List Bool × List Bool × List Bool × List Bool × List Bool :=
  let H' := H.drop ((K + K + (K + K)) * (N * K))
  let E' := Eh.drop ((K + K) * (N * K))
  let hR := (z2 ++ hRow N K s (autTW N K g T₂ s) one H' E').drop ((K + K) * (N * K))
  let c0 := (gc0Step N K g T₁)^[K + K] (z4, H')
  let C := ((gc1Step N K g T₁)^[K + K] (c0.1, c0.2, hR)).1
  let r := (deOut N K (K + K) (autTW N K g T₁ s))^[nE.length] (C, out, A, E)
  (r.2.1, H'.drop ((K + K + (K + K)) * (N * K)), E'.drop ((K + K) * (N * K)), r.2.2.1, r.2.2.2)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
theorem run_autBlkP {K N : ℕ} (hK : 0 < K) (hN0 : 0 < N) (s : Store 85)
    (hs : ∀ i : Fin 85, 20 ≤ i.val → s i = []) (hK' : (s 10).length = K) (hN : (s 11).length = N)
    (hNK : (s 12).length = N * K) (h13 : (s 13).length = K + K) (hK1 : (s 14).length = K - 1)
    (h15 : (s 15).length = (K + K) * (N * K)) (h16 : (s 16).length = (K + K) * (N * K))
    (h17 : (s 17).length = (K + K + (K + K)) * (N * K)) (h18 : (s 18).length = 1)
    (h1 : (s 1).length = N * K) (h9 : (s 9).length = N * K) :
    run autBlkP s =
      let o := autOut N K (s 6).length (s 7).length (s 8).length (s 1) (s 9) (s 2) (s 3) (s 15)
        (s 17) (s 19) (s 0) (s 4) (s 5)
      Function.update (Function.update (Function.update (Function.update (Function.update s 0 o.1)
        2 o.2.1) 3 o.2.2.1) 4 o.2.2.2.1) 5 o.2.2.2.2 := by
  have l1 := length_autTW (g := (s 6).length) hN0 h1 (s 7).length
  have l2 := length_autTW (g := (s 6).length) hN0 h1 (s 8).length
  simp only [autTW] at l1 l2
  simp only [autBlkP, run_seq, run_copy, run_clear]
  rw [run_dropP_map aD1_inj _ (by simp [aD1, hs]), run_dropP_map aD2_inj _ (by simp [aD2, aD1, hs])]
  rw [run_autItP_map aAk_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [aAk, aD2, aD1, hs] at hi ⊢
  all_goals try (simp [aAk, aD2, aD1, hK', hN, h1]; done)
  rw [run_mrowP_map aR_inj (K := K) (N := N) (L := K + K) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [aR, aAk, aD2, aD1, hs] at hi ⊢
  all_goals try (simp [aR, aAk, aD2, aD1, hK', hN, hNK, h13, hK1, h15, h16, h17, h1, h9]; done)
  rw [run_autItP_map aAt_inj (K := K) (N := N) hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [aAt, aR, aAk, aD2, aD1, hs] at hi ⊢
  all_goals try (simp [aAt, aR, aAk, aD2, aD1, hK', hN, h1]; done)
  rw [run_gcAutP_map aG_inj (K := K) (N := N) hK hN0 _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [aG, aAt, aR, aAk, aD2, aD1, hs] at hi ⊢
  all_goals try (simp [aG, aAt, aR, aAk, aD2, aD1, hK', hN, hNK]; done)
  simp only []
  rw [run_deP_map aDE_inj (K := K) (N := N) (L := K + K) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [aDE, aG, aAt, aR, aAk, aD2, aD1, hs] at hi ⊢
  all_goals try (simp [aDE, aG, aAt, aR, aAk, aD2, aD1, hK', hN, hNK, h13, hK1, h15, h16, h17, h18, l1]; done)
  funext t
  fin_cases t <;> simp [aDE, aG, aAt, aR, aAk, aD2, aD1, hs, autOut, autTW, hRow, h13, h16, h17]

theorem noGrow_autBlkP : autBlkP.NoGrow := rfl
set_option maxRecDepth 100000 in
theorem wf_autBlkP : autBlkP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
