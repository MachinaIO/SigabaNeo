import SigabaNeo.Lib.Lattices.ProgAlgo.SimSLP
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPPK
import SigabaNeo.Lib.Lattices.Algo.SimWords

/-!
# The key-matrix sum on tapes

`keySumP : Prog 86` computes `keySumMW N K k m xW` (hence `keySumW` for `m = 1`) where the term
`xW c i j` is read from a store of blocks of `V` bits (e.g. the final store of the SLP evaluator):
the block at the unary position `pos c i j`, without its first `off` bits, cut to `m 2k N K` bits.
The positions are a stream of unary words of `W` bits in the loop order (`posW`).

The program is three nested counter loops whose accumulators follow the nested `mSum`s of
`keySumMW` exactly; each round reads the block (`readP`), builds `vW c i j` (`monoWP` on
`powW K i`, kept by a shift per `i`, and `replaceP` at the column `c`), runs `ginvP`, `matMulP`
(`vtermP`) and adds (`addRWP`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices SigabaNeo.Lattices.Algo

namespace Prog

open scoped Prog

variable {k : ℕ}

/-! ### The rows `V_{c,i,j}` as a replaced block -/

theorem concatN_single (x : List Bool) {n c M : ℕ} (hc : c < n) :
    concatN n (fun p => if p = c then x else zeroW M) =
      zeroW (c * M) ++ x ++ zeroW ((n - c - 1) * M) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [concatN]
    by_cases h : c < n
    · rw [ih h, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      have : (n + 1 - c - 1) * M = (n - c - 1) * M + M := by
        rw [show n + 1 - c - 1 = (n - c - 1) + 1 by omega, Nat.succ_mul]
      rw [this]; simp only [zeroW, List.append_assoc, List.replicate_append_replicate]
    · have hcn : c = n := by omega
      subst hcn
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), concatN_congr (g := fun _ => zeroW M)
        (fun i hi => ite_eq_right_of_eq_false _ _ (eq_false (by omega))),
        concatN_zeroW]
      simp [zeroW]

theorem length_monoW' {N K : ℕ} (j : ℕ) {v : List Bool} (hv : v.length = K) :
    (monoW N K j v).length = N * K :=
  length_concatN fun t _ => by split_ifs <;> simp [hv, zeroW]

theorem vW_eq_replace {N K k c : ℕ} (i j : ℕ) (hc : c < 2 * k) :
    (zeroW (2 * k * (N * K))).take (c * (N * K)) ++ monoW N K j (powW K i) ++
      (zeroW (2 * k * (N * K))).drop ((c + 1) * (N * K)) = vW N K k c i j := by
  rw [vW, Nat.one_mul, concatN_single _ hc]
  have h1 : (zeroW (2 * k * (N * K))).take (c * (N * K)) = zeroW (c * (N * K)) := by
    simp only [zeroW, List.take_replicate]
    congr 1
    exact min_eq_left (Nat.mul_le_mul_right _ hc.le)
  have h2 : (zeroW (2 * k * (N * K))).drop ((c + 1) * (N * K)) =
      zeroW ((2 * k - c - 1) * (N * K)) := by
    simp only [zeroW, List.drop_replicate]
    congr 1
    rw [Nat.sub_sub, Nat.sub_mul]
  rw [h1, h2]

/-! ### One term: `X · G̲⁻¹(V_{c,i,j})`

`vtermP : Prog 69`. Tapes: `0` the output, `1` `X` (`m 2k N K` bits), `2` `powW K i`, `3` a word of
length `c`, `4` a word of length `j`; templates `5` … `15` of lengths `K`, `N`, `N K`, `k`, `2k`,
`2k`, `2k N`, `2k N K`, `2k 2k N K`, `m`, `m 2k N K`; registers `16` … `19` and scratch
`20` … `68`, blank before and after. -/

def vMo : Fin 12 → Fin 69 := ![16, 2, 4, 5, 6, 7, 20, 21, 22, 23, 24, 25]
def vRp : Fin 12 → Fin 69 := ![18, 17, 3, 7, 16, 20, 21, 22, 23, 24, 25, 26]
def vGi : Fin 35 → Fin 69 := ![19, 18, 5, 11, 8, 13, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]
def vMm : Fin 59 → Fin 69 := ![0, 1, 19, 5, 6, 7, 14, 9, 10, 15, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]
theorem vMo_inj : Function.Injective vMo := by decide
theorem vRp_inj : Function.Injective vRp := by decide
theorem vGi_inj : Function.Injective vGi := by decide
theorem vMm_inj : Function.Injective vMm := by decide

/-- **One term** `X · G̲⁻¹(V_{c,i,j})`. -/
def vtermP : Prog 69 :=
  map vMo monoWP ⨾ cp 17 12 ⨾ setZero 17 ⨾ map vRp replaceP ⨾ map vGi ginvP ⨾ map vMm matMulP ⨾
    clr 16 ⨾ clr 17 ⨾ clr 18 ⨾ clr 19

set_option linter.unusedSimpArgs false in
theorem run_vRp {N K k c i j : ℕ} (t : Store 69) (hb : ∀ u : Fin 69, 20 ≤ u.val → t u = [])
    (hc : c < 2 * k) (h16 : t 16 = monoW N K j (powW K i)) (h17 : t 17 = zeroW (2 * k * (N * K)))
    (h3 : (t 3).length = c) (h7 : (t 7).length = N * K) :
    run (map vRp replaceP) t = Function.update t 18 (vW N K k c i j) := by
  rw [run_map_eq_update vRp_inj replaceP _ 0 _ (run_replaceP (i := c) (K := N * K) _ ?_ ?_ ?_ ?_ ?_)]
  · simp only [Function.comp, vRp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, h16, h17]
    rw [vW_eq_replace i j hc]
  · intro u hu; fin_cases u <;> simp [vRp] at hu ⊢ <;> exact hb _ (by simp)
  · simp [vRp, h3]
  · simp [vRp, h7]
  · simp [vRp, h16, length_monoW' j (length_powW K i)]
  · simp [vRp, h17, Nat.mul_le_mul_right _ hc]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem run_vtermP {N K k m c i j : ℕ} (s : Store 69) (hb : ∀ t : Fin 69, 16 ≤ t.val → s t = [])
    (hc : c < 2 * k) (h1 : (s 1).length = m * (2 * k) * (N * K)) (h2 : s 2 = powW K i)
    (h3 : (s 3).length = c) (h4 : (s 4).length = j) (h5 : (s 5).length = K) (h6 : (s 6).length = N)
    (h7 : (s 7).length = N * K) (h8 : (s 8).length = k) (h9 : (s 9).length = 2 * k)
    (h10 : (s 10).length = 2 * k) (h11 : (s 11).length = 2 * k * N)
    (h12 : (s 12).length = 2 * k * (N * K)) (h13 : (s 13).length = 2 * k * (2 * k * (N * K)))
    (h14 : (s 14).length = m) (h15 : (s 15).length = m * (2 * k) * (N * K)) :
    run vtermP s = Function.update s 0
      (matMulW N K m (2 * k) (2 * k) (s 1) (ginvW N K k (vW N K k c i j))) := by
  have hmono : (monoW N K j (powW K i)).length = N * K := length_monoW' j (length_powW K i)
  have hvl : (vW N K k c i j).length = 2 * k * (N * K) := by
    rw [vW]
    exact (length_concatN (K := N * K) (fun p _ => by split_ifs <;> simp [hmono, zeroW])).trans
      (by ring)
  simp only [vtermP, run_seq, run_copy, run_setZero, run_clear]
  rw [run_monoWP_map vMo_inj (K := K) (N := N) (j := j) _
    (fun t ht => by fin_cases t <;> simp [vMo, vGi, vMm] at ht ⊢ <;> exact hb _ (by simp))
    (by simp [vMo, vGi, vMm, h2, length_powW]) (by simp [vMo, vGi, vMm, h4]) (by simp [vMo, vGi, vMm, h5]) (by simp [vMo, vGi, vMm, h6])
    (by simp [vMo, vGi, vMm, h7])]
  rw [run_vRp (N := N) (K := K) (k := k) (c := c) (i := i) (j := j) _ (fun t ht => by fin_cases t <;> simp [vMo, vGi, vMm] at ht ⊢ <;> exact hb _ (by simp)) hc
    (by simp [vMo, vGi, vMm, h2]) (by simp [vMo, vGi, vMm, h12, zeroW]) (by simp [vMo, vGi, vMm, h3]) (by simp [vMo, vGi, vMm, h7])]
  rw [run_ginvP_map vGi_inj (K := K) (N := N) (k' := k) _
    (fun t ht => by fin_cases t <;> simp [vMo, vGi, vMm] at ht ⊢ <;> exact hb _ (by simp))
    (by simp [vMo, vGi, vMm, h5]) (by simp [vMo, vGi, vMm, h11]) (by simp [vMo, vGi, vMm, h8]) (by simp [vMo, vGi, vMm, h13])
    (by simp [vMo, vGi, vMm, hvl])]
  rw [run_matMulP_map vMm_inj (K := K) (N := N) (m := m) (n := 2 * k) (l := 2 * k) _
    (fun t ht => by fin_cases t <;> simp [vMo, vGi, vMm] at ht ⊢ <;> exact hb _ (by simp))
    (by simp [vMo, vGi, vMm, h5]) (by simp [vMo, vGi, vMm, h6]) (by simp [vMo, vGi, vMm, h7]) (by simp [vMo, vGi, vMm, h14])
    (by simp [vMo, vGi, vMm, h9]) (by simp [vMo, vGi, vMm, h10]) (by simp [vMo, vGi, vMm, h15]) (by simp [vMo, vGi, vMm, h1])
    (by simp [vMo, vGi, vMm, length_ginvW]; ring)]
  funext t
  fin_cases t <;> simp [vMo, vGi, vMm] <;> (apply hb; decide)

/-! ### Reading a block of the store

`readP : Prog 15`. Tapes: `0` the output, `1` the store `st` (blocks of `V` bits), `2` the stream of
positions (unary words of `W` bits); templates `3` … `6` of lengths `W`, `V`, `off`, `Lx`; registers
and scratch `7` … `14`, blank before and after. It reads the next position `j` (consuming `W` bits of
the stream) and writes `Lx` bits of the block `j` after its first `off` bits. -/

def rdA : Fin 5 → Fin 15 := ![2, 7, 9, 10, 3]
def rdS : Fin 15 → Fin 15 := ![0, 1, 2, 4, 3, 7, 5, 8, 6, 9, 10, 11, 12, 13, 14]
def rdD : Fin 3 → Fin 15 := ![8, 9, 5]
def rdM : Fin 5 → Fin 15 := ![8, 0, 9, 10, 6]
theorem rdA_inj : Function.Injective rdA := by decide
theorem rdS_inj : Function.Injective rdS := by decide
theorem rdD_inj : Function.Injective rdD := by decide
theorem rdM_inj : Function.Injective rdM := by decide

/-- **Read the block at the next position.** -/
def readP : Prog 15 :=
  cp 7 3 ⨾ map rdA mvP ⨾ cp 8 1 ⨾ map rdS (skipT 5) ⨾ map rdD dropP ⨾ cp 0 6 ⨾ map rdM mvP ⨾ clr 8

/-- The block read: `Lx` bits of the block at the unary position `u`, after `off` bits. -/
def readW (V off Lx : ℕ) (st u : List Bool) : List Bool :=
  takeD Lx (((st.drop (V * u.count true)).drop off))

theorem run_rdS {V : ℕ} (t : Store 15) (h9 : t 9 = []) (h10 : t 10 = []) (h11 : t 11 = [])
    (hV : (t 4).length = V) :
    run (map rdS (skipT 5)) t =
      Function.update (Function.update t 7 []) 8 ((t 8).drop (V * (t 7).count true)) := by
  rw [run_map rdS_inj, run_skipT (V := V) 5 (Or.inl rfl) (t ∘ rdS) h9 h10 h11 (show (t (rdS 3)).length = V from hV), extend_update rdS_inj,
    extend_update rdS_inj, extend_comp_self]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_readP {W V off Lx : ℕ} (s : Store 15) (hb : ∀ t : Fin 15, 7 ≤ t.val → s t = [])
    (h3 : (s 3).length = W) (h4 : (s 4).length = V) (h5 : (s 5).length = off)
    (h6 : (s 6).length = Lx) :
    run readP s = Function.update (Function.update s 0 (readW V off Lx (s 1) (takeD W (s 2)))) 2
      ((s 2).drop W) := by
  simp only [readP, run_seq, run_copy, run_clear]
  rw [run_mvP_map rdA_inj _ (by simp [rdA, hb 9 (by decide)]) (by simp [rdA, hb 10 (by decide)])]
  rw [run_rdS (V := V) _ (by simp [rdA, hb 9 (by decide)]) (by simp [rdA, hb 10 (by decide)])
    (by simp [rdA, hb 11 (by decide)]) (by simp [rdA, h4])]
  rw [run_dropP_map rdD_inj _ (by simp [rdA, rdD, hb 9 (by decide)])]
  rw [run_mvP_map rdM_inj _ (by simp [rdA, rdD, rdM, hb 9 (by decide)])
    (by simp [rdA, rdD, rdM, hb 10 (by decide)])]
  funext t
  fin_cases t <;> simp [rdA, rdD, rdM, readW, h3, h5, h6, drop_append_takeD h3,
    drop_append_takeD h6, hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide)]

end Prog

end SigabaNeo.Tape
