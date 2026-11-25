import SigabaNeoStd.Lattices.ProgAlgo.SimTmpl
import SigabaNeoStd.Lattices.ProgAlgo.SLPPK
import SigabaNeoStd.Lattices.Algo.SimWords

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

/-! ### Counter loops with an indexed invariant -/

theorem run_loop_idx (c : Fin k) (body : Prog k) (H : ℕ → Store k) (n : ℕ)
    (hstep : ∀ j < n, ∀ w, run body (Function.update (H j) c w) = Function.update (H (j + 1)) c w) :
    ∀ (w : List Bool) (j : ℕ), j + w.length = n →
      run (loop c body) (Function.update (H j) c w) = Function.update (H n) c [] := by
  intro w
  induction w with
  | nil => intro j hj; simp only [List.length_nil, Nat.add_zero] at hj; subst hj; rw [run_loop, Function.update_self]; rfl
  | cons x w ih =>
    intro j hj
    simp only [List.length_cons] at hj
    have h1 : run body (tailAt c (Function.update (H j) c (x :: w))) =
        Function.update (H (j + 1)) c w := by
      rw [tailAt, Function.update_self, Function.update_idem]; exact hstep j (by omega) w
    have h2 := ih (j + 1) (by omega)
    rw [run_loop, Function.update_self] at h2
    rw [run_loop, Function.update_self, List.length_cons, Function.iterate_succ_apply, h1, h2]

/-- **The counter idiom with an indexed invariant**: the round `j < n` takes `H j` to `H (j + 1)`. -/
theorem run_forN_idx (c t : Fin k) (body : Prog k) (H : ℕ → Store k) (n : ℕ)
    (hstep : ∀ j < n, ∀ w, run body (Function.update (H j) c w) = Function.update (H (j + 1)) c w)
    (s : Store k) (hs : Function.update s c (s t) = Function.update (H 0) c (s t))
    (hn : (s t).length = n) :
    run (forN c t body) s = Function.update (H n) c [] := by
  rw [forN, run_seq, run_copy, hs]
  exact run_loop_idx c body H n hstep (s t) 0 (by omega)

theorem drop_concatN_append {n L c : ℕ} {f : ℕ → List Bool} (hf : ∀ i < n, (f i).length = L)
    (R : List Bool) (hc : c < n) :
    (concatN n f ++ R).drop (c * L) = f c ++ (concatN n f ++ R).drop ((c + 1) * L) := by
  induction n generalizing R with
  | zero => omega
  | succ n ih =>
    rw [concatN, List.append_assoc]
    by_cases h : c < n
    · exact ih (fun i hi => hf i (by omega)) _ h
    · have hcn : c = n := by omega
      subst hcn
      have hl : (concatN c f).length = c * L := length_concatN fun i hi => hf i (by omega)
      rw [List.drop_left' hl, Nat.succ_mul, ← List.drop_drop, List.drop_left' hl,
        List.drop_left' (hf c (by omega))]

/-! ### The key-matrix sum

`keySumP : Prog 86`. Tapes: `0` the output, `1` the store, `2` the positions; templates `3` … `17`
of lengths `K`, `N`, `N K`, `k`, `2k`, `2k`, `2k N`, `2k N K`, `2k 2k N K`, `m`, `m 2k N K`, `m 2k N`,
`W`, `V`, `off` (`KTmpl`); then, blank before and after: `18` the stream of positions, `19` the block
read, `20` the term, `21` `powW K i`, `22` `23` the words of lengths `c` and `2k − c`, `24` `25` of
lengths `j` and `N − j`, `26` `27` `28` the accumulators of the three loops, `29` a register, `30`
`31` `32` the counters, `33` … `85` scratch. -/

def oRd : Fin 15 → Fin 86 := ![19, 1, 18, 15, 16, 17, 13, 33, 34, 35, 36, 37, 38, 39, 40]
def oVt : Fin 69 → Fin 86 := ![20, 19, 21, 22, 24, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85]
def oAj : Fin 28 → Fin 86 := ![29, 26, 20, 3, 14, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
def oAi : Fin 28 → Fin 86 := ![29, 27, 26, 3, 14, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
def oAc : Fin 28 → Fin 86 := ![29, 28, 27, 3, 14, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
def oSh : Fin 11 → Fin 86 := ![29, 33, 21, 3, 34, 35, 36, 37, 38, 39, 40]
def oOne : Fin 11 → Fin 86 := ![21, 33, 29, 3, 34, 35, 36, 37, 38, 39, 40]
def oDc : Fin 3 → Fin 86 := ![22, 33, 23]
def oDj : Fin 3 → Fin 86 := ![24, 33, 25]
theorem oRd_inj : Function.Injective oRd := by decide
set_option maxRecDepth 100000 in
theorem oVt_inj : Function.Injective oVt := by decide
theorem oAj_inj : Function.Injective oAj := by decide
theorem oAi_inj : Function.Injective oAi := by decide
theorem oAc_inj : Function.Injective oAc := by decide
theorem oSh_inj : Function.Injective oSh := by decide
theorem oOne_inj : Function.Injective oOne := by decide
theorem oDc_inj : Function.Injective oDc := by decide
theorem oDj_inj : Function.Injective oDj := by decide

attribute [local simp] oRd oVt oAj oAi oAc oSh oOne oDc oDj


/-- One round of the inner loop: read, the term, add; next `j`. -/
def bodyJ : Prog 86 :=
  map oRd readP ⨾ map oVt vtermP ⨾ map oAj addRWP ⨾ cp 26 29 ⨾ clr 29 ⨾ clr 19 ⨾ clr 20 ⨾
    tl 25 ⨾ cp 24 4 ⨾ map oDj dropP

/-- The inner loop over `j < N`, its sum on `26`. -/
def loopJ : Prog 86 := cp 26 13 ⨾ setZero 26 ⨾ cp 25 4 ⨾ forN 32 4 bodyJ ⨾ clr 24 ⨾ clr 25

/-- One round of the middle loop: the inner loop, add; next `powW K i`. -/
def bodyI : Prog 86 :=
  loopJ ⨾ map oAi addRWP ⨾ cp 27 29 ⨾ clr 29 ⨾ clr 26 ⨾ map oSh shlP ⨾ cp 21 29 ⨾ clr 29

/-- The middle loop over `i < k`, its sum on `27`. -/
def loopI : Prog 86 :=
  cp 27 13 ⨾ setZero 27 ⨾ cp 29 3 ⨾ setZero 29 ⨾ map oOne (zipW oneOp true) ⨾ clr 29 ⨾
    forN 31 6 bodyI ⨾ clr 21

/-- One round of the outer loop: the middle loop, add; next `c`. -/
def bodyC : Prog 86 :=
  loopI ⨾ map oAc addRWP ⨾ cp 28 29 ⨾ clr 29 ⨾ clr 27 ⨾ tl 23 ⨾ cp 22 7 ⨾ map oDc dropP

/-- **The key-matrix sum** `keySumMW N K k m xW`, `xW c i j` read from the store. -/
def keySumP : Prog 86 :=
  cp 18 2 ⨾ cp 28 13 ⨾ setZero 28 ⨾ cp 23 7 ⨾ forN 30 7 bodyC ⨾ cp 0 28 ⨾ clr 28 ⨾ clr 22 ⨾
    clr 23 ⨾ clr 18

/-- The templates of `keySumP`. -/
structure KTmpl (N K k m W V off : ℕ) (r : Store 86) : Prop where
  h3 : (r 3).length = K
  h4 : (r 4).length = N
  h5 : (r 5).length = N * K
  h6 : (r 6).length = k
  h7 : (r 7).length = 2 * k
  h8 : (r 8).length = 2 * k
  h9 : (r 9).length = 2 * k * N
  h10 : (r 10).length = 2 * k * (N * K)
  h11 : (r 11).length = 2 * k * (2 * k * (N * K))
  h12 : (r 12).length = m
  h13 : (r 13).length = m * (2 * k) * (N * K)
  h14 : (r 14).length = m * (2 * k) * N
  h15 : (r 15).length = W
  h16 : (r 16).length = V
  h17 : (r 17).length = off

theorem run_oRd {W V off Lx : ℕ} (t : Store 86) (hb : ∀ x : Fin 86, 33 ≤ x.val → x.val < 41 → t x = [])
    (h15 : (t 15).length = W) (h16 : (t 16).length = V) (h17 : (t 17).length = off)
    (h13 : (t 13).length = Lx) :
    run (map oRd readP) t = Function.update (Function.update t 19
      (readW V off Lx (t 1) (takeD W (t 18)))) 18 ((t 18).drop W) := by
  rw [run_map oRd_inj, run_readP (W := W) (V := V) (off := off) (Lx := Lx) (t ∘ oRd)
    (fun x hx => by fin_cases x <;> simp [oRd] at hx ⊢ <;> (apply hb <;> decide)) h15 h16 h17 h13,
    extend_update oRd_inj, extend_update oRd_inj, extend_comp_self]
  rfl

theorem run_oVt {N K k m c i j : ℕ} (t : Store 86) (hb : ∀ x : Fin 86, 33 ≤ x.val → t x = [])
    (ht : KTmpl N K k m W V off t) (hc : c < 2 * k)
    (h19 : (t 19).length = m * (2 * k) * (N * K)) (h21 : t 21 = powW K i)
    (h22 : (t 22).length = c) (h24 : (t 24).length = j) :
    run (map oVt vtermP) t = Function.update t 20
      (matMulW N K m (2 * k) (2 * k) (t 19) (ginvW N K k (vW N K k c i j))) :=
  run_map_eq_update oVt_inj vtermP t 0 _ (run_vtermP (t ∘ oVt)
    (fun x hx => by fin_cases x <;> simp [oVt] at hx ⊢ <;> (apply hb; decide)) hc h19 h21 h22 h24
    ht.h3 ht.h4 ht.h5 ht.h6 ht.h7 ht.h8 ht.h9 ht.h10 ht.h11 ht.h12 ht.h13)

theorem KTmpl.upd {N K k m W V off : ℕ} {r : Store 86} (h : KTmpl N K k m W V off r) (t : Fin 86)
    (ht : 18 ≤ t.val) (w : List Bool) : KTmpl N K k m W V off (Function.update r t w) := by
  have e : ∀ x : Fin 86, x.val < 18 → Function.update r t w x = r x := fun x hx =>
    Function.update_of_ne (fun h => by subst h; omega) _ _
  exact ⟨by rw [e 3 (by decide)]; exact h.h3, by rw [e 4 (by decide)]; exact h.h4,
    by rw [e 5 (by decide)]; exact h.h5, by rw [e 6 (by decide)]; exact h.h6,
    by rw [e 7 (by decide)]; exact h.h7, by rw [e 8 (by decide)]; exact h.h8,
    by rw [e 9 (by decide)]; exact h.h9, by rw [e 10 (by decide)]; exact h.h10,
    by rw [e 11 (by decide)]; exact h.h11, by rw [e 12 (by decide)]; exact h.h12,
    by rw [e 13 (by decide)]; exact h.h13, by rw [e 14 (by decide)]; exact h.h14,
    by rw [e 15 (by decide)]; exact h.h15, by rw [e 16 (by decide)]; exact h.h16,
    by rw [e 17 (by decide)]; exact h.h17⟩

/-- The term of the bit `(c, i, j)`: the block read at the position, times `G̲⁻¹(V_{c,i,j})`. -/
def termW (N K k m V off W : ℕ) (st : List Bool) (pos : ℕ → ℕ → ℕ → ℕ) (c i j : ℕ) : List Bool :=
  matMulW N K m (2 * k) (2 * k) (readW V off (m * (2 * k) * (N * K)) st (unaryW W (pos c i j)))
    (ginvW N K k (vW N K k c i j))

theorem length_mSum (N K k m : ℕ) (f : ℕ → List Bool) :
    ∀ t, (mSum N K k m f t).length = m * (2 * k) * (N * K)
  | 0 => by simp [mSum]
  | t + 1 => by rw [mSum]; exact length_matAddW (length_mSum N K k m f t) _

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **The inner loop**: the sum over `j < N` on `26`; the positions consumed. -/
theorem run_loopJ {N K k m W V off c i : ℕ} (r : Store 86) (ht : KTmpl N K k m W V off r)
    (hb : ∀ t : Fin 86, 33 ≤ t.val → r t = []) (h19 : r 19 = []) (h20 : r 20 = [])
    (h24 : r 24 = []) (h25 : r 25 = []) (h29 : r 29 = []) (h32 : r 32 = [])
    (hc : c < 2 * k) (h21 : r 21 = powW K i) (h22 : (r 22).length = c) (pos : ℕ → ℕ → ℕ → ℕ)
    (hpos : ∀ j < N, pos c i j ≤ W) (R : List Bool)
    (h18 : r 18 = concatN N (fun j => unaryW W (pos c i j)) ++ R) :
    run loopJ r = Function.update (Function.update r 26
      (mSum N K k m (termW N K k m V off W (r 1) pos c i) N)) 18 R := by
  set S := concatN N (fun j => unaryW W (pos c i j)) ++ R with hS
  have hlu : ∀ j < N, (unaryW W (pos c i j)).length = W := fun j hj => length_unaryW (hpos j hj)
  let H : ℕ → Store 86 := fun j => Function.update (Function.update (Function.update
    (Function.update r 26 (mSum N K k m (termW N K k m V off W (r 1) pos c i) j)) 18
      (S.drop (j * W))) 25 ((r 4).drop j)) 24 ((r 4).drop (N - j))
  have hstep : ∀ j < N, ∀ w, run bodyJ (Function.update (H j) 32 w) =
      Function.update (H (j + 1)) 32 w := by
    intro j hj w
    have hD := drop_concatN_append (f := fun j => unaryW W (pos c i j)) hlu R hj
    have hT : takeD W (S.drop (j * W)) = unaryW W (pos c i j) := by
      rw [hS, hD, takeD_eq_take (by simp [hlu j hj]), List.take_left' (hlu j hj)]
    have hD' : (S.drop (j * W)).drop W = S.drop ((j + 1) * W) := by
      rw [hS, hD, List.drop_left' (hlu j hj)]
    simp only [bodyJ, run_seq, run_copy, run_clear, run_tail]
    rw [run_oRd (W := W) (V := V) (off := off) (Lx := m * (2 * k) * (N * K)) _
      (fun x hx hx' => by fin_cases x <;> simp [H] at hx hx' ⊢ <;> (apply hb; decide))
      (by simp [H, ht.h15]) (by simp [H, ht.h16]) (by simp [H, ht.h17]) (by simp [H, ht.h13])]
    rw [run_oVt (N := N) (K := K) (k := k) (m := m) (c := c) (i := i) (j := j) _
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      ((ht.upd 26 (by decide) _ |>.upd 18 (by decide) _ |>.upd 25 (by decide) _ |>.upd 24 (by decide) _
        |>.upd 32 (by decide) _ |>.upd 19 (by decide) _ |>.upd 18 (by decide) _)) hc
      (by simp [H, readW]) (by simp [H, h21]) (by simp [H, h22]) (by simp [H, ht.h4]; omega)]
    rw [run_addRWP_mat_map oAj_inj (K := K) (N := N) (L := m * (2 * k)) _
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      (by simp [oAj, H, ht.h3]) (by simp [oAj, H, ht.h14])
      (by simp [oAj, H, length_mSum]; ring) (by simp [oAj, H, length_matMulW]; ring)]
    rw [run_dropP_map oDj_inj _ (by simp [oDj, H, hb 33 (by decide)])]
    funext x
    fin_cases x <;> simp [H, h19, h20, h29, ht.h4, hT, mSum, termW, Nat.succ_mul]
  have hSN : S.drop (N * W) = R := by
    rw [hS, List.drop_left' (length_concatN hlu)]
  simp only [loopJ, run_seq, run_copy, run_setZero, run_clear]
  rw [run_forN_idx 32 4 bodyJ H N hstep _ ?_ (by simp [ht.h4])]
  · funext x
    fin_cases x <;> simp [H, hSN, h24, h25, h32]
  · funext x
    fin_cases x <;> simp [H, h18, h24, ht.h4, ht.h13, mSum, zeroW]

theorem run_oSh {K i : ℕ} (t : Store 86) (hb : ∀ x : Fin 86, 33 ≤ x.val → x.val < 41 → t x = [])
    (h21 : t 21 = powW K i) :
    run (map oSh shlP) t = Function.update t 29 (powW K (i + 1)) := by
  rw [shlP, run_zipW_map oSh_inj _ _ t (fun x hx => by
      fin_cases x <;> simp at hx ⊢ <;> (apply hb <;> decide)) (by apply hb <;> decide)]
  simp [h21, serF_shlOp_false, shl_powW]

theorem run_oOne {K : ℕ} (t : Store 86) (hb : ∀ x : Fin 86, 33 ≤ x.val → x.val < 41 → t x = [])
    (h29 : t 29 = List.replicate K false) :
    run (map oOne (zipW oneOp true)) t = Function.update t 21 (powW K 0) := by
  rw [run_zipW_map oOne_inj _ _ t (fun x hx => by
      fin_cases x <;> simp at hx ⊢ <;> (apply hb <;> decide)) (by apply hb <;> decide)]
  simp [h29, serF_oneOp_powW]

/-- The sum over `j < N` of the terms of `(c, i)`. -/
def sumJ (N K k m V off W : ℕ) (st : List Bool) (pos : ℕ → ℕ → ℕ → ℕ) (c i : ℕ) : List Bool :=
  mSum N K k m (termW N K k m V off W st pos c i) N

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **The middle loop**: the sum over `i < k` on `27`; the positions consumed. -/
theorem run_loopI {N K k m W V off c : ℕ} (r : Store 86) (ht : KTmpl N K k m W V off r)
    (hb : ∀ t : Fin 86, 33 ≤ t.val → r t = []) (h19 : r 19 = []) (h20 : r 20 = [])
    (h21 : r 21 = []) (h24 : r 24 = []) (h25 : r 25 = []) (h26 : r 26 = []) (h29 : r 29 = [])
    (h31 : r 31 = []) (h32 : r 32 = []) (hc : c < 2 * k) (h22 : (r 22).length = c)
    (pos : ℕ → ℕ → ℕ → ℕ) (hpos : ∀ i < k, ∀ j < N, pos c i j ≤ W) (R : List Bool)
    (h18 : r 18 = concatN k (fun i => concatN N (fun j => unaryW W (pos c i j))) ++ R) :
    run loopI r = Function.update (Function.update r 27
      (mSum N K k m (sumJ N K k m V off W (r 1) pos c) k)) 18 R := by
  set S := concatN k (fun i => concatN N (fun j => unaryW W (pos c i j))) ++ R with hS
  have hlu : ∀ i < k, (concatN N (fun j => unaryW W (pos c i j))).length = N * W := fun i hi =>
    length_concatN fun j hj => length_unaryW (hpos i hi j hj)
  let H : ℕ → Store 86 := fun i => Function.update (Function.update (Function.update r 27
    (mSum N K k m (sumJ N K k m V off W (r 1) pos c) i)) 18 (S.drop (i * (N * W)))) 21 (powW K i)
  have hstep : ∀ i < k, ∀ w, run bodyI (Function.update (H i) 31 w) =
      Function.update (H (i + 1)) 31 w := by
    intro i hi w
    have hD := drop_concatN_append (f := fun i => concatN N (fun j => unaryW W (pos c i j))) hlu R hi
    simp only [bodyI, run_seq, run_copy, run_clear]
    rw [run_loopJ (N := N) (K := K) (k := k) (m := m) (W := W) (V := V) (off := off) (c := c)
      (i := i) _ (ht.upd 27 (by decide) _ |>.upd 18 (by decide) _ |>.upd 21 (by decide) _
        |>.upd 31 (by decide) _)
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      (by simp [H, h19]) (by simp [H, h20]) (by simp [H, h24]) (by simp [H, h25]) (by simp [H, h29])
      (by simp [H, h32]) hc (by simp [H]) (by simp [H, h22]) pos (hpos i hi)
      (S.drop ((i + 1) * (N * W))) (by
        rw [Function.update_of_ne (by decide)]
        simp only [H, Function.update_of_ne (show (18 : Fin 86) ≠ 21 by decide), Function.update_self]
        rw [hS, hD])]
    rw [run_addRWP_mat_map oAi_inj (K := K) (N := N) (L := m * (2 * k)) _
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      (by simp [H, ht.h3]) (by simp [H, ht.h14])
      (by simp [H, length_mSum]; ring) (by simp [H, length_mSum]; ring)]
    rw [run_oSh (K := K) (i := i) _ (fun x hx hx' => by fin_cases x <;> simp [H] at hx hx' ⊢ <;> (apply hb; decide))
      (by simp [H])]
    funext x
    fin_cases x <;> simp [H, h26, h29, mSum, sumJ, Nat.succ_mul]
  have hSk : S.drop (k * (N * W)) = R := by
    rw [hS, List.drop_left' (length_concatN hlu)]
  simp only [loopI, run_seq, run_copy, run_setZero, run_clear]
  rw [run_oOne (K := K) _ (fun x hx hx' => by fin_cases x <;> simp at hx hx' ⊢ <;> (apply hb; decide))
    (by simp [ht.h3])]
  rw [run_forN_idx 31 6 bodyI H k hstep _ ?_ (by simp [ht.h6])]
  · funext x
    fin_cases x <;> simp [H, hSk, h21, h31]
  · funext x
    fin_cases x <;> simp [H, h18, h29, ht.h13, mSum, zeroW]

/-- **The positions** in the loop order: the unary words of `pos c i j` for `c < 2k`, `i < k`,
`j < N`, `W` bits each. -/
def posW (W N k : ℕ) (pos : ℕ → ℕ → ℕ → ℕ) : List Bool :=
  concatN (2 * k) fun c => concatN k fun i => concatN N fun j => unaryW W (pos c i j)

/-- The sum over `i < k` of the sums of `(c, i)`. -/
def sumI (N K k m V off W : ℕ) (st : List Bool) (pos : ℕ → ℕ → ℕ → ℕ) (c : ℕ) : List Bool :=
  mSum N K k m (sumJ N K k m V off W st pos c) k

theorem keySumMW_eq_mSum (N K k m V off W : ℕ) (st : List Bool) (pos : ℕ → ℕ → ℕ → ℕ) :
    keySumMW N K k m (fun c i j => readW V off (m * (2 * k) * (N * K)) st (unaryW W (pos c i j))) =
      mSum N K k m (sumI N K k m V off W st pos) (2 * k) := rfl

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **`keySumP` computes the key-matrix sum** `keySumMW N K k m xW`, the term `xW c i j` being the
block of the store `s 1` at the position `pos c i j` (`readW`), the positions given in the loop
order on `s 2` (`posW`); only the output tape `0` changes. -/
theorem run_keySumP {N K k m W V off : ℕ} (r : Store 86) (ht : KTmpl N K k m W V off r)
    (hb : ∀ t : Fin 86, 18 ≤ t.val → r t = []) (pos : ℕ → ℕ → ℕ → ℕ)
    (hpos : ∀ c < 2 * k, ∀ i < k, ∀ j < N, pos c i j ≤ W) (h2 : r 2 = posW W N k pos) :
    run keySumP r = Function.update r 0 (keySumMW N K k m
      (fun c i j => readW V off (m * (2 * k) * (N * K)) (r 1) (unaryW W (pos c i j)))) := by
  set S := posW W N k pos ++ [] with hS
  have hlu : ∀ c < 2 * k, (concatN k fun i => concatN N fun j => unaryW W (pos c i j)).length =
      k * (N * W) := fun c hc => length_concatN fun i hi => length_concatN fun j hj =>
    length_unaryW (hpos c hc i hi j hj)
  let H : ℕ → Store 86 := fun c => Function.update (Function.update (Function.update
    (Function.update r 28 (mSum N K k m (sumI N K k m V off W (r 1) pos) c)) 18
      (S.drop (c * (k * (N * W))))) 23 ((r 7).drop c)) 22 ((r 7).drop (2 * k - c))
  have hstep : ∀ c < 2 * k, ∀ w, run bodyC (Function.update (H c) 30 w) =
      Function.update (H (c + 1)) 30 w := by
    intro c hc w
    have hD := drop_concatN_append
      (f := fun c => concatN k fun i => concatN N fun j => unaryW W (pos c i j)) hlu [] hc
    simp only [bodyC, run_seq, run_copy, run_clear, run_tail]
    rw [run_loopI (N := N) (K := K) (k := k) (m := m) (W := W) (V := V) (off := off) (c := c)
      _ (ht.upd 28 (by decide) _ |>.upd 18 (by decide) _ |>.upd 23 (by decide) _
        |>.upd 22 (by decide) _ |>.upd 30 (by decide) _)
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      (by simp [H, hb 19 (by decide)]) (by simp [H, hb 20 (by decide)])
      (by simp [H, hb 21 (by decide)]) (by simp [H, hb 24 (by decide)])
      (by simp [H, hb 25 (by decide)]) (by simp [H, hb 26 (by decide)])
      (by simp [H, hb 29 (by decide)]) (by simp [H, hb 31 (by decide)])
      (by simp [H, hb 32 (by decide)]) hc (by simp [H, ht.h7]; omega) pos (hpos c hc)
      (S.drop ((c + 1) * (k * (N * W)))) (by
        rw [Function.update_of_ne (by decide)]
        simp only [H, Function.update_of_ne (show (18 : Fin 86) ≠ 22 by decide),
          Function.update_of_ne (show (18 : Fin 86) ≠ 23 by decide), Function.update_self]
        rw [hS, posW, hD])]
    rw [run_addRWP_mat_map oAc_inj (K := K) (N := N) (L := m * (2 * k)) _
      (fun x hx => by fin_cases x <;> simp [H] at hx ⊢ <;> (apply hb; decide))
      (by simp [H, ht.h3]) (by simp [H, ht.h14])
      (by simp [H, length_mSum]; ring) (by simp [H, length_mSum]; ring)]
    rw [run_dropP_map oDc_inj _ (by simp [H, hb 33 (by decide)])]
    funext x
    fin_cases x <;> simp [H, hb 27 (by decide), hb 29 (by decide), ht.h7, mSum, sumI, Nat.succ_mul]
  have hS2 : S.drop (2 * k * (k * (N * W))) = [] := by
    rw [hS, posW, List.drop_left' (length_concatN hlu)]
  simp only [keySumP, run_seq, run_copy, run_setZero, run_clear]
  rw [run_forN_idx 30 7 bodyC H (2 * k) hstep _ ?_ (by simp [ht.h7])]
  · rw [keySumMW_eq_mSum]
    have e18 : S.drop (2 * k * (k * (N * W))) = r 18 := by rw [hS2, hb 18 (by decide)]
    have e23 : (r 7).drop (2 * k) = r 23 := by simp [ht.h7, hb 23 (by decide)]
    simp only [H, e18, e23, Nat.sub_self, List.drop_zero]
    generalize mSum N K k m (sumI N K k m V off W (r 1) pos) (2 * k) = v
    clear hstep
    funext x
    fin_cases x <;> simp [hb 18 (by decide), hb 22 (by decide), hb 23 (by decide),
      hb 28 (by decide), hb 30 (by decide)]
  · have e18 : S.drop (0 * (k * (N * W))) = r 2 := by simp [hS, h2]
    have e28 : mSum N K k m (sumI N K k m V off W (r 1) pos) 0 =
        List.replicate (r 13).length false := by simp [mSum, zeroW, ht.h13]
    have e22 : (r 7).drop (2 * k - 0) = r 22 := by simp [ht.h7, hb 22 (by decide)]
    simp only [H, e18, e28, e22, List.drop_zero]
    clear hstep
    funext x
    fin_cases x <;> simp

/-! ### Reading the final store of an evaluator -/

theorem mSum_congr {N K k m n : ℕ} {f g : ℕ → List Bool} (h : ∀ t < n, f t = g t) :
    mSum N K k m f n = mSum N K k m g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mSum, mSum, ih (fun t ht => h t (by omega)), h n (by omega)]

theorem keySumMW_congr {N K k m : ℕ} {f g : ℕ → ℕ → ℕ → List Bool}
    (h : ∀ c < 2 * k, ∀ i < k, ∀ j < N, f c i j = g c i j) :
    keySumMW N K k m f = keySumMW N K k m g :=
  mSum_congr fun c hc => mSum_congr fun i hi => mSum_congr fun j hj => by rw [h c hc i hi j hj]

theorem rowSum_eq_mSum (N K k : ℕ) (f : ℕ → List Bool) :
    ∀ t, rowSum N K k f t = mSum N K k 1 f t
  | 0 => rfl
  | t + 1 => by rw [rowSum, mSum, rowSum_eq_mSum N K k f t]

/-- `keySumW` is `keySumMW` with one row. -/
theorem keySumW_eq_keySumMW (N K k : ℕ) (f : ℕ → ℕ → ℕ → List Bool) :
    keySumW N K k f = keySumMW N K k 1 f := by
  simp only [keySumW, keySumMW, rowSum_eq_mSum]

/-- **The block read** from a flattened list of words of `V` bits: `Lx` bits of the entry `j`, after
`off` bits. -/
theorem readW_flatten {V off Lx W j : ℕ} (L : List (List Bool)) (hL : ∀ x ∈ L, x.length = V)
    (hj : j < L.length) (hV : off + Lx ≤ V) :
    readW V off Lx L.flatten (unaryW W j) = (L[j].drop off).take Lx := by
  have hlen := length_flatten_of L hL
  have hle : V ≤ (L.flatten.drop (j * V)).length := by
    rw [List.length_drop, hlen]
    have := Nat.mul_le_mul_right V (show j + 1 ≤ L.length by omega)
    rw [Nat.succ_mul] at this; omega
  have e : L.flatten.drop (j * V) = L[j] ++ (L.flatten.drop (j * V)).drop V := by
    rw [← drop_take_flatten L hL j hj, List.take_append_drop]
  have hj' : (L[j]).length = V := hL _ (List.getElem_mem hj)
  rw [readW, count_unaryW, Nat.mul_comm V j, e, List.drop_append_of_le_length (by omega),
    takeD_eq_take (by simp; omega), List.take_append_of_le_length (by simp; omega)]

/-- The words of the final store of an evaluator all have `V` bits. -/
theorem store_len {ι : Type*} {V : ℕ} {ins : List (List Bool)} (hins : ∀ x ∈ ins, x.length = V)
    {n : ℕ} (hn : ins.length = n) {ix : ι → ℕ} (hix : ∀ i, ix i < n) {one : List Bool}
    (hone : one.length = V) (step : List Bool → List Bool → List Bool)
    (hstep : ∀ a b, a.length = V → b.length = V → (step a b).length = V) (p : SLP ι) :
    ∀ x ∈ ins ++ [one] ++ SLP.values (fun i => ins.getD (ix i) []) one step p, x.length = V := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | rfl) | hx
  · exact hins x hx
  · exact hone
  · refine slpRun_len _ one step (fun i => ?_) hone hstep p [] (by simp) x hx
    rw [List.getD_eq_getElem _ _ (by rw [hn]; exact hix i)]
    exact hins _ (List.getElem_mem _)

theorem wireIx_lt_store {ι : Type*} {α : Type*} {ins : List α} {n : ℕ} (hn : ins.length = n)
    {ix : ι → ℕ} (hix : ∀ i, ix i < n) (inp : ι → α) (one : α) (step : α → α → α) (p : SLP ι)
    (w : Wire ι) : wireIx ix n p.length w < (ins ++ [one] ++ SLP.values inp one step p).length := by
  have := wireIx_le ix hix p.length w
  have hv : (SLP.values inp one step p).length = p.length := by
    rw [SLP.values, length_slpRun]; simp
  simp [hn, hv]; omega

theorem length_keySumMW (N K k m : ℕ) (f : ℕ → ℕ → ℕ → List Bool) :
    (keySumMW N K k m f).length = m * (2 * k) * (N * K) := length_mSum _ _ _ _ _ _

/-! ### The short matrix `W_f`: a key sum plus one block

`simKeyP : Prog 94` runs `keySumP` on its tapes `0 … 85`, then reads one more block (`readP`) from a
second store (`86`) at the unary position on `87` (templates `88` `89` `90` of lengths `W'`, `V'`,
`off'`) and adds it: `matAddW N K (m 2k) (keySumMW …) (readW V' off' (m 2k N K) …)`. Tapes `91`
`92` `93` are blank before and after. -/

def oRg : Fin 15 → Fin 94 := ![91, 86, 93, 88, 89, 90, 13, 33, 34, 35, 36, 37, 38, 39, 40]
def oAf : Fin 28 → Fin 94 := ![92, 0, 91, 3, 14, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
theorem oRg_inj : Function.Injective oRg := by decide
theorem oAf_inj : Function.Injective oAf := by decide

/-- The tapes of `keySumP` inside `simKeyP`. -/
def oKs : Fin 86 → Fin 94 := Fin.castLE (by decide)
theorem oKs_inj : Function.Injective oKs := Fin.castLE_injective _

/-- **The key sum plus one block.** -/
def simKeyP : Prog 94 :=
  map oKs keySumP ⨾ cp 93 87 ⨾ map oRg readP ⨾ map oAf addRWP ⨾ cp 0 92 ⨾ clr 92 ⨾ clr 91 ⨾ clr 93

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem run_simKeyP {N K k m W V off W' V' off' : ℕ} (r : Store 94)
    (ht : KTmpl N K k m W V off (r ∘ oKs)) (hb : ∀ t : Fin 94, 18 ≤ t.val → t.val < 86 → r t = [])
    (hb' : ∀ t : Fin 94, 91 ≤ t.val → r t = []) (pos : ℕ → ℕ → ℕ → ℕ)
    (hpos : ∀ c < 2 * k, ∀ i < k, ∀ j < N, pos c i j ≤ W) (h2 : r 2 = posW W N k pos)
    (h88 : (r 88).length = W') (h89 : (r 89).length = V') (h90 : (r 90).length = off') :
    run simKeyP r = Function.update r 0 (matAddW N K (m * (2 * k))
      (keySumMW N K k m (fun c i j => readW V off (m * (2 * k) * (N * K)) (r 1) (unaryW W (pos c i j))))
      (readW V' off' (m * (2 * k) * (N * K)) (r 86) (takeD W' (r 87)))) := by
  have h13 : (r 13).length = m * (2 * k) * (N * K) := ht.h13
  have h14 : (r 14).length = m * (2 * k) * N := ht.h14
  have h3 : (r 3).length = K := ht.h3
  simp only [simKeyP, run_seq, run_copy, run_clear]
  rw [run_map_eq_update oKs_inj keySumP r 0 _ (run_keySumP (r ∘ oKs) ht
    (fun x hx => hb (oKs x) hx (by simp [oKs])) pos hpos h2)]
  rw [run_map oRg_inj, run_readP (W := W') (V := V') (off := off') (Lx := m * (2 * k) * (N * K)) _
    (fun x hx => by fin_cases x <;> simp [oRg, oKs] at hx ⊢ <;> (apply hb <;> decide))
    (by simp [oRg, oKs, h88]) (by simp [oRg, oKs, h89]) (by simp [oRg, oKs, h90])
    (by simp [oRg, oKs, h13]), extend_update oRg_inj, extend_update oRg_inj, extend_comp_self]
  rw [run_addRWP_mat_map oAf_inj (K := K) (N := N) (L := m * (2 * k)) _
    (fun x hx => by fin_cases x <;> simp [oAf, oRg, oKs] at hx ⊢ <;> (apply hb <;> decide))
    (by simp [oAf, oRg, oKs, h3]) (by simp [oAf, oRg, oKs, h14])
    (by simp [oAf, oRg, oKs, length_keySumMW]; ring) (by simp [oAf, oRg, oKs, readW]; ring)]
  funext x
  fin_cases x <;> simp [oAf, oRg, oKs, hb' 91 (by decide), hb' 92 (by decide), hb' 93 (by decide)]


end Prog

end SigabaNeo.Tape
