import SigabaNeo.Lib.Lattices.ProgAlgo.MatMul
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Mul

/-!
# The product of matrix words modulo `2^K − 1` as a tape program

`matMulMP : Prog 59` computes `matMulMW N K m n l x y` (`run_matMulMP`), the analogue of
`matMulP` (`SigabaNeo.Lib.Lattices.ProgAlgo.MatMul`) with the products and sums of
`ℤ_{2^K − 1}[X]/(X^N + 1)` (`mulRMP`, `addRMP`): tapes `0` output, `1` `x` (`m × n` entries), `2`
`y` (`n × l` entries), and templates `3` … `9` of lengths `K`, `N`, `N · K`, `m`, `n`, `l`,
`m · l · N · K`; scratch `10 … 58`, blank before and after. Entry `(i, j)` reads as
`Σ_t x_{i,t} y_{t,j}` (`decRM_rget_matMulMW`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The running sum of `n` ring words modulo `2^K − 1`. -/
def sumLoopM (N K : ℕ) (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => zeroW (N * K)
  | t + 1 => addRMW N K (sumLoopM N K f t) (f t)

theorem sumLoopM_congr {N K n : ℕ} {f g : ℕ → List Bool} (h : ∀ t < n, f t = g t) :
    ∀ t, t ≤ n → sumLoopM N K f t = sumLoopM N K g t
  | 0, _ => rfl
  | t + 1, ht => by rw [sumLoopM, sumLoopM, sumLoopM_congr h t (by omega), h t (by omega)]

theorem length_sumLoopM (N K : ℕ) (f : ℕ → List Bool) : ∀ t, (sumLoopM N K f t).length = N * K
  | 0 => by simp [sumLoopM]
  | t + 1 => length_addRMW N K (length_sumLoopM N K f t) _

/-- **The running sum reads as the sum.** -/
theorem decRM_sumLoopM {N K n : ℕ} {f : ℕ → List Bool} (hf : ∀ t < n, (f t).length = N * K) :
    ∀ t, t ≤ n → decRM N K (sumLoopM N K f t) = ∑ t' ∈ Finset.range t, decRM N K (f t')
  | 0, _ => by
    apply ext_coefG; intro i hi
    have hb : block K i (zeroW (N * K)) = zeroW K := by
      simp only [block, zeroW, List.drop_replicate, List.take_replicate]
      congr 1
      have : i * K + K ≤ N * K := by nlinarith
      omega
    rw [sumLoopM, coefG_decRM _ hi, hb, decM_zeroW, Finset.range_zero, Finset.sum_empty,
      coefG_zero]
  | t + 1, ht => by
    rw [sumLoopM, decRM_addRMW (length_sumLoopM N K f t) (hf t (by omega)),
      decRM_sumLoopM hf t (by omega), Finset.sum_range_succ]

/-- **Matrix product** of an `m × n` and an `n × l` matrix word modulo `2^K − 1`. -/
def matMulMW (N K m n l : ℕ) (x y : List Bool) : List Bool :=
  concatN (m * l) fun p =>
    sumLoopM N K (fun t => mulRMW N K (rget N K (p / l * n + t) x) (rget N K (t * l + p % l) y)) n

namespace Prog

open scoped Prog

def vMMm : Fin 37 → Fin 59 := ![18, 15, 16, 3, 4, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
def vAAm : Fin 28 → Fin 59 := ![19, 14, 18, 3, 4, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]

theorem vMMm_inj : Function.Injective vMMm := by decide
theorem vAAm_inj : Function.Injective vAAm := by decide

/-- A term. Tapes `10` the row stream, `11` the column stream, `12` `13` their copies, `14` the
accumulator, `15` `16` the entries, `17` a copy, `18` their product, `19` the new accumulator,
`20` `21` `22` the counters of rows, columns and terms, `23` a bit, `24` `25` counters,
`26 … 58` the scratch of the subprograms. -/
def tBodyM : Prog 59 :=
  cp 15 5 ⨾ map mvEA mvP ⨾ cp 17 13 ⨾ cp 16 5 ⨾ map mvEB mvP ⨾ clr 17 ⨾ map skL skipP ⨾
    map vMMm mulRMP ⨾ map vAAm addRMP ⨾ cp 14 19 ⨾ clr 15 ⨾ clr 16 ⨾ clr 18 ⨾ clr 19

/-- An entry: the sum of its `n` terms, shifted into the output; the column stream moves to the
next column. -/
def jBodyM : Prog 59 :=
  cp 14 5 ⨾ setZero 14 ⨾ cp 12 10 ⨾ cp 13 11 ⨾ forN 22 7 tBodyM ⨾ map mvAcc mvP ⨾ map sk1 dropP ⨾
    clr 12 ⨾ clr 13 ⨾ clr 14

/-- A row: its `l` entries; the row stream moves to the next row. -/
def iBodyM : Prog 59 := cp 11 2 ⨾ forN 21 8 jBodyM ⨾ map skN skipP ⨾ clr 11

/-- **The product of an `m × n` and an `n × l` matrix word.** -/
def matMulMP : Prog 59 := cp 0 9 ⨾ cp 10 1 ⨾ forN 20 6 iBodyM ⨾ clr 10

/-- The abstract term: (row stream, column stream, accumulator). -/
def tstepM (N K l : ℕ) : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (sa, sb, acc) => (sa.drop (N * K), sb.drop (l * (N * K)),
      addRMW N K acc (mulRMW N K (takeD (N * K) sa) (takeD (N * K) sb)))

def tGM (S : Store 59) : List Bool × List Bool × List Bool → Store 59
  | (sa, sb, acc) => Function.update (Function.update (Function.update S 12 sa) 13 sb) 14 acc

/-- The scratch tapes of a term are blank. -/
def TCleanM (S : Store 59) : Prop :=
  ∀ i : Fin 59, (15 ≤ i.val ∧ i.val ≤ 19) ∨ 23 ≤ i.val → S i = []

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem run_tBodyM {K N l : ℕ} (S : Store 59) (hS : TCleanM S) (hK : (S 3).length = K)
    (hN : (S 4).length = N) (hNK : (S 5).length = N * K) (hl : (S 8).length = l) (a)
    (ha : a.2.2.length = N * K) (w : List Bool) :
    run tBodyM (Function.update (tGM S a) 22 w) = Function.update (tGM S (tstepM N K l a)) 22 w := by
  obtain ⟨sa, sb, acc⟩ := a
  simp only at ha
  have hS : ∀ i : Fin 59, (15 ≤ i.val ∧ i.val ≤ 19) ∨ 23 ≤ i.val → S i = [] := hS
  simp only [tBodyM, run_seq, run_copy, run_clear]
  rw [run_mvP_map mvEA_inj _ ?_ ?_, run_mvP_map mvEB_inj _ ?_ ?_, run_skipP_map skL_inj _ ?_ ?_,
    run_mulRMP_map vMMm_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_,
    run_addRMP_map vAAm_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [tGM, tstepM]
    fin_cases t <;> simp [mvEA, mvEB, skL, vMMm, vAAm, hS, hNK, hl, drop_append_of_length]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [mvEA, mvEB, skL, vMMm, vAAm, tGM, hS] at hi ⊢)
    | simp [mvEA, mvEB, skL, vMMm, vAAm, tGM, hS, hK, hN, hNK, ha, drop_append_of_length, length_mulRMW]

/-- The entry of a row stream and a column stream. -/
def accFM (N K n l : ℕ) (sa sb : List Bool) : List Bool :=
  sumLoopM N K (fun t => mulRMW N K (takeD (N * K) (sa.drop (t * (N * K))))
    (takeD (N * K) (sb.drop (t * (l * (N * K)))))) n

theorem tstepM_iter (N K l : ℕ) (sa sb : List Bool) : ∀ t,
    (tstepM N K l)^[t] (sa, sb, zeroW (N * K)) =
      (sa.drop (t * (N * K)), sb.drop (t * (l * (N * K))), sumLoopM N K (fun t =>
        mulRMW N K (takeD (N * K) (sa.drop (t * (N * K))))
          (takeD (N * K) (sb.drop (t * (l * (N * K)))))) t)
  | 0 => by simp [sumLoopM]
  | t + 1 => by
    rw [Function.iterate_succ_apply', tstepM_iter N K l sa sb t, tstepM, List.drop_drop,
      List.drop_drop, sumLoopM]
    congr 2 <;> ring_nf

/-- The abstract entry: (column stream, output register). -/
def jstepM (N K n l : ℕ) (sai : List Bool) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (N * K), (a.2 ++ takeD (N * K) (accFM N K n l sai a.1)).drop (N * K))

def jGM (S : Store 59) : List Bool × List Bool → Store 59
  | (sbj, out) => Function.update (Function.update S 11 sbj) 0 out

/-- The scratch tapes of an entry are blank. -/
def JCleanM (S : Store 59) : Prop :=
  ∀ i : Fin 59, (12 ≤ i.val ∧ i.val ≤ 19) ∨ 22 ≤ i.val → S i = []

set_option linter.unusedSimpArgs false in
theorem run_jBodyM {K N n l : ℕ} (S : Store 59) (hS : JCleanM S) (hK : (S 3).length = K)
    (hN : (S 4).length = N) (hNK : (S 5).length = N * K) (hn : (S 7).length = n)
    (hl : (S 8).length = l) (a) (w : List Bool) :
    run jBodyM (Function.update (jGM S a) 21 w) =
      Function.update (jGM S (jstepM N K n l (S 10) a)) 21 w := by
  obtain ⟨sbj, out⟩ := a
  have hS : ∀ i : Fin 59, (12 ≤ i.val ∧ i.val ≤ 19) ∨ 22 ≤ i.val → S i = [] := hS
  have e0 : run (cp 13 11) (run (cp 12 10) (run (setZero 14) (run (cp 14 5)
      (Function.update (jGM S (sbj, out)) 21 w)))) =
      tGM (Function.update (jGM S (sbj, out)) 21 w) (S 10, sbj, zeroW (N * K)) := by
    funext t; simp only [run_copy, run_setZero, tGM, jGM]
    fin_cases t <;> simp [hS, hNK, zeroW]
  have hloop := run_forN_inv 22 7 tBodyM (tGM (Function.update (jGM S (sbj, out)) 21 w)) (tstepM N K l)
    (fun a => a.2.2.length = N * K)
    (fun a w' ha => run_tBodyM _ (fun i hi => by fin_cases i <;> simp [jGM, hS] at hi ⊢)
      (by simp [jGM, hK]) (by simp [jGM, hN]) (by simp [jGM, hNK]) (by simp [jGM, hl]) a ha w')
    (fun a ha => by obtain ⟨_, _, _⟩ := a; exact length_addRMW N K ha _)
    (S 10, sbj, zeroW (N * K)) (by simp [zeroW]) _ rfl
  have hsplit : run jBodyM (Function.update (jGM S (sbj, out)) 21 w) =
      run (map mvAcc mvP ⨾ map sk1 dropP ⨾ clr 12 ⨾ clr 13 ⨾ clr 14)
        (run (forN 22 7 tBodyM) (run (cp 13 11) (run (cp 12 10) (run (setZero 14) (run (cp 14 5)
          (Function.update (jGM S (sbj, out)) 21 w)))))) := rfl
  rw [hsplit, e0, hloop, tstepM_iter]
  simp only [run_seq, run_clear]
  rw [run_mvP_map mvAcc_inj _ ?_ ?_, run_dropP_map sk1_inj _ ?_]
  · have hacc : (sumLoopM N K (fun t => mulRMW N K (takeD (N * K) ((S 10).drop (t * (N * K))))
        (takeD (N * K) (sbj.drop (t * (l * (N * K)))))) n).length = N * K := length_sumLoopM _ _ _ _
    funext t
    simp only [tGM, jGM, jstepM, accFM]
    fin_cases t <;> simp [mvAcc, sk1, hS, hNK, hn, hacc, takeD_of_length']
  all_goals simp [mvAcc, sk1, tGM, jGM, hS]

/-- The abstract row: (row stream, output register). -/
def istepM (N K n l : ℕ) (y : List Bool) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (n * (N * K)), (a.2 ++ concatN l (fun j =>
    takeD (N * K) (accFM N K n l a.1 (y.drop (j * (N * K)))))).drop (l * (N * K)))

def iGM (s : Store 59) : List Bool × List Bool → Store 59
  | (sai, out) => Function.update (Function.update s 10 sai) 0 out

set_option linter.unusedSimpArgs false in
theorem run_iBodyM {K N n l : ℕ} (s : Store 59) (hs : ∀ i : Fin 59, 10 ≤ i.val → i ≠ 20 → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hn : (s 7).length = n) (hl : (s 8).length = l) (a) (w : List Bool) :
    run iBodyM (Function.update (iGM s a) 20 w) =
      Function.update (iGM s (istepM N K n l (s 2) a)) 20 w := by
  obtain ⟨sai, out⟩ := a
  set S := Function.update (iGM s (sai, out)) 20 w
  have hloop := run_forN 21 8 jBodyM (jGM (Function.update S 11 (s 2))) (jstepM N K n l sai)
    (fun a w' => by
      have := run_jBodyM (K := K) (N := N) (n := n) (l := l) (Function.update S 11 (s 2))
        (fun i hi => by fin_cases i <;> simp [S, iGM, hs] at hi ⊢) (by simp [S, iGM, hK])
        (by simp [S, iGM, hN]) (by simp [S, iGM, hNK]) (by simp [S, iGM, hn]) (by simp [S, iGM, hl]) a w'
      rwa [show (Function.update S 11 (s 2)) 10 = sai by simp [S, iGM]] at this)
    (s 2, out) (Function.update S 11 (s 2)) (by funext t; fin_cases t <;> simp [S, jGM, iGM])
  have hsplit : run iBodyM S = run (map skN skipP ⨾ clr 11)
      (run (forN 21 8 jBodyM) (run (cp 11 2) S)) := rfl
  have h2 : S 2 = s 2 := by simp [S, iGM]
  have h8 : Function.update S 11 (s 2) 8 = s 8 := by simp [S, iGM]
  rw [hsplit, run_copy, h2, hloop, h8, hl]
  erw [pushSeq_iter (N * K) (N * K) (fun sb => takeD (N * K) (accFM N K n l sai sb))
    (fun _ => length_takeD _ _)]
  simp only [run_seq, run_clear]
  rw [run_skipP_map skN_inj _ ?_ ?_]
  · funext t
    simp only [jGM, iGM, istepM, S]
    fin_cases t <;> simp [skN, hs, hNK, hn]
  all_goals simp [skN, S, jGM, iGM, hs]

theorem accFM_eq {N K m n l : ℕ} {x y : List Bool} (hx : x.length = m * n * (N * K))
    (hy : y.length = n * l * (N * K)) {i j : ℕ} (hi : i < m) (hj : j < l) :
    takeD (N * K) (accFM N K n l (x.drop (i * n * (N * K))) (y.drop (j * (N * K)))) =
      sumLoopM N K (fun t => mulRMW N K (rget N K (i * n + t) x) (rget N K (t * l + j) y)) n := by
  rw [accFM, takeD_of_length' (length_sumLoopM _ _ _ _)]
  apply sumLoopM_congr _ n le_rfl
  intro t ht
  have hx' : x.length = (m * n) * (N * K) := hx
  have hy' : y.length = (n * l) * (N * K) := hy
  have hia : i * n + t < m * n := by nlinarith
  have hjb : t * l + j < n * l := by nlinarith
  rw [List.drop_drop, List.drop_drop, rget, rget,
    ← takeD_drop_eq_block hx' hia, ← takeD_drop_eq_block hy' hjb]
  congr 3 <;> ring

theorem matMulMW_eq {N K m n l : ℕ} {x y : List Bool} (hx : x.length = m * n * (N * K))
    (hy : y.length = n * l * (N * K)) :
    concatN m (fun i => concatN l (fun j =>
      takeD (N * K) (accFM N K n l (x.drop (i * (n * (N * K)))) (y.drop (j * (N * K)))))) =
      matMulMW N K m n l x y := by
  rw [matMulMW, concatN_mul]
  apply concatN_congr
  intro i hi
  apply concatN_congr
  intro j hj
  have hl : 0 < l := by omega
  have hdiv : (i * l + j) / l = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (i * l + j) % l = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod, show i * (n * (N * K)) = i * n * (N * K) by ring, accFM_eq hx hy hi hj]

set_option linter.unusedSimpArgs false in
/-- **The product of matrix words.** -/
theorem run_matMulMP {K N m n l : ℕ} (s : Store 59) (hs : ∀ i : Fin 59, 10 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hm : (s 6).length = m) (hn : (s 7).length = n) (hl : (s 8).length = l)
    (hO : (s 9).length = m * l * (N * K)) (hx : (s 1).length = m * n * (N * K))
    (hy : (s 2).length = n * l * (N * K)) :
    run matMulMP s = Function.update s 0 (matMulMW N K m n l (s 1) (s 2)) := by
  have hloop := run_forN 20 6 iBodyM (iGM s) (istepM N K n l (s 2))
    (fun a w => run_iBodyM (K := K) (N := N) (n := n) (l := l) s (fun i hi _ => hs i hi) hK hN hNK
      hn hl a w) (s 1, s 9) (Function.update (Function.update s 0 (s 9)) 10 (s 1))
    (by funext t; fin_cases t <;> simp [iGM])
  have hsplit : run matMulMP s = run (clr 10) (run (forN 20 6 iBodyM)
      (Function.update (Function.update s 0 (s 9)) 10 (s 1))) := by
    simp only [matMulMP, run_seq, run_copy]
    rw [show Function.update s 0 (s 9) 1 = s 1 by simp]
  rw [hsplit, hloop]
  have h6 : Function.update (Function.update s 0 (s 9)) 10 (s 1) 6 = s 6 := by simp
  have hpush := pushSeq_iter (n * (N * K)) (l * (N * K)) (fun sai => concatN l (fun j =>
    takeD (N * K) (accFM N K n l sai ((s 2).drop (j * (N * K)))))) (fun _ =>
      length_concatN fun _ _ => length_takeD _ _) m (s 1) (s 9)
  rw [h6, hm]
  erw [hpush]
  rw [show m * (l * (N * K)) = m * l * (N * K) by ring, drop_append_of_length hO,
    matMulMW_eq hx hy]
  funext t
  fin_cases t <;> simp [iGM, hs]

theorem noGrow_matMulMP : matMulMP.NoGrow := rfl
theorem wf_matMulMP : matMulMP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
