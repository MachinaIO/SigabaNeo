import SigabaNeo.Lib.Lattices.ProgAlgo.MulRW
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd

/-!
# The product of matrix words as a tape program

`matMulP : Prog 59` computes `matMulW N K m n l x y` (`run_matMulP`): tapes `0` output, `1` `x`
(`m × n` entries), `2` `y` (`n × l` entries), and templates `3` … `9` of lengths `K`, `N`, `N · K`,
`m`, `n`, `l`, `m · l · N · K`; scratch `10 … 58`, blank before and after.

Random access is replaced by streams: for each row `i`, a stream positioned at the row `i` of `x`;
for each column `j`, a stream positioned at the entry `(0, j)` of `y`; the term `t` reads the next
entry of a copy of the row stream and the first entry of the column stream, which then skips `l`
entries. The entry `(i, j)` is the sum of `n` products of ring words (`mulRWP`, `addRWP`), shifted
into the output register.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-- Shifting a sequence of words of length `c` into a register, consuming `d` bits of a stream
for each. -/
theorem pushSeq_iter (d c : ℕ) (g : List Bool → List Bool) (hg : ∀ s, (g s).length = c) :
    ∀ (m : ℕ) (sv out : List Bool),
      (fun a : List Bool × List Bool => (a.1.drop d, (a.2 ++ g a.1).drop c))^[m] (sv, out) =
        (sv.drop (m * d), (out ++ concatN m (fun j => g (sv.drop (j * d)))).drop (m * c))
  | 0, sv, out => by simp [concatN]
  | m + 1, sv, out => by
    rw [Function.iterate_succ_apply', pushSeq_iter d c g hg m sv out]
    have hl : (concatN m (fun j => g (sv.drop (j * d)))).length = m * c :=
      length_concatN fun j _ => hg _
    have := drop_append_drop out (concatN m (fun j => g (sv.drop (j * d)))) (g (sv.drop (m * d)))
    rw [hl, hg] at this
    simp only [List.drop_drop, this, concatN, Nat.succ_mul]


theorem iterate_drop (d : ℕ) : ∀ (m : ℕ) (sv : List Bool),
    (fun sv : List Bool => sv.drop d)^[m] sv = sv.drop (m * d)
  | 0, sv => by simp
  | m + 1, sv => by
    rw [Function.iterate_succ_apply', iterate_drop d m sv, List.drop_drop, Nat.succ_mul,
      Nat.add_comm]

theorem sumLoop_congr {N K n : ℕ} {f g : ℕ → List Bool} (h : ∀ t < n, f t = g t) :
    ∀ t, t ≤ n → sumLoop N K f t = sumLoop N K g t
  | 0, _ => rfl
  | t + 1, ht => by rw [sumLoop, sumLoop, sumLoop_congr h t (by omega), h t (by omega)]

theorem length_sumLoop (N K : ℕ) (f : ℕ → List Bool) : ∀ t, (sumLoop N K f t).length = N * K
  | 0 => by simp [sumLoop]
  | t + 1 => length_addRW N K (length_sumLoop N K f t) _

namespace Prog

open scoped Prog

/-! ### Skipping entries -/

def skv : Fin 3 → Fin 5 := ![0, 2, 4]
theorem skv_inj : Function.Injective skv := by decide

/-- Drop `|s 3| · |s 4|` bits of the stream `0` (tapes `1` `2` counters). -/
def skipP : Prog 5 := forN 1 3 (map skv dropP)

theorem run_skipP (s : Store 5) (h1 : s 1 = []) (h2 : s 2 = []) :
    run skipP s = Function.update s 0 ((s 0).drop ((s 3).length * (s 4).length)) := by
  have h := run_forN 1 3 (map skv dropP) (fun sv => Function.update s 0 sv)
    (fun sv => sv.drop (s 4).length) (fun sv w => by
      rw [run_dropP_map skv_inj _ (by simp [skv, h2])]
      funext t; fin_cases t <;> simp [skv]) (s 0) s (by funext t; fin_cases t <;> simp)
  rw [skipP, h, iterate_drop]
  funext t; fin_cases t <;> simp [h1]

theorem run_skipP_map {u : Fin 5 → Fin k} (hu : Function.Injective u) (s : Store k)
    (h1 : s (u 1) = []) (h2 : s (u 2) = []) :
    run (map u skipP) s =
      Function.update s (u 0) ((s (u 0)).drop ((s (u 3)).length * (s (u 4)).length)) :=
  run_map_eq_update hu _ s 0 _ (run_skipP _ h1 h2)

theorem run_mulRWP_map {u : Fin 38 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 38, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    run (map u mulRWP) s = Function.update s (u 0) (mulRW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_mulRWP _ hs hK hN hx hy)

theorem run_addRWP_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    run (map u addRWP) s = Function.update s (u 0) (addRW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_addRWP _ hs hK hN hx hy)

/-! ### The product -/

def mvEA : Fin 5 → Fin 59 := ![12, 15, 23, 24, 5]
def mvEB : Fin 5 → Fin 59 := ![17, 16, 23, 24, 5]
def mvAcc : Fin 5 → Fin 59 := ![14, 0, 23, 24, 5]
def skL : Fin 5 → Fin 59 := ![13, 24, 25, 8, 5]
def skN : Fin 5 → Fin 59 := ![10, 24, 25, 7, 5]
def sk1 : Fin 3 → Fin 59 := ![11, 24, 5]
def vMM : Fin 38 → Fin 59 := ![18, 15, 16, 3, 4, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
def vAA : Fin 28 → Fin 59 := ![19, 14, 18, 3, 4, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]

theorem mvEA_inj : Function.Injective mvEA := by decide
theorem mvEB_inj : Function.Injective mvEB := by decide
theorem mvAcc_inj : Function.Injective mvAcc := by decide
theorem skL_inj : Function.Injective skL := by decide
theorem skN_inj : Function.Injective skN := by decide
theorem sk1_inj : Function.Injective sk1 := by decide
theorem vMM_inj : Function.Injective vMM := by decide
theorem vAA_inj : Function.Injective vAA := by decide

/-- A term. Tapes `10` the row stream, `11` the column stream, `12` `13` their copies, `14` the
accumulator, `15` `16` the entries, `17` a copy, `18` their product, `19` the new accumulator,
`20` `21` `22` the counters of rows, columns and terms, `23` a bit, `24` `25` counters,
`26 … 58` the scratch of the subprograms. -/
def tBody : Prog 59 :=
  cp 15 5 ⨾ map mvEA mvP ⨾ cp 17 13 ⨾ cp 16 5 ⨾ map mvEB mvP ⨾ clr 17 ⨾ map skL skipP ⨾
    map vMM mulRWP ⨾ map vAA addRWP ⨾ cp 14 19 ⨾ clr 15 ⨾ clr 16 ⨾ clr 18 ⨾ clr 19

/-- An entry: the sum of its `n` terms, shifted into the output; the column stream moves to the
next column. -/
def jBody : Prog 59 :=
  cp 14 5 ⨾ setZero 14 ⨾ cp 12 10 ⨾ cp 13 11 ⨾ forN 22 7 tBody ⨾ map mvAcc mvP ⨾ map sk1 dropP ⨾
    clr 12 ⨾ clr 13 ⨾ clr 14

/-- A row: its `l` entries; the row stream moves to the next row. -/
def iBody : Prog 59 := cp 11 2 ⨾ forN 21 8 jBody ⨾ map skN skipP ⨾ clr 11

/-- **The product of an `m × n` and an `n × l` matrix word.** -/
def matMulP : Prog 59 := cp 0 9 ⨾ cp 10 1 ⨾ forN 20 6 iBody ⨾ clr 10

/-- The abstract term: (row stream, column stream, accumulator). -/
def tstep (N K l : ℕ) : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (sa, sb, acc) => (sa.drop (N * K), sb.drop (l * (N * K)),
      addRW N K acc (mulRW N K (takeD (N * K) sa) (takeD (N * K) sb)))

def tG (S : Store 59) : List Bool × List Bool × List Bool → Store 59
  | (sa, sb, acc) => Function.update (Function.update (Function.update S 12 sa) 13 sb) 14 acc

/-- The scratch tapes of a term are blank. -/
def TClean (S : Store 59) : Prop :=
  ∀ i : Fin 59, (15 ≤ i.val ∧ i.val ≤ 19) ∨ 23 ≤ i.val → S i = []

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem run_tBody {K N l : ℕ} (S : Store 59) (hS : TClean S) (hK : (S 3).length = K)
    (hN : (S 4).length = N) (hNK : (S 5).length = N * K) (hl : (S 8).length = l) (a)
    (ha : a.2.2.length = N * K) (w : List Bool) :
    run tBody (Function.update (tG S a) 22 w) = Function.update (tG S (tstep N K l a)) 22 w := by
  obtain ⟨sa, sb, acc⟩ := a
  simp only at ha
  have hS : ∀ i : Fin 59, (15 ≤ i.val ∧ i.val ≤ 19) ∨ 23 ≤ i.val → S i = [] := hS
  simp only [tBody, run_seq, run_copy, run_clear]
  rw [run_mvP_map mvEA_inj _ ?_ ?_, run_mvP_map mvEB_inj _ ?_ ?_, run_skipP_map skL_inj _ ?_ ?_,
    run_mulRWP_map vMM_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_,
    run_addRWP_map vAA_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [tG, tstep]
    fin_cases t <;> simp [mvEA, mvEB, skL, vMM, vAA, hS, hNK, hl, drop_append_of_length]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [mvEA, mvEB, skL, vMM, vAA, tG, hS] at hi ⊢)
    | simp [mvEA, mvEB, skL, vMM, vAA, tG, hS, hK, hN, hNK, ha, drop_append_of_length, length_mulRW]

/-- The entry of a row stream and a column stream. -/
def accF (N K n l : ℕ) (sa sb : List Bool) : List Bool :=
  sumLoop N K (fun t => mulRW N K (takeD (N * K) (sa.drop (t * (N * K))))
    (takeD (N * K) (sb.drop (t * (l * (N * K)))))) n

theorem tstep_iter (N K l : ℕ) (sa sb : List Bool) : ∀ t,
    (tstep N K l)^[t] (sa, sb, zeroW (N * K)) =
      (sa.drop (t * (N * K)), sb.drop (t * (l * (N * K))), sumLoop N K (fun t =>
        mulRW N K (takeD (N * K) (sa.drop (t * (N * K))))
          (takeD (N * K) (sb.drop (t * (l * (N * K)))))) t)
  | 0 => by simp [sumLoop]
  | t + 1 => by
    rw [Function.iterate_succ_apply', tstep_iter N K l sa sb t, tstep, List.drop_drop,
      List.drop_drop, sumLoop]
    congr 2 <;> ring_nf

/-- The abstract entry: (column stream, output register). -/
def jstep (N K n l : ℕ) (sai : List Bool) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (N * K), (a.2 ++ takeD (N * K) (accF N K n l sai a.1)).drop (N * K))

def jG (S : Store 59) : List Bool × List Bool → Store 59
  | (sbj, out) => Function.update (Function.update S 11 sbj) 0 out

/-- The scratch tapes of an entry are blank. -/
def JClean (S : Store 59) : Prop :=
  ∀ i : Fin 59, (12 ≤ i.val ∧ i.val ≤ 19) ∨ 22 ≤ i.val → S i = []

set_option linter.unusedSimpArgs false in
theorem run_jBody {K N n l : ℕ} (S : Store 59) (hS : JClean S) (hK : (S 3).length = K)
    (hN : (S 4).length = N) (hNK : (S 5).length = N * K) (hn : (S 7).length = n)
    (hl : (S 8).length = l) (a) (w : List Bool) :
    run jBody (Function.update (jG S a) 21 w) =
      Function.update (jG S (jstep N K n l (S 10) a)) 21 w := by
  obtain ⟨sbj, out⟩ := a
  have hS : ∀ i : Fin 59, (12 ≤ i.val ∧ i.val ≤ 19) ∨ 22 ≤ i.val → S i = [] := hS
  have e0 : run (cp 13 11) (run (cp 12 10) (run (setZero 14) (run (cp 14 5)
      (Function.update (jG S (sbj, out)) 21 w)))) =
      tG (Function.update (jG S (sbj, out)) 21 w) (S 10, sbj, zeroW (N * K)) := by
    funext t; simp only [run_copy, run_setZero, tG, jG]
    fin_cases t <;> simp [hS, hNK, zeroW]
  have hloop := run_forN_inv 22 7 tBody (tG (Function.update (jG S (sbj, out)) 21 w)) (tstep N K l)
    (fun a => a.2.2.length = N * K)
    (fun a w' ha => run_tBody _ (fun i hi => by fin_cases i <;> simp [jG, hS] at hi ⊢)
      (by simp [jG, hK]) (by simp [jG, hN]) (by simp [jG, hNK]) (by simp [jG, hl]) a ha w')
    (fun a ha => by obtain ⟨_, _, _⟩ := a; exact length_addRW N K ha _)
    (S 10, sbj, zeroW (N * K)) (by simp [zeroW]) _ rfl
  have hsplit : run jBody (Function.update (jG S (sbj, out)) 21 w) =
      run (map mvAcc mvP ⨾ map sk1 dropP ⨾ clr 12 ⨾ clr 13 ⨾ clr 14)
        (run (forN 22 7 tBody) (run (cp 13 11) (run (cp 12 10) (run (setZero 14) (run (cp 14 5)
          (Function.update (jG S (sbj, out)) 21 w)))))) := rfl
  rw [hsplit, e0, hloop, tstep_iter]
  simp only [run_seq, run_clear]
  rw [run_mvP_map mvAcc_inj _ ?_ ?_, run_dropP_map sk1_inj _ ?_]
  · have hacc : (sumLoop N K (fun t => mulRW N K (takeD (N * K) ((S 10).drop (t * (N * K))))
        (takeD (N * K) (sbj.drop (t * (l * (N * K)))))) n).length = N * K := length_sumLoop _ _ _ _
    funext t
    simp only [tG, jG, jstep, accF]
    fin_cases t <;> simp [mvAcc, sk1, hS, hNK, hn, hacc, takeD_of_length']
  all_goals simp [mvAcc, sk1, tG, jG, hS]

/-- The abstract row: (row stream, output register). -/
def istep (N K n l : ℕ) (y : List Bool) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (n * (N * K)), (a.2 ++ concatN l (fun j =>
    takeD (N * K) (accF N K n l a.1 (y.drop (j * (N * K)))))).drop (l * (N * K)))

def iG (s : Store 59) : List Bool × List Bool → Store 59
  | (sai, out) => Function.update (Function.update s 10 sai) 0 out

set_option linter.unusedSimpArgs false in
theorem run_iBody {K N n l : ℕ} (s : Store 59) (hs : ∀ i : Fin 59, 10 ≤ i.val → i ≠ 20 → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hn : (s 7).length = n) (hl : (s 8).length = l) (a) (w : List Bool) :
    run iBody (Function.update (iG s a) 20 w) =
      Function.update (iG s (istep N K n l (s 2) a)) 20 w := by
  obtain ⟨sai, out⟩ := a
  set S := Function.update (iG s (sai, out)) 20 w
  have hloop := run_forN 21 8 jBody (jG (Function.update S 11 (s 2))) (jstep N K n l sai)
    (fun a w' => by
      have := run_jBody (K := K) (N := N) (n := n) (l := l) (Function.update S 11 (s 2))
        (fun i hi => by fin_cases i <;> simp [S, iG, hs] at hi ⊢) (by simp [S, iG, hK])
        (by simp [S, iG, hN]) (by simp [S, iG, hNK]) (by simp [S, iG, hn]) (by simp [S, iG, hl]) a w'
      rwa [show (Function.update S 11 (s 2)) 10 = sai by simp [S, iG]] at this)
    (s 2, out) (Function.update S 11 (s 2)) (by funext t; fin_cases t <;> simp [S, jG, iG])
  have hsplit : run iBody S = run (map skN skipP ⨾ clr 11)
      (run (forN 21 8 jBody) (run (cp 11 2) S)) := rfl
  have h2 : S 2 = s 2 := by simp [S, iG]
  have h8 : Function.update S 11 (s 2) 8 = s 8 := by simp [S, iG]
  rw [hsplit, run_copy, h2, hloop, h8, hl]
  erw [pushSeq_iter (N * K) (N * K) (fun sb => takeD (N * K) (accF N K n l sai sb))
    (fun _ => length_takeD _ _)]
  simp only [run_seq, run_clear]
  rw [run_skipP_map skN_inj _ ?_ ?_]
  · funext t
    simp only [jG, iG, istep, S]
    fin_cases t <;> simp [skN, hs, hNK, hn]
  all_goals simp [skN, S, jG, iG, hs]

theorem accF_eq {N K m n l : ℕ} {x y : List Bool} (hx : x.length = m * n * (N * K))
    (hy : y.length = n * l * (N * K)) {i j : ℕ} (hi : i < m) (hj : j < l) :
    takeD (N * K) (accF N K n l (x.drop (i * n * (N * K))) (y.drop (j * (N * K)))) =
      sumLoop N K (fun t => mulRW N K (rget N K (i * n + t) x) (rget N K (t * l + j) y)) n := by
  rw [accF, takeD_of_length' (length_sumLoop _ _ _ _)]
  apply sumLoop_congr _ n le_rfl
  intro t ht
  have hx' : x.length = (m * n) * (N * K) := hx
  have hy' : y.length = (n * l) * (N * K) := hy
  have hia : i * n + t < m * n := by nlinarith
  have hjb : t * l + j < n * l := by nlinarith
  rw [List.drop_drop, List.drop_drop, rget, rget,
    ← takeD_drop_eq_block hx' hia, ← takeD_drop_eq_block hy' hjb]
  congr 3 <;> ring

theorem matMulW_eq {N K m n l : ℕ} {x y : List Bool} (hx : x.length = m * n * (N * K))
    (hy : y.length = n * l * (N * K)) :
    concatN m (fun i => concatN l (fun j =>
      takeD (N * K) (accF N K n l (x.drop (i * (n * (N * K)))) (y.drop (j * (N * K)))))) =
      matMulW N K m n l x y := by
  rw [matMulW, concatN_mul]
  apply concatN_congr
  intro i hi
  apply concatN_congr
  intro j hj
  have hl : 0 < l := by omega
  have hdiv : (i * l + j) / l = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (i * l + j) % l = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod, show i * (n * (N * K)) = i * n * (N * K) by ring, accF_eq hx hy hi hj]

set_option linter.unusedSimpArgs false in
/-- **The product of matrix words.** -/
theorem run_matMulP {K N m n l : ℕ} (s : Store 59) (hs : ∀ i : Fin 59, 10 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hNK : (s 5).length = N * K)
    (hm : (s 6).length = m) (hn : (s 7).length = n) (hl : (s 8).length = l)
    (hO : (s 9).length = m * l * (N * K)) (hx : (s 1).length = m * n * (N * K))
    (hy : (s 2).length = n * l * (N * K)) :
    run matMulP s = Function.update s 0 (matMulW N K m n l (s 1) (s 2)) := by
  have hloop := run_forN 20 6 iBody (iG s) (istep N K n l (s 2))
    (fun a w => run_iBody (K := K) (N := N) (n := n) (l := l) s (fun i hi _ => hs i hi) hK hN hNK
      hn hl a w) (s 1, s 9) (Function.update (Function.update s 0 (s 9)) 10 (s 1))
    (by funext t; fin_cases t <;> simp [iG])
  have hsplit : run matMulP s = run (clr 10) (run (forN 20 6 iBody)
      (Function.update (Function.update s 0 (s 9)) 10 (s 1))) := by
    simp only [matMulP, run_seq, run_copy]
    rw [show Function.update s 0 (s 9) 1 = s 1 by simp]
  rw [hsplit, hloop]
  have h6 : Function.update (Function.update s 0 (s 9)) 10 (s 1) 6 = s 6 := by simp
  have hpush := pushSeq_iter (n * (N * K)) (l * (N * K)) (fun sai => concatN l (fun j =>
    takeD (N * K) (accF N K n l sai ((s 2).drop (j * (N * K)))))) (fun _ =>
      length_concatN fun _ _ => length_takeD _ _) m (s 1) (s 9)
  rw [h6, hm]
  erw [hpush]
  rw [show m * (l * (N * K)) = m * l * (N * K) by ring, drop_append_of_length hO,
    matMulW_eq hx hy]
  funext t
  fin_cases t <;> simp [iG, hs]

theorem noGrow_matMulP : matMulP.NoGrow := rfl
theorem wf_matMulP : matMulP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
