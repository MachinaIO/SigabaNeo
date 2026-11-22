import SigabaNeo.Lib.Lattices.ProgAlgo.MatMul

/-!
# Transposing block matrices and selecting blocks by bits, as tape programs

Programs of the fragment `NoGrow` (sizes from templates).

* `trP : Prog 20` (tapes `0` output, `1` the word `u`, templates `2` … `7` of lengths `B`, `r`,
  `s`, `m`, `Z` and `m · (s · (r · B) + Z)`; scratch `8 … 19`): the word `u` holds `m` matrices of
  `r × s` blocks of `B` bits, row-major; the output holds their transposes (`s × r`, row-major),
  each followed by `Z` zero bits (`trW`, `run_trP`).
* `selP : Prog 13` (tapes `0` output, `1` a bit stream `x`, `2` `3` words `X`, `Y`, templates `4`
  `5` `6` of lengths `B`, `n`, `n · B`; scratch `7 … 12`): for each of the first `n` bits of `x`,
  the first `B` bits of `X` if the bit is set, of `Y` otherwise (`selW`, `run_selP`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-! ### Words -/

/-- The column `j` of an `r × s` block matrix, read from the stream at the entry `(0, j)`. -/
def colTW (r s B : ℕ) (cs : List Bool) : List Bool :=
  concatN r (fun i => takeD B (cs.drop (i * (s * B))))

/-- The transpose of an `r × s` block matrix (row-major), read from a stream. -/
def matTW (r s B : ℕ) (ms : List Bool) : List Bool :=
  concatN s (fun j => colTW r s B (ms.drop (j * B)))

/-- **The transposes of `m` block matrices**, each followed by `Z` zero bits. -/
def trW (m r s B Z : ℕ) (u : List Bool) : List Bool :=
  concatN m (fun q => matTW r s B (u.drop (q * (r * (s * B)))) ++ List.replicate Z false)

theorem length_colTW (r s B : ℕ) (cs : List Bool) : (colTW r s B cs).length = r * B :=
  length_concatN fun _ _ => length_takeD _ _

theorem length_matTW (r s B : ℕ) (ms : List Bool) : (matTW r s B ms).length = s * (r * B) :=
  length_concatN fun _ _ => length_colTW _ _ _ _

theorem length_trW (m r s B Z : ℕ) (u : List Bool) :
    (trW m r s B Z u).length = m * (s * (r * B) + Z) :=
  length_concatN fun _ _ => by simp [length_matTW]

/-- **Blocks selected by bits.** -/
def selW (n B : ℕ) (x X Y : List Bool) : List Bool :=
  concatN n (fun j => takeD B (if hd (x.drop j) then X else Y))

theorem length_selW (n B : ℕ) (x X Y : List Bool) : (selW n B x X Y).length = n * B :=
  length_concatN fun _ _ => length_takeD _ _

namespace Prog

open scoped Prog

/-! ### The transpose -/

def tvM : Fin 5 → Fin 20 := ![11, 0, 16, 17, 2]
def tvI : Fin 5 → Fin 20 := ![10, 16, 17, 4, 2]
def tvD : Fin 3 → Fin 20 := ![9, 16, 2]
def tvS : Fin 5 → Fin 20 := ![8, 16, 17, 4, 2]
def tvF : Fin 3 → Fin 20 := ![0, 16, 6]
theorem tvM_inj : Function.Injective tvM := by decide
theorem tvI_inj : Function.Injective tvI := by decide
theorem tvD_inj : Function.Injective tvD := by decide
theorem tvS_inj : Function.Injective tvS := by decide
theorem tvF_inj : Function.Injective tvF := by decide

/-- A row of a column: shift the block of the row stream `10` into the output, then skip a row. -/
def trIBody : Prog 20 := cp 11 10 ⨾ map tvM mvP ⨾ clr 11 ⨾ map tvI skipP

/-- A column: its `r` blocks; the column stream `9` moves to the next column. -/
def trCBody : Prog 20 := cp 10 9 ⨾ forN 14 3 trIBody ⨾ clr 10 ⨾ map tvD dropP

/-- A matrix: its `s` columns, then `Z` zeros; the matrix stream `8` moves to the next matrix. -/
def trMBody : Prog 20 :=
  cp 9 8 ⨾ forN 13 4 trCBody ⨾ clr 9 ⨾ forN 15 3 (map tvS skipP) ⨾ map tvF (fillP false)

/-- **The transposes of `m` block matrices.** -/
def trP : Prog 20 := cp 0 7 ⨾ cp 8 1 ⨾ forN 12 5 trMBody ⨾ clr 8

/-- The abstract row: (row stream, output register). -/
def trIStep (s B : ℕ) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (s * B), (a.2 ++ takeD B a.1).drop B)

def trIG (S : Store 20) : List Bool × List Bool → Store 20
  | (rs, out) => Function.update (Function.update S 10 rs) 0 out

set_option linter.unusedSimpArgs false in
theorem run_trIBody {B s : ℕ} (S : Store 20) (h11 : S 11 = []) (h16 : S 16 = []) (h17 : S 17 = [])
    (hB : (S 2).length = B) (hs : (S 4).length = s) (a) (w : List Bool) :
    run trIBody (Function.update (trIG S a) 14 w) =
      Function.update (trIG S (trIStep s B a)) 14 w := by
  obtain ⟨rs, out⟩ := a
  simp only [trIBody, run_seq, run_copy, run_clear]
  rw [run_mvP_map tvM_inj _ (by simp [tvM, trIG, h16]) (by simp [tvM, trIG, h17]),
    run_skipP_map tvI_inj _ (by simp [tvM, tvI, trIG, h16]) (by simp [tvM, tvI, trIG, h17])]
  funext t
  simp only [trIG, trIStep]
  fin_cases t <;> simp [tvM, tvI, h11, hB, hs]

/-- The abstract column: (column stream, output register). -/
def trCStep (r s B : ℕ) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop B, (a.2 ++ colTW r s B a.1).drop (r * B))

def trCG (S : Store 20) : List Bool × List Bool → Store 20
  | (cs, out) => Function.update (Function.update S 9 cs) 0 out

set_option linter.unusedSimpArgs false in
theorem run_trCBody {B r s : ℕ} (S : Store 20) (h10 : S 10 = []) (h11 : S 11 = [])
    (h14 : S 14 = []) (h16 : S 16 = []) (h17 : S 17 = [])
    (hB : (S 2).length = B) (hr : (S 3).length = r) (hs : (S 4).length = s) (a) (w : List Bool) :
    run trCBody (Function.update (trCG S a) 13 w) =
      Function.update (trCG S (trCStep r s B a)) 13 w := by
  obtain ⟨cs, out⟩ := a
  set S1 := Function.update (Function.update (trCG S (cs, out)) 13 w) 10 cs
  have hloop := run_forN 14 3 trIBody (trIG S1) (trIStep s B)
    (fun a w' => run_trIBody S1 (by simp [S1, trCG, h11]) (by simp [S1, trCG, h16])
      (by simp [S1, trCG, h17]) (by simp [S1, trCG, hB]) (by simp [S1, trCG, hs]) a w')
    (cs, out) S1 (by funext t; fin_cases t <;> simp [S1, trIG, trCG])
  have hsplit : run trCBody (Function.update (trCG S (cs, out)) 13 w) =
      run (clr 10 ⨾ map tvD dropP) (run (forN 14 3 trIBody) S1) := by
    simp only [trCBody, run_seq, run_copy]
    rw [show Function.update (trCG S (cs, out)) 13 w 9 = cs by simp [trCG]]
  have h3 : S1 3 = S 3 := by simp [S1, trCG]
  rw [hsplit, hloop, h3, hr]
  erw [pushSeq_iter (s * B) B (takeD B) (fun _ => length_takeD _ _) r cs out]
  simp only [run_seq, run_clear]
  rw [run_dropP_map tvD_inj _ (by simp [tvD, trIG, S1, trCG, h16])]
  funext t
  simp only [trIG, trCG, trCStep, S1, colTW]
  fin_cases t <;> simp [tvD, h10, h14, hB]

/-- The abstract matrix: (matrix stream, output register). -/
def trMStep (r s B Z : ℕ) : List Bool × List Bool → List Bool × List Bool :=
  fun a => (a.1.drop (r * (s * B)),
    (a.2 ++ (matTW r s B a.1 ++ List.replicate Z false)).drop (s * (r * B) + Z))

def trMG (S : Store 20) : List Bool × List Bool → Store 20
  | (ms, out) => Function.update (Function.update S 8 ms) 0 out

theorem iterate_dropN (d : ℕ) : ∀ (m : ℕ) (sv : List Bool),
    (fun sv : List Bool => sv.drop d)^[m] sv = sv.drop (m * d) := iterate_drop d

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem run_trMBody {B r s Z : ℕ} (S : Store 20) (h9 : S 9 = []) (h10 : S 10 = [])
    (h11 : S 11 = []) (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) (h16 : S 16 = [])
    (h17 : S 17 = []) (hB : (S 2).length = B) (hr : (S 3).length = r) (hs : (S 4).length = s)
    (hZ : (S 6).length = Z) (a) (w : List Bool) :
    run trMBody (Function.update (trMG S a) 12 w) =
      Function.update (trMG S (trMStep r s B Z a)) 12 w := by
  obtain ⟨ms, out⟩ := a
  set S1 := Function.update (Function.update (trMG S (ms, out)) 12 w) 9 ms
  have hloop := run_forN 13 4 trCBody (trCG S1) (trCStep r s B)
    (fun a w' => run_trCBody S1 (by simp [S1, trMG, h10]) (by simp [S1, trMG, h11])
      (by simp [S1, trMG, h14]) (by simp [S1, trMG, h16]) (by simp [S1, trMG, h17])
      (by simp [S1, trMG, hB]) (by simp [S1, trMG, hr]) (by simp [S1, trMG, hs]) a w')
    (ms, out) S1 (by funext t; fin_cases t <;> simp [S1, trCG, trMG])
  have h4 : S1 4 = S 4 := by simp [S1, trMG]
  have hsplit : run trMBody (Function.update (trMG S (ms, out)) 12 w) =
      run (clr 9 ⨾ forN 15 3 (map tvS skipP) ⨾ map tvF (fillP false))
        (run (forN 13 4 trCBody) S1) := by
    simp only [trMBody, run_seq, run_copy]
    rw [show Function.update (trMG S (ms, out)) 12 w 8 = ms by simp [trMG]]
  rw [hsplit, hloop, h4, hs]
  erw [pushSeq_iter B (r * B) (colTW r s B) (fun _ => length_colTW _ _ _ _) s ms out]
  set S2 := Function.update (trCG S1 (ms.drop (s * B),
    (out ++ concatN s (fun j => colTW r s B (ms.drop (j * B)))).drop (s * (r * B)))) 13 []
  have hloop2 := run_forN 15 3 (map tvS skipP) (fun v => Function.update (run (clr 9) S2) 8 v)
    (fun v => v.drop (s * B)) (fun v w' => by
      rw [run_skipP_map tvS_inj _ (by simp [tvS, S2, trCG, S1, trMG, h16])
        (by simp [tvS, S2, trCG, S1, trMG, h17])]
      funext t; fin_cases t <;> simp [tvS, S2, trCG, S1, trMG, hs, hB])
    ms (run (clr 9) S2) (by funext t; fin_cases t <;> simp [S2, trCG, S1, trMG])
  simp only [run_seq]
  rw [hloop2, iterate_dropN]
  rw [run_fillP_map tvF_inj _ _ (by simp [tvF, S2, trCG, S1, trMG, h16])]
  have hd := drop_append_drop out (concatN s (fun j => colTW r s B (ms.drop (j * B))))
    (List.replicate Z false)
  rw [length_concatN (fun _ _ => length_colTW _ _ _ _), List.length_replicate] at hd
  funext t
  simp only [trCG, trMG, trMStep, S1, S2, matTW]
  fin_cases t <;> simp [tvF, h9, h13, h15, hZ, hr, hd, Nat.mul_assoc]

set_option linter.unusedSimpArgs false in
/-- **The transposes of `m` block matrices.** -/
theorem run_trP {B r s m Z : ℕ} (S : Store 20) (hS : ∀ i : Fin 20, 8 ≤ i.val → S i = [])
    (hB : (S 2).length = B) (hr : (S 3).length = r) (hs : (S 4).length = s)
    (hm : (S 5).length = m) (hZ : (S 6).length = Z)
    (hT : (S 7).length = m * (s * (r * B) + Z)) :
    run trP S = Function.update S 0 (trW m r s B Z (S 1)) := by
  set S1 := Function.update (Function.update S 0 (S 7)) 8 (S 1)
  have hloop := run_forN 12 5 trMBody (trMG S1) (trMStep r s B Z)
    (fun a w => run_trMBody S1 (by simp [S1, hS]) (by simp [S1, hS]) (by simp [S1, hS])
      (by simp [S1, hS]) (by simp [S1, hS]) (by simp [S1, hS]) (by simp [S1, hS])
      (by simp [S1, hS]) (by simp [S1, hB]) (by simp [S1, hr]) (by simp [S1, hs])
      (by simp [S1, hZ]) a w)
    (S 1, S 7) S1 (by funext t; fin_cases t <;> simp [S1, trMG])
  have hsplit : run trP S = run (clr 8) (run (forN 12 5 trMBody) S1) := by
    simp only [trP, run_seq, run_copy]
    rw [show Function.update S 0 (S 7) 1 = S 1 by simp]
  have h5 : S1 5 = S 5 := by simp [S1]
  rw [hsplit, hloop, h5, hm]
  erw [pushSeq_iter (r * (s * B)) (s * (r * B) + Z)
    (fun ms => matTW r s B ms ++ List.replicate Z false)
    (fun _ => by simp [length_matTW]) m (S 1) (S 7)]
  rw [drop_append_of_length hT]
  funext t
  simp only [trMG, S1, trW]
  fin_cases t <;> simp [hS]

theorem run_trP_map {u : Fin 20 → Fin k} (hu : Function.Injective u) {B r s m Z : ℕ} (S : Store k)
    (hS : ∀ i : Fin 20, 8 ≤ i.val → S (u i) = []) (hB : (S (u 2)).length = B)
    (hr : (S (u 3)).length = r) (hs : (S (u 4)).length = s) (hm : (S (u 5)).length = m)
    (hZ : (S (u 6)).length = Z) (hT : (S (u 7)).length = m * (s * (r * B) + Z)) :
    run (map u trP) S = Function.update S (u 0) (trW m r s B Z (S (u 1))) :=
  run_map_eq_update hu _ S 0 _ (run_trP _ hS hB hr hs hm hZ hT)

theorem noGrow_trP : trP.NoGrow := rfl
theorem wf_trP : trP.WF := wf_of_wfB (by decide)

/-! ### Selection by bits -/

def svM : Fin 5 → Fin 13 := ![10, 0, 11, 12, 4]
theorem svM_inj : Function.Injective svM := by decide

/-- A bit: pop it, shift the selected block into the output. -/
def selBody : Prog 13 := pp 7 8 ⨾ ifBit 8 (cp 10 2) (cp 10 3) ⨾ map svM mvP ⨾ clr 10 ⨾ clr 8

/-- **Blocks selected by bits.** -/
def selP : Prog 13 := cp 0 6 ⨾ cp 7 1 ⨾ forN 9 5 selBody ⨾ clr 7

def selG (S : Store 13) : List Bool × List Bool → Store 13
  | (xs, out) => Function.update (Function.update S 7 xs) 0 out

set_option linter.unusedSimpArgs false in
theorem run_selBody {B : ℕ} (S : Store 13) (h8 : S 8 = []) (h10 : S 10 = []) (h11 : S 11 = [])
    (h12 : S 12 = []) (hB : (S 4).length = B) (a) (w : List Bool) :
    run selBody (Function.update (selG S a) 9 w) =
      Function.update (selG S ((fun a : List Bool × List Bool => (a.1.drop 1,
        (a.2 ++ takeD B (if hd a.1 then S 2 else S 3)).drop B)) a)) 9 w := by
  obtain ⟨xs, out⟩ := a
  have hh : ∀ l : List Bool, hd (l.take 1) = hd l := by intro l; cases l <;> rfl
  simp only [selBody, run_seq, run_copy, run_clear, run_pop, run_ifBit, selG]
  split_ifs with h <;>
    rw [run_mvP_map svM_inj _ (by simp [svM, h11]) (by simp [svM, h12])] <;>
    funext t <;> fin_cases t <;> simp_all [svM, List.drop_one]

set_option linter.unusedSimpArgs false in
/-- **Blocks selected by bits.** -/
theorem run_selP {B n : ℕ} (S : Store 13) (hS : ∀ i : Fin 13, 7 ≤ i.val → S i = [])
    (hB : (S 4).length = B) (hn : (S 5).length = n) (hT : (S 6).length = n * B) :
    run selP S = Function.update S 0 (selW n B (S 1) (S 2) (S 3)) := by
  set S1 := Function.update (Function.update S 0 (S 6)) 7 (S 1)
  have hloop := run_forN 9 5 selBody (selG S1) _
    (fun a w => run_selBody (B := B) S1 (by simp [S1, hS]) (by simp [S1, hS]) (by simp [S1, hS])
      (by simp [S1, hS]) (by simp [S1, hB]) a w)
    (S 1, S 6) S1 (by funext t; fin_cases t <;> simp [S1, selG])
  have hsplit : run selP S = run (clr 7) (run (forN 9 5 selBody) S1) := by
    simp only [selP, run_seq, run_copy]
    rw [show Function.update S 0 (S 6) 1 = S 1 by simp]
  have h5 : S1 5 = S 5 := by simp [S1]
  have h2 : S1 2 = S 2 := by simp [S1]
  have h3 : S1 3 = S 3 := by simp [S1]
  rw [hsplit, hloop, h5, hn, h2, h3]
  erw [pushSeq_iter 1 B (fun xs => takeD B (if hd xs then S 2 else S 3))
    (fun _ => length_takeD _ _) n (S 1) (S 6)]
  rw [drop_append_of_length (by rw [hT])]
  funext t
  simp only [selG, S1, selW]
  fin_cases t <;> simp [hS]

theorem run_selP_map {u : Fin 13 → Fin k} (hu : Function.Injective u) {B n : ℕ} (S : Store k)
    (hS : ∀ i : Fin 13, 7 ≤ i.val → S (u i) = []) (hB : (S (u 4)).length = B)
    (hn : (S (u 5)).length = n) (hT : (S (u 6)).length = n * B) :
    run (map u selP) S = Function.update S (u 0) (selW n B (S (u 1)) (S (u 2)) (S (u 3))) :=
  run_map_eq_update hu _ S 0 _ (run_selP _ hS hB hn hT)

theorem noGrow_selP : selP.NoGrow := rfl
theorem wf_selP : selP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
