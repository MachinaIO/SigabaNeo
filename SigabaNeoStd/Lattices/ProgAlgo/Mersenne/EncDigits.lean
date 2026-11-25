import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncZRow
import SigabaNeoStd.Lattices.ProgAlgo.Digits

/-!
# Digit encodings modulo `2^K − 1`

The digit encodings of a gadget ciphertext `C` (ePrint 2026/2539 §4.2, Mul; the components `c^aut`
and `c^in` of `Enc`): for every entry `C_j` (in the order of its word) and every digit `i < K`, the
row `s' A_{j,i} − (d_i(C_j) · (s', 1)) G + e_{j,i}`, where `d_i` is the `i`-th binary digit.
**`deP : Prog 74`** (`run_deP`): for `|14|` entries of the stream `2`, with the secret `1`, the
matrix stream `3` and the error stream `4` (both consumed, `mrowP`), the rows are shifted into the
output register `0`; the digit `i` is the digit `0` of the `i`-fold rotation (`rotBP` by one bit,
template `13` of length `1`).

Tapes: `0` output, `1` `s'`, `2` the entries, `3` `A`, `4` `E`, templates `5` (`K`), `6` (`N`),
`7` (`N K`), `8` (`L`), `9` (`K − 1`), `10` (`2 K · N K`), `11` (`L · N K`), `12` (`2 L · N K`),
`13` (length `1`), `14` (the number of entries); scratch `15 … 73`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The row of a digit word `dg`: `s' A + A' − zStream dg s' + E` (`A' = A` dropped by a row). -/
def deRow (N K L : ℕ) (s' dg A E : List Bool) : List Bool :=
  rowW N K L s' A (A.drop (L * (N * K))) (Prog.zStream N K dg s') E

/-- One digit: the row of the digit `0` of `cur`, then `cur` rotated by one bit. -/
def deIn (N K L : ℕ) (s' : List Bool) :
    List Bool × List Bool × List Bool × List Bool → List Bool × List Bool × List Bool × List Bool
  | (cur, out, A, E) => (rotBW N K 1 cur,
      (out ++ deRow N K L s' (digitRW N K 0 cur) A E).drop (L * (N * K)),
      A.drop ((L + L) * (N * K)), E.drop (L * (N * K)))

/-- One entry: its `K` digits. -/
def deOut (N K L : ℕ) (s' : List Bool) :
    List Bool × List Bool × List Bool × List Bool → List Bool × List Bool × List Bool × List Bool
  | (C, out, A, E) =>
    let r := (deIn N K L s')^[K] (takeD (N * K) C, out, A, E)
    (C.drop (N * K), r.2.1, r.2.2.1, r.2.2.2)

namespace Prog

open scoped Prog

/-- `digitRWP`: `16 := digit 0 of 15` (count tape `20`, blank). -/
def dDig : Fin 31 → Fin 74 := ![16, 15, 20, 5, 6, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
  34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
/-- `mrowP` with `y` the copy `19` of `s'`, `u` the digit `16`. -/
def dRow : Fin 66 → Fin 74 := ![0, 1, 19, 16, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
  51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]
/-- `rotBP`: `21 := rotBW 1 15`. -/
def dRot : Fin 30 → Fin 74 := ![21, 15, 13, 5, 6, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
  34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
/-- `mvP`: the next entry of `2` into `15`. -/
def dMv : Fin 5 → Fin 74 := ![2, 15, 22, 23, 7]

set_option maxRecDepth 10000 in
theorem dDig_inj : Function.Injective dDig := by decide
set_option maxRecDepth 10000 in
theorem dRow_inj : Function.Injective dRow := by decide
set_option maxRecDepth 10000 in
theorem dRot_inj : Function.Injective dRot := by decide
set_option maxRecDepth 10000 in
theorem dMv_inj : Function.Injective dMv := by decide

/-- One digit. -/
def deBody : Prog 74 :=
  map dDig digitRWP ⨾ map dRow mrowP ⨾ map dRot rotBP ⨾ cp 15 21 ⨾ clr 21 ⨾ clr 16

/-- One entry. -/
def deEntry : Prog 74 :=
  cp 15 7 ⨾ map dMv mvP ⨾ cp 19 1 ⨾ forN 18 5 deBody ⨾ clr 15 ⨾ clr 19

/-- **The digit encodings.** -/
def deP : Prog 74 := forN 17 14 deEntry

/-- The store of a digit round. -/
def dG (S : Store 74) : List Bool × List Bool × List Bool × List Bool → Store 74
  | (cur, out, A, E) =>
    Function.update (Function.update (Function.update (Function.update S 15 cur) 0 out) 3 A) 4 E

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_deBody {K N L : ℕ} (hK : 0 < K) (S : Store 74)
    (hS : ∀ i : Fin 74, 16 ≤ i.val → i.val ≠ 17 → i.val ≠ 18 → i.val ≠ 19 → S i = [])
    (hK' : (S 5).length = K) (hN : (S 6).length = N) (hNK : (S 7).length = N * K)
    (hL : (S 8).length = L) (hK1 : (S 9).length = K - 1) (h10 : (S 10).length = (K + K) * (N * K))
    (h11 : (S 11).length = L * (N * K)) (h12 : (S 12).length = (L + L) * (N * K))
    (h13 : (S 13).length = 1) (h1 : (S 1).length = N * K) (h19 : S 19 = S 1)
    (a : List Bool × List Bool × List Bool × List Bool) (ha : a.1.length = N * K) (w : List Bool) :
    run deBody (Function.update (dG S a) 18 w) =
      Function.update (dG S (deIn N K L (S 1) a)) 18 w := by
  obtain ⟨cur, out, A, E⟩ := a
  simp only at ha
  have hd : (digitRW N K 0 cur).length = N * K := length_concatN fun _ _ => length_bitW _ _
  simp only [deBody, run_seq, run_copy, run_clear]
  rw [run_digitRWP_map' dDig_inj (K := K) (N := N) (i := 0) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [dDig, dG, hS] at hi ⊢
  · simp [dDig, dG, hS]
  · simp [dDig, dG, hK']
  · simp [dDig, dG, hN]
  · simp [dDig, dG, ha]
  rw [run_mrowP_map' dRow_inj (K := K) (N := N) (L := L) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [dRow, dDig, dG, hS] at hi ⊢
  · simp [dRow, dDig, dG, hK']
  · simp [dRow, dDig, dG, hN]
  · simp [dRow, dDig, dG, hNK]
  · simp [dRow, dDig, dG, hL]
  · simp [dRow, dDig, dG, hK1]
  · simp [dRow, dDig, dG, h10]
  · simp [dRow, dDig, dG, h11]
  · simp [dRow, dDig, dG, h12]
  · simp [dRow, dDig, dG, h1]
  · simp [dRow, dDig, dG, hd]
  rw [run_rotBP_map dRot_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [dRot, dRow, dDig, dG, hS] at hi ⊢
  · simp [dRot, dRow, dDig, dG, hK']
  · simp [dRot, dRow, dDig, dG, hN]
  · simp [dRot, dRow, dDig, dG, ha]
  funext t
  fin_cases t <;> simp [dRot, dRow, dDig, dG, hS, h13, h19, deIn, deRow, h11, h12]
where
  run_digitRWP_map' {u : Fin 31 → Fin 74} (hu : Function.Injective u) {K N i : ℕ} (s : Store 74)
      (hs : ∀ j : Fin 31, 5 ≤ j.val → s (u j) = []) (hi : (s (u 2)).length = i)
      (hK : (s (u 3)).length = K) (hN : (s (u 4)).length = N) (hw : (s (u 1)).length = N * K) :
      run (map u digitRWP) s = Function.update s (u 0) (digitRW N K i (s (u 1))) :=
    run_map_eq_update hu _ s 0 _ (run_digitRWP (s ∘ u) hs hi hK hN hw)
  run_mrowP_map' {u : Fin 66 → Fin 74} (hu : Function.Injective u) {K N L : ℕ} (hK : 0 < K)
      (s : Store 74) (hs : ∀ i : Fin 66, 14 ≤ i.val → s (u i) = []) (hK' : (s (u 6)).length = K)
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

/-- The store of an entry round. -/
def eG (S : Store 74) : List Bool × List Bool × List Bool × List Bool → Store 74
  | (C, out, A, E) =>
    Function.update (Function.update (Function.update (Function.update S 2 C) 0 out) 3 A) 4 E

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_deEntry {K N L : ℕ} (hK : 0 < K) (S : Store 74)
    (hS : ∀ i : Fin 74, 15 ≤ i.val → i.val ≠ 17 → S i = [])
    (hK' : (S 5).length = K) (hN : (S 6).length = N) (hNK : (S 7).length = N * K)
    (hL : (S 8).length = L) (hK1 : (S 9).length = K - 1) (h10 : (S 10).length = (K + K) * (N * K))
    (h11 : (S 11).length = L * (N * K)) (h12 : (S 12).length = (L + L) * (N * K))
    (h13 : (S 13).length = 1) (h1 : (S 1).length = N * K)
    (a : List Bool × List Bool × List Bool × List Bool) (w : List Bool) :
    run deEntry (Function.update (eG S a) 17 w) =
      Function.update (eG S (deOut N K L (S 1) a)) 17 w := by
  obtain ⟨C, out, A, E⟩ := a
  set S0 := Function.update (Function.update (Function.update S 2 (C.drop (N * K))) 17 w) 19 (S 1)
    with hS0
  have hS0c : ∀ i : Fin 74, 16 ≤ i.val → i.val ≠ 17 → i.val ≠ 18 → i.val ≠ 19 → S0 i = [] := by
    intro i hi h17 h18 h19
    have h2 : i ≠ 2 := fun h => by subst h; simp at hi
    have h17' : i ≠ 17 := fun h => by subst h; simp at h17
    have h19' : i ≠ 19 := fun h => by subst h; simp at h19
    rw [hS0, Function.update_of_ne h19', Function.update_of_ne h17', Function.update_of_ne h2]
    exact hS i (by omega) h17
  have e3 : run (cp 19 1) (run (map dMv mvP) (run (cp 15 7)
      (Function.update (eG S (C, out, A, E)) 17 w))) = dG S0 (takeD (N * K) C, out, A, E) := by
    simp only [run_copy]
    rw [run_mvP_map dMv_inj _ (by simp [dMv, eG, hS]) (by simp [dMv, eG, hS])]
    funext t
    fin_cases t <;> simp [S0, dG, eG, dMv, hNK, drop_append_of_length, hS]
  have hloop := run_forN_inv 18 5 deBody (dG S0) (deIn N K L (S 1)) (fun a => a.1.length = N * K)
    (fun a w' ha => by
      have := run_deBody (K := K) (N := N) (L := L) hK S0 hS0c (by simp [S0, hK']) (by simp [S0, hN]) (by simp [S0, hNK])
        (by simp [S0, hL]) (by simp [S0, hK1]) (by simp [S0, h10]) (by simp [S0, h11])
        (by simp [S0, h12]) (by simp [S0, h13]) (by simp [S0, h1]) (by simp [S0]) a ha w'
      rwa [show S0 1 = S 1 by simp [S0]] at this)
    (fun a ha => by obtain ⟨c, o, A', E'⟩ := a; exact length_rotBW N K 1 ha)
    (takeD (N * K) C, out, A, E) (length_takeD _ _) (dG S0 (takeD (N * K) C, out, A, E))
    (by funext t; fin_cases t <;> simp [dG, S0, hS])
  simp only [deEntry, run_seq, run_clear]
  rw [e3, hloop, show dG S0 (takeD (N * K) C, out, A, E) 5 = S 5 by simp [dG, S0], hK']
  simp only [deOut]
  funext t
  generalize (deIn N K L (S 1))^[K] (takeD (N * K) C, out, A, E) = r
  obtain ⟨c, o, A', E'⟩ := r
  fin_cases t <;> simp [dG, eG, S0, hS]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The digit encodings**: `|14|` entries of `2`, their rows shifted into `0`, the streams
consumed. -/
theorem run_deP {K N L : ℕ} (hK : 0 < K) (s : Store 74)
    (hs : ∀ i : Fin 74, 15 ≤ i.val → s i = [])
    (hK' : (s 5).length = K) (hN : (s 6).length = N) (hNK : (s 7).length = N * K)
    (hL : (s 8).length = L) (hK1 : (s 9).length = K - 1) (h10 : (s 10).length = (K + K) * (N * K))
    (h11 : (s 11).length = L * (N * K)) (h12 : (s 12).length = (L + L) * (N * K))
    (h13 : (s 13).length = 1) (h1 : (s 1).length = N * K) :
    run deP s = eG s ((deOut N K L (s 1))^[(s 14).length] (s 2, s 0, s 3, s 4)) := by
  have h := run_forN 17 14 deEntry (eG s) (deOut N K L (s 1))
    (fun a w => run_deEntry hK s (fun i hi _ => hs i hi) hK' hN hNK hL hK1 h10 h11 h12 h13 h1 a w)
    (s 2, s 0, s 3, s 4) s (by funext t; fin_cases t <;> simp [eG])
  rw [deP, h]
  funext t
  generalize (deOut N K L (s 1))^[(s 14).length] (s 2, s 0, s 3, s 4) = r
  obtain ⟨C, o, A, E⟩ := r
  fin_cases t <;> simp [eG, hs]

theorem noGrow_deP : deP.NoGrow := rfl
theorem wf_deP : deP.WF := wf_of_wfB (by decide)

/-! ### Certificate -/

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The inputs of `deP` (variables `top, N, K, L, nE`); the count tape `20` of the digit is blank. -/
def σD' : Asg := [pTop, pNK, pTop, pTop, pTop, pK, pN, pNK, pm, pK, p2NKK, mo 1 [1, 1, 1],
  mo 2 [1, 1, 1], pC 1, pn]
def σD : Asg := σD' ++ List.replicate 5 pTop ++ [[]] ++ List.replicate 53 pTop

/-- A bound of the sweeps of `deP`: `nE K` rows. -/
def wD : Poly := [([], 100), ([0, 0, 0, 0, 1], 200), ([0, 0, 1, 0, 1], 1300), ([0, 0, 1, 1, 1], 1000), ([0, 0, 2, 0, 1], 1100), ([0, 0, 2, 1, 1], 1000), ([0, 0, 3, 0, 1], 200), ([0, 1, 1, 0, 1], 1300), ([0, 1, 1, 1, 1], 1000), ([0, 1, 2, 0, 1], 1300), ([0, 1, 2, 1, 1], 1100), ([0, 1, 3, 0, 1], 1100), ([0, 1, 4, 0, 1], 200), ([0, 2, 1, 0, 1], 1000), ([0, 2, 1, 1, 1], 1000), ([0, 2, 2, 0, 1], 1000), ([0, 2, 2, 1, 1], 1000), ([0, 2, 3, 0, 1], 22), ([0, 2, 3, 1, 1], 30)]

set_option maxRecDepth 100000 in
/-- **The certificate of `deP`.** -/
theorem check_deP : check 8 deP σD σD' wD = true := by decide +kernel

/-- The sweeps of `deP`: per entry `K` rows of `L` entries (`rowSweeps`) and the digits. -/
def deSweeps (N K L nE : ℕ) : ℕ := 100 + nE * (200 + K * (rowSweeps N K L + 200 + 200 * N +
  100 * K + 200 * (N * K) + 100 * (N * K ^ 2)) + 100 * (N * K))

set_option maxHeartbeats 4000000 in
theorem time_deP {M N K L nE : ℕ} {ℓ : Fin 74 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K L nE 0 0) σD)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT deP ℓ ≤ (2 * M + 3) * deSweeps N K L nE := by
  refine (bounds_of_check check_deP (vars M N K L nE 0 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wD, pEval, mEval, vars, top, deSweeps, rowSweeps]
  ring

end Cert

end Prog

end SigabaNeo.Tape
