import SigabaNeo.Lib.Lattices.ProgAlgo.Transpose

/-!
# Sums selected by bits, as a tape program

`hashP : Prog 45` (tapes `0` output, `1` a bit stream `w`, `2` a word `V` of `d` ring entries,
`3` a word `E` of `P` ring entries, templates `4` … `9` of lengths `K`, `N`, `N K`, `d`, `P`,
`P · N K`; scratch `10 … 44`): for each `p < P`, the ring word

  `∑_{a < d, w_{p d + a} = 1} V_a + E_p`

(the sum of the entries of `V` selected by the bits `p d, …, p d + d − 1` of `w`, plus the entry
`p` of `E`), all shifted into the output (`hashW`, `run_hashP`). With `V = B₀` and the bits of the
binary matrices `W_j` this is `B₀ W_j + E` (`B_j` and the encodings `c_j` of the scheme).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo

variable {k : ℕ}

/-! ### Words -/

/-- The sum of the first `a` entries of `V` selected by the bits of `ws`. -/
def csum (N K : ℕ) : ℕ → List Bool → List Bool → List Bool
  | 0, _, _ => zeroW (N * K)
  | a + 1, ws, V => if hd (ws.drop a) then addRW N K (csum N K a ws V) (takeD (N * K) (V.drop (a * (N * K))))
      else csum N K a ws V

theorem length_csum (N K : ℕ) : ∀ (a : ℕ) (ws V : List Bool), (csum N K a ws V).length = N * K
  | 0, _, _ => by simp [csum, zeroW]
  | a + 1, ws, V => by
    rw [csum]; split_ifs
    · exact length_addRW N K (length_csum N K a ws V) _
    · exact length_csum N K a ws V

/-- **Sums selected by bits.** -/
def hashW (P d N K : ℕ) (w V E : List Bool) : List Bool :=
  concatN P (fun p => addRW N K (csum N K d (w.drop (p * d)) V) (takeD (N * K) (E.drop (p * (N * K)))))

theorem length_hashW (P d N K : ℕ) (w V E : List Bool) : (hashW P d N K w V E).length = P * (N * K) :=
  length_concatN fun _ _ => length_addRW N K (length_csum _ _ _ _ _) _

/-- Shifting into a register a word computed from two streams. -/
theorem pushSeq2_iter (d e c : ℕ) (g : List Bool → List Bool → List Bool)
    (hg : ∀ s t, (g s t).length = c) :
    ∀ (m : ℕ) (sv tv out : List Bool),
      (fun a : List Bool × List Bool × List Bool =>
        (a.1.drop d, a.2.1.drop e, (a.2.2 ++ g a.1 a.2.1).drop c))^[m] (sv, tv, out) =
        (sv.drop (m * d), tv.drop (m * e),
          (out ++ concatN m (fun j => g (sv.drop (j * d)) (tv.drop (j * e)))).drop (m * c))
  | 0, sv, tv, out => by simp [concatN]
  | m + 1, sv, tv, out => by
    rw [Function.iterate_succ_apply', pushSeq2_iter d e c g hg m sv tv out]
    have hl : (concatN m (fun j => g (sv.drop (j * d)) (tv.drop (j * e)))).length = m * c :=
      length_concatN fun j _ => hg _ _
    have := drop_append_drop out (concatN m (fun j => g (sv.drop (j * d)) (tv.drop (j * e))))
      (g (sv.drop (m * d)) (tv.drop (m * e)))
    rw [hl, hg] at this
    simp only [List.drop_drop, this, concatN, Nat.succ_mul]

namespace Prog

open scoped Prog

def hvV : Fin 5 → Fin 45 := ![12, 15, 20, 21, 6]
def hvE : Fin 5 → Fin 45 := ![11, 19, 20, 21, 6]
def hvO : Fin 5 → Fin 45 := ![16, 0, 20, 21, 6]
def hvA : Fin 28 → Fin 45 := ![16, 13, 15, 4, 5, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def hvB : Fin 28 → Fin 45 := ![16, 13, 19, 4, 5, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
theorem hvV_inj : Function.Injective hvV := by decide
theorem hvE_inj : Function.Injective hvE := by decide
theorem hvO_inj : Function.Injective hvO := by decide
theorem hvA_inj : Function.Injective hvA := by decide
theorem hvB_inj : Function.Injective hvB := by decide

/-- A term: pop a bit of `w` (`10`), read the next entry of `V` (`12`), add it to the accumulator
(`13`) if the bit is set. -/
def hABody : Prog 45 :=
  pp 10 14 ⨾ cp 15 6 ⨾ map hvV mvP ⨾ ifBit 14 (map hvA addRWP ⨾ cp 13 16 ⨾ clr 16) (nop 16) ⨾
    clr 15 ⨾ clr 14

/-- An entry: the selected sum, plus the next entry of `E` (`11`), shifted into the output. -/
def hPBody : Prog 45 :=
  cp 13 6 ⨾ setZero 13 ⨾ cp 12 2 ⨾ forN 18 7 hABody ⨾ cp 19 6 ⨾ map hvE mvP ⨾ map hvB addRWP ⨾
    map hvO mvP ⨾ clr 12 ⨾ clr 13 ⨾ clr 16 ⨾ clr 19

/-- **Sums selected by bits.** -/
def hashP : Prog 45 := cp 0 9 ⨾ cp 10 1 ⨾ cp 11 3 ⨾ forN 17 8 hPBody ⨾ clr 10 ⨾ clr 11

/-- The abstract term: (bit stream, entry stream, accumulator). -/
def hAStep (N K : ℕ) : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (ws, vs, acc) => (ws.drop 1, vs.drop (N * K),
      if hd ws then addRW N K acc (takeD (N * K) vs) else acc)

def hAG (S : Store 45) : List Bool × List Bool × List Bool → Store 45
  | (ws, vs, acc) => Function.update (Function.update (Function.update S 10 ws) 12 vs) 13 acc

theorem hAStep_iter (N K : ℕ) (ws V : List Bool) : ∀ a,
    (hAStep N K)^[a] (ws, V, zeroW (N * K)) = (ws.drop a, V.drop (a * (N * K)), csum N K a ws V)
  | 0 => by simp [csum]
  | a + 1 => by
    rw [Function.iterate_succ_apply', hAStep_iter N K ws V a, hAStep, csum, List.drop_drop,
      List.drop_drop]
    congr 2; ring_nf

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem run_hABody {K N : ℕ} (S : Store 45) (hS : ∀ i : Fin 45, (14 ≤ i.val ∧ i.val ≤ 16) ∨
    20 ≤ i.val → S i = []) (hK : (S 4).length = K) (hN : (S 5).length = N)
    (hNK : (S 6).length = N * K) (a) (ha : a.2.2.length = N * K) (w : List Bool) :
    run hABody (Function.update (hAG S a) 18 w) = Function.update (hAG S (hAStep N K a)) 18 w := by
  obtain ⟨ws, vs, acc⟩ := a
  simp only at ha
  have hh : ∀ l : List Bool, hd (l.take 1) = hd l := by intro l; cases l <;> rfl
  simp only [hABody, run_seq, run_copy, run_clear, run_pop, hAG]
  rw [run_mvP_map hvV_inj _ (by simp [hvV, hS]) (by simp [hvV, hS])]
  simp only [run_ifBit, run_seq, run_copy, run_clear, run_nop]
  by_cases hx : hd ws = true
  · rw [ite_eq_left_iff.mpr (by simp [hvV, hh, hx])]
    rw [run_addRWP_map hvA_inj (K := K) (N := N) _ (fun i hi => by fin_cases i <;> simp [hvA, hvV, hS] at hi ⊢)
      (by simp [hvA, hvV, hK]) (by simp [hvA, hvV, hN]) (by simp [hvA, hvV, ha]) (by simp [hvA, hvV, hNK, drop_append_of_length])]
    funext t
    simp only [hAStep]
    fin_cases t <;> simp [hvA, hvV, hNK, drop_append_of_length, List.drop_one, hx, hS, ha]
  · rw [if_neg (by simp [hvV, hh, hx])]
    funext t
    simp only [hAStep]
    fin_cases t <;> simp [hvA, hvV, hNK, drop_append_of_length, List.drop_one, hx, hS, ha]

/-- The abstract entry: (bit stream, entry stream of `E`, output register). -/
def hPG (S : Store 45) : List Bool × List Bool × List Bool → Store 45
  | (ws, es, out) => Function.update (Function.update (Function.update S 10 ws) 11 es) 0 out

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem run_hPBody {K N d : ℕ} (S : Store 45) (hS : ∀ i : Fin 45, 12 ≤ i.val → i ≠ 17 → S i = [])
    (hK : (S 4).length = K) (hN : (S 5).length = N) (hNK : (S 6).length = N * K)
    (hd : (S 7).length = d) (a) (w : List Bool) :
    run hPBody (Function.update (hPG S a) 17 w) =
      Function.update (hPG S ((fun a : List Bool × List Bool × List Bool =>
        (a.1.drop d, a.2.1.drop (N * K), (a.2.2 ++ addRW N K (csum N K d a.1 (S 2))
          (takeD (N * K) a.2.1)).drop (N * K))) a)) 17 w := by
  obtain ⟨ws, es, out⟩ := a
  set S0 := Function.update (hPG S (ws, es, out)) 17 w
  set S1 := run (cp 12 2) (run (setZero 13) (run (cp 13 6) S0))
  have e1 : S1 = hAG S0 (ws, S 2, zeroW (N * K)) := by
    funext t; simp only [S1, S0, run_copy, run_setZero, hAG, hPG]
    fin_cases t <;> simp [hS, hNK, zeroW]
  have hloop := run_forN_inv 18 7 hABody (hAG S0) (hAStep N K) (fun a => a.2.2.length = N * K)
    (fun a w' ha => run_hABody S0 (fun i hi => by fin_cases i <;> simp [S0, hPG, hS] at hi ⊢)
      (by simp [S0, hPG, hK]) (by simp [S0, hPG, hN]) (by simp [S0, hPG, hNK]) a ha w')
    (fun a ha => by
      obtain ⟨_, _, _⟩ := a
      simp only [hAStep]; split_ifs
      · exact length_addRW N K ha _
      · exact ha)
    (ws, S 2, zeroW (N * K)) (by simp [zeroW]) S1 (by rw [e1])
  have hsplit : run hPBody S0 = run (cp 19 6 ⨾ map hvE mvP ⨾ map hvB addRWP ⨾ map hvO mvP ⨾
      clr 12 ⨾ clr 13 ⨾ clr 16 ⨾ clr 19) (run (forN 18 7 hABody) S1) := rfl
  have h7 : S1 7 = S 7 := by rw [e1]; simp [S0, hAG, hPG]
  rw [hsplit, hloop, h7, hd, hAStep_iter]
  have hc := length_csum N K d ws (S 2)
  simp only [run_seq, run_copy, run_clear]
  rw [run_mvP_map hvE_inj _ (by simp [hvE, hAG, S0, hPG, hS]) (by simp [hvE, hAG, S0, hPG, hS])]
  rw [run_addRWP_map hvB_inj (K := K) (N := N) _
    (fun i hi => by fin_cases i <;> simp [hvB, hvE, hAG, S0, hPG, hS] at hi ⊢)
    (by simp [hvB, hvE, hAG, S0, hPG, hK]) (by simp [hvB, hvE, hAG, S0, hPG, hN])
    (by simp [hvB, hvE, hAG, S0, hPG, hc]) (by simp [hvB, hvE, hAG, S0, hPG, hNK, drop_append_of_length])]
  rw [run_mvP_map hvO_inj _ (by simp [hvO, hvB, hvE, hAG, S0, hPG, hS])
    (by simp [hvO, hvB, hvE, hAG, S0, hPG, hS])]
  funext t
  simp only [hAG, hPG, S0]
  have htk : takeD (N * K) (addRW N K (csum N K d ws (S 2)) (takeD (N * K) es)) =
      addRW N K (csum N K d ws (S 2)) (takeD (N * K) es) := takeD_of_length' (length_addRW N K hc _)
  fin_cases t <;> simp [hvO, hvB, hvE, hS, hNK, drop_append_of_length, length_addRW, hc, htk]

set_option linter.unusedSimpArgs false in
/-- **Sums selected by bits.** -/
theorem run_hashP {K N d P : ℕ} (S : Store 45) (hS : ∀ i : Fin 45, 10 ≤ i.val → S i = [])
    (hK : (S 4).length = K) (hN : (S 5).length = N) (hNK : (S 6).length = N * K)
    (hd : (S 7).length = d) (hP : (S 8).length = P) (hT : (S 9).length = P * (N * K)) :
    run hashP S = Function.update S 0 (hashW P d N K (S 1) (S 2) (S 3)) := by
  set S1 := Function.update (Function.update (Function.update S 0 (S 9)) 10 (S 1)) 11 (S 3)
  have hloop := run_forN 17 8 hPBody (hPG S1) _
    (fun a w => run_hPBody (K := K) (N := N) (d := d) S1
      (fun i hi hi' => by fin_cases i <;> simp [S1, hS] at hi hi' ⊢) (by simp [S1, hK])
      (by simp [S1, hN]) (by simp [S1, hNK]) (by simp [S1, hd]) a w)
    (S 1, S 3, S 9) S1 (by funext t; fin_cases t <;> simp [S1, hPG])
  have hsplit : run hashP S = run (clr 10 ⨾ clr 11) (run (forN 17 8 hPBody) S1) := by
    simp only [hashP, run_seq, run_copy]
    rw [show Function.update S 0 (S 9) 1 = S 1 by simp,
      show Function.update (Function.update S 0 (S 9)) 10 (S 1) 3 = S 3 by simp]
  have h8 : S1 8 = S 8 := by simp [S1]
  have h2 : S1 2 = S 2 := by simp [S1]
  rw [hsplit, hloop, h8, hP, h2]
  erw [pushSeq2_iter d (N * K) (N * K) (fun ws es => addRW N K (csum N K d ws (S 2)) (takeD (N * K) es))
    (fun _ _ => length_addRW N K (length_csum _ _ _ _ _) _) P (S 1) (S 3) (S 9)]
  rw [drop_append_of_length hT]
  funext t
  simp only [hPG, S1, hashW]
  fin_cases t <;> simp [hS]

theorem run_hashP_map {u : Fin 45 → Fin k} (hu : Function.Injective u) {K N d P : ℕ} (S : Store k)
    (hS : ∀ i : Fin 45, 10 ≤ i.val → S (u i) = []) (hK : (S (u 4)).length = K)
    (hN : (S (u 5)).length = N) (hNK : (S (u 6)).length = N * K) (hd : (S (u 7)).length = d)
    (hP : (S (u 8)).length = P) (hT : (S (u 9)).length = P * (N * K)) :
    run (map u hashP) S = Function.update S (u 0) (hashW P d N K (S (u 1)) (S (u 2)) (S (u 3))) :=
  run_map_eq_update hu _ S 0 _ (run_hashP _ hS hK hN hNK hd hP hT)

theorem noGrow_hashP : hashP.NoGrow := rfl
theorem wf_hashP : hashP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
