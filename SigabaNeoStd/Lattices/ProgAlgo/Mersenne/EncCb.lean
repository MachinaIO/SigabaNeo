import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncZRow

/-!
# The attribute rows of `Enc` modulo `2^K − 1`

The bottom row of the attribute ciphertext `C^in_t` (ePrint 2026/2539 §5.1) is
`−s a_t + (X^{w x_t} (s, 1)) G + e_t`. **`cbP : Prog 74`** (`run_cbP`): from the next `8` bits of the
attribute stream `2` (most significant first), `u := ±` the product of the monomials of the set bits
(`rbitP`: `X^{−|τ|}` by `rhoJP` for a set bit), then the row `s (¬a) + 0 − zStream (¬u) s + e`
(`zrowP`) shifted into the output register `0`; the streams `2` (`8` bits), `3` (`a`, `L` entries)
and `4` (`e`, `L` entries) are consumed.

Tapes: `0` output, `1` `s`, `2` the attribute bits, `3` `a`, `4` `e`, `5` the word of `1`,
`6 … 13` the templates of the eight bits in reading order, templates `14` (`K`), `15` (`N`),
`16` (`N K`), `17` (`L`), `18` (`K − 1`), `19` (`2 K · N K`, also `L · N K` zeros); scratch
`20 … 73` (`24` stays blank: the stream `A₁ = 0`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- One bit: `u := X^{−t} u` if the next bit is set. -/
def rbitW (K t : ℕ) (b : Bool) (u : List Bool) : List Bool := if b then (rhoMW K)^[t] u else u

/-- The eight bits, in reading order, with the template lengths `τ j`. -/
def rbitsW (K : ℕ) (τ : ℕ → ℕ) (x : List Bool) : ℕ → List Bool → List Bool
  | 0, u => u
  | j + 1, u => rbitW K (τ j) (hd (x.drop j)) (rbitsW K τ x j u)

@[simp] theorem length_rbitsW (K : ℕ) (τ : ℕ → ℕ) (x u : List Bool) :
    ∀ j, (rbitsW K τ x j u).length = u.length
  | 0 => rfl
  | j + 1 => by
    unfold rbitsW rbitW
    split_ifs <;> simp [length_rbitsW K τ x u j]

namespace Prog

open scoped Prog

/-- `rhoJP`: `3 := X^{−|4|} 0`. -/
def bRho : Fin 7 → Fin 9 := ![3, 0, 4, 5, 6, 7, 8]

set_option maxRecDepth 10000 in
theorem bRho_inj : Function.Injective bRho := by decide

/-- **One bit**: tapes `0` `u`, `1` the bits, `2` flag, `3` scratch, `4` the template, `5` `K`;
scratch `6 … 8`. -/
def rbitP : Prog 9 := pp 1 2 ⨾ ifBit 2 (map bRho rhoJP ⨾ cp 0 3 ⨾ clr 3) (clr 3) ⨾ clr 2

theorem run_rbitP (s : Store 9) (hs : ∀ i : Fin 9, 2 ≤ i.val → i.val ≠ 4 → i.val ≠ 5 → s i = []) :
    run rbitP s = Function.update (Function.update s 0
      (rbitW (s 5).length (s 4).length (hd (s 1)) (s 0))) 1 (s 1).tail := by
  simp only [rbitP, run_seq, run_pop, run_clear]
  rw [run_ifBit]
  cases h : s 1 with
  | nil =>
    simp [hd, rbitW, h]
    funext t; fin_cases t <;> simp [hs]
  | cons b w =>
    cases b
    · simp [hd, rbitW]
      funext t; fin_cases t <;> simp [hs, h]
    · simp only [Function.update_self, List.take_succ_cons, List.take_zero, List.head?_cons,
        ite_true, run_seq, run_copy, run_clear]
      rw [run_rhoJP_map bRho_inj _ (fun i hi => by fin_cases i <;> simp [bRho, hs] at hi ⊢)]
      funext t; fin_cases t <;> simp [bRho, hs, h, rbitW]

theorem run_rbitP_map {u : Fin 9 → Fin k} (hu : Function.Injective u) (s : Store k)
    (hs : ∀ i : Fin 9, 2 ≤ i.val → i.val ≠ 4 → i.val ≠ 5 → s (u i) = []) :
    run (map u rbitP) s = Function.update (Function.update s (u 0)
      (rbitW (s (u 5)).length (s (u 4)).length (hd (s (u 1))) (s (u 0)))) (u 1) (s (u 1)).tail := by
  rw [run_map hu, run_rbitP (s ∘ u) hs, extend_update hu, extend_update hu, extend_comp_self]
  rfl

theorem noGrow_rbitP : rbitP.NoGrow := rfl

/-- `rbitP` for the bit `j` (template `6 + j`). -/
def bMs : Fin 8 → Fin 9 → Fin 74 := fun j => ![20, 2, 21, 23, ⟨6 + j.val, by omega⟩, 14, 26, 27, 28]

set_option maxRecDepth 100000 in
theorem bMs_inj : ∀ j, Function.Injective (bMs j) := by decide

/-- `u := 1`, then the first `j` bits. -/
def bitsP : ℕ → Prog 74
  | 0 => cp 20 5
  | j + 1 => bitsP j ⨾ map (bMs ⟨j % 8, Nat.mod_lt _ (by decide)⟩) rbitP

/-- The template lengths of the bits. -/
def τOf (S : Store 74) (i : ℕ) : ℕ := (S ⟨6 + i % 8, by omega⟩).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem run_bitsP (S : Store 74) (hS : ∀ i : Fin 74, 20 ≤ i.val → S i = []) :
    ∀ j ≤ 8, run (bitsP j) S = Function.update (Function.update S 20
      (rbitsW (S 14).length (τOf S) (S 2) j (S 5))) 2 ((S 2).drop j)
  | 0, _ => by
    simp only [bitsP, run_copy, rbitsW, List.drop_zero]
    funext t
    by_cases h : t = 2
    · subst h; simp
    · simp [Function.update_apply, h]
  | j + 1, hj => by
    rw [bitsP, run_seq, run_bitsP S hS j (by omega), run_rbitP_map (bMs_inj _) _ ?_]
    · have hm : j % 8 = j := Nat.mod_eq_of_lt (by omega)
      have e2 : ¬ (6 + j = 2) := by omega
      have e20 : ¬ (6 + j = 20) := by omega
      funext t
      simp only [bMs, Function.update_apply]
      fin_cases t <;> simp [hm, rbitsW, τOf, List.tail_drop, Fin.ext_iff, e2, e20]
    · intro i hi h4 h5
      have hm : j % 8 = j := Nat.mod_eq_of_lt (by omega)
      fin_cases i <;> simp_all [bMs, hS]

/-- `notP`: `23 := ¬20`. -/
def cNt : Fin 11 → Fin 74 := ![23, 20, 26, 27, 28, 29, 30, 31, 32, 33, 34]
/-- `notP`: `23 := ¬22`. -/
def cNa : Fin 11 → Fin 74 := ![23, 22, 26, 27, 28, 29, 30, 31, 32, 33, 34]
/-- `mvP`: `22 := ` the next `L` entries of `a`. -/
def cMv : Fin 5 → Fin 74 := ![3, 22, 26, 27, 19]
/-- `zrowP`. -/
def cZ : Fin 61 → Fin 74 := ![0, 1, 25, 20, 22, 24, 4, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54,
  55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]
/-- `dropP` of the error stream. -/
def cD : Fin 3 → Fin 74 := ![4, 26, 19]

set_option maxRecDepth 10000 in
theorem cNt_inj : Function.Injective cNt := by decide
set_option maxRecDepth 10000 in
theorem cNa_inj : Function.Injective cNa := by decide
set_option maxRecDepth 10000 in
theorem cMv_inj : Function.Injective cMv := by decide
set_option maxRecDepth 10000 in
theorem cZ_inj : Function.Injective cZ := by decide
set_option maxRecDepth 10000 in
theorem cD_inj : Function.Injective cD := by decide

/-- **The bottom row of an attribute ciphertext.** -/
def cbP : Prog 74 :=
  bitsP 8 ⨾ map cNt notP ⨾ cp 20 23 ⨾ clr 23 ⨾ cp 22 19 ⨾ map cMv mvP ⨾ map cNa notP ⨾ cp 22 23 ⨾
    clr 23 ⨾ cp 25 1 ⨾ map cZ zrowP ⨾ map cD dropP ⨾ clr 20 ⨾ clr 22 ⨾ clr 25

/-- The row of `cbP`. -/
def cbRow (N K : ℕ) (τ : ℕ → ℕ) (s x a e one : List Bool) : List Bool :=
  rowW N K (K + K) s (notW (takeD ((K + K) * (N * K)) a)) []
    (zStream N K (notW (rbitsW K τ x 8 one)) s) e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The bottom row of an attribute ciphertext**: the row shifted into `0`, `8` bits of `2`, `L`
entries of `3` and of `4` consumed. -/
theorem run_cbP {K N : ℕ} (hK : 0 < K) (s : Store 74) (hs : ∀ i : Fin 74, 20 ≤ i.val → s i = [])
    (hK' : (s 14).length = K) (hN : (s 15).length = N) (hNK : (s 16).length = N * K)
    (hL : (s 17).length = K + K) (hK1 : (s 18).length = K - 1)
    (h19 : (s 19).length = (K + K) * (N * K)) (h1 : (s 1).length = N * K)
    (h5 : (s 5).length = N * K) :
    run cbP s = Function.update (Function.update (Function.update (Function.update s 0
      ((s 0 ++ cbRow N K (τOf s) (s 1) (s 2) (s 3) (s 4) (s 5)).drop ((K + K) * (N * K))))
        2 ((s 2).drop 8)) 3 ((s 3).drop ((K + K) * (N * K)))) 4
          ((s 4).drop ((K + K) * (N * K))) := by
  have hu := length_rbitsW K (τOf s) (s 2) (s 5) 8
  rw [h5] at hu
  simp only [cbP, run_seq, run_copy, run_clear]
  rw [run_bitsP s hs 8 le_rfl, hK']
  rw [run_notP_map cNt_inj _ (fun i hi => by fin_cases i <;> simp [cNt, hs] at hi ⊢)]
  rw [run_mvP_map cMv_inj _ (by simp [cMv, cNt, hs]) (by simp [cMv, cNt, hs])]
  rw [run_notP_map cNa_inj _ (fun i hi => by fin_cases i <;> simp [cNa, cMv, cNt, hs] at hi ⊢)]
  rw [run_zrowP_map cZ_inj (K := K) (N := N) (L := K + K) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [cZ, cNa, cMv, cNt, hs] at hi ⊢
  · simp [cZ, cNa, cMv, cNt, hK']
  · simp [cZ, cNa, cMv, cNt, hN]
  · simp [cZ, cNa, cMv, cNt, hNK]
  · simp [cZ, cNa, cMv, cNt, hL]
  · simp [cZ, cNa, cMv, cNt, hK1]
  · simp [cZ, cNa, cMv, cNt, h19]
  · simp [cZ, cNa, cMv, cNt, h1]
  · simp [cZ, cNa, cMv, cNt, notW, hu]
  rw [run_dropP_map cD_inj _ (by simp [cD, cZ, cNa, cMv, cNt, hs])]
  funext t
  fin_cases t <;> simp [cD, cZ, cNa, cMv, cNt, hs, h19, cbRow, drop_append_of_length]

theorem noGrow_bitsP : ∀ j, (bitsP j).NoGrow
  | 0 => rfl
  | j + 1 => by
    show ((bitsP j).noGrowB && _) = true
    rw [noGrow_bitsP j]; rfl

/-! ### Certificate -/

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The inputs of `cbP` (variables `top, N, K`; the bit templates at most `2 N`). -/
def σCb' : Asg := [pTop, pNK, pTop, pTop, pTop, pNK] ++ List.replicate 8 (mo 2 [1]) ++
  [pK, pN, pNK, mo 2 [0, 1], pK, p2NKK]
def σCb : Asg := σCb' ++ List.replicate 4 pTop ++ [[]] ++ List.replicate 49 pTop

/-- A bound of the sweeps of `cbP`: a row of `2 K` entries. -/
def wCb : Poly := [([], 1500), ([0, 1], 1500), ([0, 0, 1], 3000), ([0, 1, 1], 4000), ([0, 2], 1000),
  ([0, 2, 1], 3000), ([0, 2, 2], 2100), ([0, 1, 2], 3500), ([0, 1, 3], 200), ([0, 0, 2], 2200),
  ([0, 2, 3], 60)]

set_option maxRecDepth 100000 in
/-- **The certificate of `cbP`.** -/
theorem check_cbP : check 8 cbP σCb σCb' wCb = true := by decide +kernel

/-- The sweeps of `cbP`. -/
def cbSweeps (N K : ℕ) : ℕ := 1500 + 1500 * N + 3000 * K + 4000 * (N * K) + 1000 * N ^ 2 +
  3000 * (N ^ 2 * K) + 2100 * (N ^ 2 * K ^ 2) + 3500 * (N * K ^ 2) + 200 * (N * K ^ 3) +
  2200 * K ^ 2 + 60 * (N ^ 2 * K ^ 3)

set_option maxHeartbeats 4000000 in
theorem time_cbP {M N K : ℕ} {ℓ : Fin 74 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K 0 0 0 0) σCb)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT cbP ℓ ≤ (2 * M + 3) * cbSweeps N K := by
  refine (bounds_of_check check_cbP (vars M N K 0 0 0 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wCb, pEval, mEval, vars, top, cbSweeps]
  ring

end Cert

end Prog

end SigabaNeo.Tape
