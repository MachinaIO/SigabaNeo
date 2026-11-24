import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.GadStream
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.Aut

/-!
# Encoding rows with a gadget term, on shift registers

The encodings of `Enc` (ePrint 2026/2539 §5.1) are rows `c = s' A⁽⁰⁾ + A⁽¹⁾ − (z G) + e` with
`z = (u y, u)` for ring elements `u`, `y` (`G = I₂ ⊗ (1, 2, …, 2^{K−1})`). Here:

* `run_encRowP_sh`: `encRowP` on an output register of any length is a **shift register**: it
  becomes `(out ++ rowW …).drop (L · N K)`, so successive rows accumulate the words of a ciphertext
  in one preallocated register;
* **`zrowP : Prog 61`** (`run_zrowP`): `0 := (0 ++ rowW N K L s' A₀ A₁ (gzW (u y) ++ gzW u) E).drop
  (L N K)`; tapes `0` the output register, `1` `s'`, `2` `y`, `3` `u`, `4` `A₀`, `5` `A₁`, `6` `E`,
  templates `7` (`K`), `8` (`N`), `9` (`N K`), `10` (`L`), `11` (`K − 1`), `12` (`2 K · N K`);
  scratch `13 … 60`, blank before and after;
* **`mrowP : Prog 66`** (`run_mrowP`): the row of a `2 × L` matrix stream `M` (row `0` then row `1`)
  and an error stream `E`, both **consumed** (`M := M.drop (2 L N K)`, `E := E.drop (L N K)`);
  tapes as `zrowP` with `4` `M`, `5` `E`, templates `6 … 11` (`K`, `N`, `N K`, `L`, `K − 1`,
  `2 K · N K`), `12` (`L · N K`), `13` (`2 L · N K`); scratch `14 … 65`;
* **`autItP : Prog 27`** (`run_autItP`): `0 := (σ_g)^{|2|}(0)` (`autMW` with the template `1` of
  length `g`), templates `3` (`K`), `4` (`N`); scratch `5 … 26`.

Each comes with a certificate of the abstract interpreter (`check_*`) and its clock (`time_*`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

namespace Prog

open scoped Prog

/-! ### The encoding row as a shift register -/

/-- **One encoding row on a shift register**: `0 := (0 ++ rowW N K L s A₀ A₁ Z E).drop (L N K)`. -/
theorem run_encRowP_sh {K N L : ℕ} (hK : 0 < K) (s : Store 56)
    (hs : ∀ i : Fin 56, 10 ≤ i.val → s i = []) (hK' : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hL : (s 9).length = L) (h1 : (s 1).length = N * K) :
    run encRowP s = Function.update s 0
      ((s 0 ++ rowW N K L (s 1) (s 2) (s 3) (s 4) (s 5)).drop (L * (N * K))) := by
  set s1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update s 10 (s 2)) 11 (s 3)) 12 (s 4)) 13 (s 5))
      14 (s 8)) 15 (s 8)) 16 (s 8)) 17 (s 8)
  have hloop := run_forN_inv 23 9 rowBody (rG s1) (rstep N K (s 1))
    (fun a => a.2.2.2.2.1.length = N * K ∧ a.2.2.2.2.2.1.length = N * K ∧
      a.2.2.2.2.2.2.1.length = N * K ∧ a.2.2.2.2.2.2.2.1.length = N * K)
    (fun a w ha => by
      have := run_rowBody hK s1 (fun i hi h23 => by
        fin_cases i <;> simp [s1, hs] at hi h23 ⊢) (by simp [s1, hK']) (by simp [s1, hN])
        (by simp [s1, hNK]) (by simp [s1, h1]) a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 w
      rwa [show s1 1 = s 1 by simp [s1]] at this)
    (fun a ha => by
      obtain ⟨v0, v1, vz, ve, r0, r1, rz, re, out⟩ := a
      exact ⟨length_takeD _ _, length_takeD _ _, length_takeD _ _, length_takeD _ _⟩)
    (s 2, s 3, s 4, s 5, s 8, s 8, s 8, s 8, s 0) ⟨hNK, hNK, hNK, hNK⟩ s1
    (by funext t; fin_cases t <;> simp [s1, rG, hs])
  have hsplit : run encRowP s = run (clr 10 ⨾ clr 11 ⨾ clr 12 ⨾ clr 13 ⨾ clr 14 ⨾ clr 15 ⨾ clr 16 ⨾
      clr 17) (run (forN 23 9 rowBody) s1) := by
    simp only [encRowP, run_seq, run_copy, s1]
    rfl
  rw [hsplit, hloop, rstep_iter, show s1 9 = s 9 by simp [s1], hL]
  simp only [run_seq, run_clear]
  funext t
  fin_cases t <;> simp [rG, s1, hs, rowW, rowC, blk]

theorem run_encRowP_sh_map {u : Fin 56 → Fin k} (hu : Function.Injective u) {K N L : ℕ}
    (hK : 0 < K) (s : Store k) (hs : ∀ i : Fin 56, 10 ≤ i.val → s (u i) = [])
    (hK' : (s (u 6)).length = K) (hN : (s (u 7)).length = N) (hNK : (s (u 8)).length = N * K)
    (hL : (s (u 9)).length = L) (h1 : (s (u 1)).length = N * K) :
    run (map u encRowP) s = Function.update s (u 0)
      ((s (u 0) ++ rowW N K L (s (u 1)) (s (u 2)) (s (u 3)) (s (u 4)) (s (u 5))).drop
        (L * (N * K))) :=
  run_map_eq_update hu _ s 0 _ (run_encRowP_sh hK (s ∘ u) hs hK' hN hNK hL h1)

theorem run_gzP_map {u : Fin 36 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 36, 7 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hNK : (s (u 5)).length = N * K) (hj : (s (u 6)).length = K - 1)
    (h1 : (s (u 1)).length = N * K) (h2 : (s (u 2)).length = N * K)
    (hO : (s (u 0)).length = (K + K) * (N * K)) :
    run (map u gzP) s = Function.update s (u 0) (gzW N K (s (u 1)) ++ gzW N K (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_gzP (s ∘ u) hs hK hN hNK hj h1 h2 hO)

/-! ### `zrowP`: a row with the gadget term of `z = (u y, u)` -/

/-- `mulRMP`: `13 := u · y`. -/
def zMul : Fin 37 → Fin 61 := ![13, 3, 2, 7, 8, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
  33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]
/-- `gzP`: `14 := gzW (u y) ++ gzW u`. -/
def zGz : Fin 36 → Fin 61 := ![14, 13, 3, 7, 8, 9, 11, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]
/-- `encRowP` on the output register `0`. -/
def zRow : Fin 56 → Fin 61 := ![0, 1, 4, 5, 14, 6, 7, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
  48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]

set_option maxRecDepth 10000 in
theorem zMul_inj : Function.Injective zMul := by decide
set_option maxRecDepth 10000 in
theorem zGz_inj : Function.Injective zGz := by decide
set_option maxRecDepth 10000 in
theorem zRow_inj : Function.Injective zRow := by decide

/-- **A row with a gadget term.** -/
def zrowP : Prog 61 :=
  map zMul mulRMP ⨾ cp 14 12 ⨾ map zGz gzP ⨾ map zRow encRowP ⨾ clr 13 ⨾ clr 14

/-- The gadget stream of `z = (u y, u)`. -/
def zStream (N K : ℕ) (u y : List Bool) : List Bool := gzW N K (mulRMW N K u y) ++ gzW N K u

set_option maxHeartbeats 4000000 in
/-- **The row**: `0 := (0 ++ rowW N K L s' A₀ A₁ (zStream u y) E).drop (L N K)`. -/
theorem run_zrowP {K N L : ℕ} (hK : 0 < K) (s : Store 61)
    (hs : ∀ i : Fin 61, 13 ≤ i.val → s i = []) (hK' : (s 7).length = K) (hN : (s 8).length = N)
    (hNK : (s 9).length = N * K) (hL : (s 10).length = L) (hK1 : (s 11).length = K - 1)
    (h12 : (s 12).length = (K + K) * (N * K)) (h1 : (s 1).length = N * K)
    (hu : (s 3).length = N * K) :
    run zrowP s = Function.update s 0
      ((s 0 ++ rowW N K L (s 1) (s 4) (s 5) (zStream N K (s 3) (s 2)) (s 6)).drop
        (L * (N * K))) := by
  have lm := length_mulRMW N K (s 3) (s 2)
  simp only [zrowP, run_seq, run_clear, run_copy]
  rw [run_mulRMP_map zMul_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [zMul, hs] at hi ⊢
  · simp [zMul, hK']
  · simp [zMul, hN]
  · simp [zMul, hu]
  rw [run_gzP_map zGz_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [zGz, zMul, hs] at hi ⊢
  · simp [zGz, zMul, hK']
  · simp [zGz, zMul, hN]
  · simp [zGz, zMul, hNK]
  · simp [zGz, zMul, hK1]
  · simp [zGz, zMul, lm]
  · simp [zGz, zMul, hu]
  · simp [zGz, zMul, h12]
  rw [run_encRowP_sh_map zRow_inj (K := K) (N := N) (L := L) hK _ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [zRow, zGz, zMul, hs] at hi ⊢
  · simp [zRow, zGz, zMul, hK']
  · simp [zRow, zGz, zMul, hN]
  · simp [zRow, zGz, zMul, hNK]
  · simp [zRow, zGz, zMul, hL]
  · simp [zRow, zGz, zMul, h1]
  funext t
  fin_cases t <;> simp [zRow, zGz, zMul, hs, zStream]

theorem run_zrowP_map {u : Fin 61 → Fin k} (hu : Function.Injective u) {K N L : ℕ} (hK : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 61, 13 ≤ i.val → s (u i) = [])
    (hK' : (s (u 7)).length = K) (hN : (s (u 8)).length = N)
    (hNK : (s (u 9)).length = N * K) (hL : (s (u 10)).length = L)
    (hK1 : (s (u 11)).length = K - 1) (h12 : (s (u 12)).length = (K + K) * (N * K))
    (h1 : (s (u 1)).length = N * K) (hu' : (s (u 3)).length = N * K) :
    run (map u zrowP) s = Function.update s (u 0)
      ((s (u 0) ++ rowW N K L (s (u 1)) (s (u 4)) (s (u 5)) (zStream N K (s (u 3)) (s (u 2)))
        (s (u 6))).drop (L * (N * K))) :=
  run_map_eq_update hu _ s 0 _ (run_zrowP hK (s ∘ u) hs hK' hN hNK hL hK1 h12 h1 hu')

theorem noGrow_zrowP : zrowP.NoGrow := rfl
theorem wf_zrowP : zrowP.WF := wf_of_wfB (by decide)

/-! ### `mrowP`: the row of a matrix stream, consuming its inputs -/

/-- `dropP` of the copy `14` of the matrix stream by `L N K` bits (counter `15`). -/
def mD1 : Fin 3 → Fin 66 := ![14, 15, 12]
/-- `zrowP` with `A₀ = M`, `A₁` the copy `14`. -/
def mZ : Fin 61 → Fin 66 := ![0, 1, 2, 3, 4, 14, 5, 6, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
  45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
/-- `dropP` of the matrix stream by `2 L N K` bits. -/
def mDM : Fin 3 → Fin 66 := ![4, 15, 13]
/-- `dropP` of the error stream by `L N K` bits. -/
def mDE : Fin 3 → Fin 66 := ![5, 15, 12]

set_option maxRecDepth 10000 in
theorem mD1_inj : Function.Injective mD1 := by decide
set_option maxRecDepth 10000 in
theorem mZ_inj : Function.Injective mZ := by decide
set_option maxRecDepth 10000 in
theorem mDM_inj : Function.Injective mDM := by decide
set_option maxRecDepth 10000 in
theorem mDE_inj : Function.Injective mDE := by decide

/-- **The row of a matrix stream.** -/
def mrowP : Prog 66 :=
  cp 14 4 ⨾ map mD1 dropP ⨾ map mZ zrowP ⨾ clr 14 ⨾ map mDM dropP ⨾ map mDE dropP

set_option maxHeartbeats 4000000 in
/-- **The row of a matrix stream**: the output register gets the row of `s' · M⁽⁰⁾ + M⁽¹⁾ −
zStream u y + E`, and both streams are consumed. -/
theorem run_mrowP {K N L : ℕ} (hK : 0 < K) (s : Store 66)
    (hs : ∀ i : Fin 66, 14 ≤ i.val → s i = []) (hK' : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hL : (s 9).length = L) (hK1 : (s 10).length = K - 1)
    (h11 : (s 11).length = (K + K) * (N * K)) (h12 : (s 12).length = L * (N * K))
    (h13 : (s 13).length = (L + L) * (N * K)) (h1 : (s 1).length = N * K)
    (hu : (s 3).length = N * K) :
    run mrowP s = Function.update (Function.update (Function.update s 0
      ((s 0 ++ rowW N K L (s 1) (s 4) ((s 4).drop (L * (N * K))) (zStream N K (s 3) (s 2))
        (s 5)).drop (L * (N * K)))) 4 ((s 4).drop ((L + L) * (N * K)))) 5
          ((s 5).drop (L * (N * K))) := by
  simp only [mrowP, run_seq, run_clear, run_copy]
  rw [run_dropP_map mD1_inj _ (by simp [mD1, hs])]
  rw [run_zrowP_map mZ_inj (K := K) (N := N) (L := L) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [mZ, mD1, hs] at hi ⊢
  · simp [mZ, mD1, hK']
  · simp [mZ, mD1, hN]
  · simp [mZ, mD1, hNK]
  · simp [mZ, mD1, hL]
  · simp [mZ, mD1, hK1]
  · simp [mZ, mD1, h11]
  · simp [mZ, mD1, h1]
  · simp [mZ, mD1, hu]
  rw [run_dropP_map mDM_inj _ (by simp [mDM, mZ, mD1, hs]),
    run_dropP_map mDE_inj _ (by simp [mDE, mDM, mZ, mD1, hs])]
  funext t
  fin_cases t <;> simp [mDE, mDM, mZ, mD1, hs, h12, h13]

theorem noGrow_mrowP : mrowP.NoGrow := rfl
theorem wf_mrowP : mrowP.WF := wf_of_wfB (by decide)

/-! ### `autItP`: iterated automorphisms -/

/-- `autMP`: `5 := σ_{|1|}(0)`. -/
def aA : Fin 25 → Fin 27 := ![5, 0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26]

set_option maxRecDepth 10000 in
theorem aA_inj : Function.Injective aA := by decide

/-- **Iterated automorphisms**: `|2|` rounds of `0 := σ_{|1|}(0)` (counter `6`). -/
def autItP : Prog 27 := forN 6 2 (map aA autMP ⨾ cp 0 5 ⨾ clr 5)

theorem run_autItP {K N : ℕ} (hN0 : 0 < N) (s : Store 27) (hs : ∀ i : Fin 27, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 0).length = N * K) :
    run autItP s = Function.update s 0 ((autMW N K (s 1).length)^[(s 2).length] (s 0)) := by
  have h := run_forN_inv 6 2 (map aA autMP ⨾ cp 0 5 ⨾ clr 5) (fun x => Function.update s 0 x)
    (autMW N K (s 1).length) (fun x => x.length = N * K)
    (fun x w hx' => by
      simp only [run_seq, run_copy, run_clear]
      rw [run_autMP_map aA_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ hN0]
      · funext t; fin_cases t <;> simp [aA, hs]
      · intro i hi; fin_cases i <;> simp [aA, hs] at hi ⊢
      · simp [aA, hK]
      · simp [aA, hN]
      · simp [aA, hx'])
    (fun x _ => length_autMW N K _ x hN0) (s 0) hx s (by funext t; fin_cases t <;> simp)
  rw [autItP, h]
  funext t; fin_cases t <;> simp [hs]

theorem noGrow_autItP : autItP.NoGrow := rfl
theorem wf_autItP : autItP.WF := wf_of_wfB (by decide)

/-! ### Certificates -/

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- `2 K · N K`. -/
def p2NKK : Poly := mo 2 [1, 2]

/-- The inputs of `zrowP` (variables `top, N, K, L`); streams and output below the top. -/
def σZ' : Asg := [pTop, pNK, pNK, pNK, pTop, pTop, pTop, pK, pN, pNK, pm, pK, p2NKK]
def σZ : Asg := σZ' ++ List.replicate 48 pTop

/-- A bound of the sweeps of `zrowP` (`L` rows of `22 N² K²`-sweep products dominate). -/
def wM : Poly := [([], 1100), ([0, 1], 1000), ([0, 0, 1], 1000), ([0, 1, 1], 1100), ([0, 2], 1000),
  ([0, 2, 1], 1000), ([0, 2, 2], 22), ([0, 1, 2], 1000), ([0, 1, 3], 200), ([0, 0, 2], 200),
  ([0, 0, 0, 1], 1000), ([0, 1, 0, 1], 1000), ([0, 1, 1, 1], 1100), ([0, 2, 0, 1], 1000),
  ([0, 2, 1, 1], 1000), ([0, 2, 2, 1], 30), ([0, 0, 1, 1], 1000)]

def wZ : Poly := wM

set_option maxRecDepth 100000 in
/-- **The certificate of `zrowP`.** -/
theorem check_zrowP : check 8 zrowP σZ σZ' wZ = true := by decide +kernel

/-- The inputs of `mrowP` (variables `top, N, K, L`). -/
def σM' : Asg := [pTop, pNK, pNK, pNK, pTop, pTop, pK, pN, pNK, pm, pK, p2NKK, mo 1 [1, 1, 1],
  mo 2 [1, 1, 1]]
def σM : Asg := σM' ++ List.replicate 52 pTop

set_option maxRecDepth 100000 in
/-- **The certificate of `mrowP`.** -/
theorem check_mrowP : check 8 mrowP σM σM' wM = true := by decide +kernel

/-- The inputs of `autItP` (variables `top, N, K, g, T`). -/
def σA' : Asg := [pNK, pm, pn, pK, pN]
def σA : Asg := σA' ++ List.replicate 22 pTop

/-- A bound of the sweeps of `autItP`: `T` automorphisms `σ_g` of `14 N K g` sweeps. -/
def wA : Poly := [([], 5), ([0, 0, 0, 0, 1], 20), ([0, 1, 0, 0, 1], 55), ([0, 1, 1, 0, 1], 40),
  ([0, 1, 0, 1, 1], 8), ([0, 1, 1, 1, 1], 14)]

set_option maxRecDepth 100000 in
/-- **The certificate of `autItP`.** -/
theorem check_autItP : check 8 autItP σA σA' wA = true := by decide +kernel

/-- The sweeps of a row of `L` entries, `zrowP` and `mrowP`. -/
def rowSweeps (N K L : ℕ) : ℕ :=
  1100 + 1000 * N + 1000 * K + 1100 * (N * K) + 1000 * N ^ 2 + 1000 * (N ^ 2 * K) +
    22 * (N ^ 2 * K ^ 2) + 1000 * (N * K ^ 2) + 200 * (N * K ^ 3) + 200 * K ^ 2 +
    L * (1000 + 1000 * N + 1100 * (N * K) + 1000 * N ^ 2 + 1000 * (N ^ 2 * K) +
      30 * (N ^ 2 * K ^ 2) + 1000 * K)

theorem time_zrowP {M N K L : ℕ} {ℓ : Fin 61 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K L 0 0 0) σZ)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT zrowP ℓ ≤ (2 * M + 3) * rowSweeps N K L := by
  refine (bounds_of_check check_zrowP (vars M N K L 0 0 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wZ, wM, pEval, mEval, vars, top, rowSweeps]
  ring

theorem time_mrowP {M N K L : ℕ} {ℓ : Fin 66 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K L 0 0 0) σM)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT mrowP ℓ ≤ (2 * M + 3) * rowSweeps N K L := by
  refine (bounds_of_check check_mrowP (vars M N K L 0 0 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wM, pEval, mEval, vars, top, rowSweeps]
  ring

theorem time_autItP {M N K g T : ℕ} {ℓ : Fin 27 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K g T 0 0) σA)
    (hM : ∀ t, ℓ t ≤ M) : timeBoundT autItP ℓ ≤
      (2 * M + 3) * (5 + T * (20 + 55 * N + 40 * (N * K) + 8 * (N * g) + 14 * (N * K * g))) := by
  refine (bounds_of_check check_autItP (vars M N K g T 0 0) hℓ hM).2.2.trans
    (Nat.mul_le_mul_left _ (le_of_eq ?_))
  simp [wA, pEval, mEval, vars, top]
  ring

end Cert

end Prog

end SigabaNeo.Tape
