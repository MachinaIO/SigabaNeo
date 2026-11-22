import SigabaNeo.Lib.Lattices.ProgAlgo.Blocks
import SigabaNeo.Lib.Lattices.ProgAlgo.MulAlg

/-!
# Negacyclic multiplication of ring words as a tape program

* `repP : Prog 9` (`0` output, `1` a word `v`, `2` a word of length `N · K`, `3` `4` templates of
  lengths `K`, `N`; scratch `5 … 8`): `N` copies of the first `K` bits of `v` (`run_repP`).
* `rhoP : Prog 19` (`0` output, `1` a ring word `e`, `2` `3` templates of lengths `K`, `N`; scratch
  `4 … 18`): the word `rhoW N K e` of `X⁻¹ e`: the blocks shifted down by one, the first negated to
  the top (`run_rhoP`, `rhoW_enc`).
* `mulRWP : Prog 38` (`0` output, `1` `x`, `2` `y`, `3` `4` templates; scratch `5 … 37`):
  **`mulRW N K x y`** (`run_mulRWP`), by Horner's rule in `X⁻¹` (`SigabaNeo.Lattices.Algo.neg_rhoR_eR`):
  `e := 0; for j < N: e := ρ e + y_j · x`, then `-ρ e`, each step a block-wise program.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Encode

variable {k : ℕ}

theorem length_concatN_const (n : ℕ) (u : List Bool) :
    (concatN n (fun _ => u)).length = n * u.length := length_concatN fun _ _ => rfl

@[simp] theorem takeD_takeD (n : ℕ) (w : List Bool) : takeD n (takeD n w) = takeD n w :=
  takeD_of_length' (length_takeD n w)

/-- Shifting the same word `m` times into a register. -/
theorem pushConst_iter (u : List Bool) : ∀ (m : ℕ) (out : List Bool),
    (fun o => (o ++ u).drop u.length)^[m] out = (out ++ concatN m (fun _ => u)).drop (m * u.length)
  | 0, out => by simp [concatN]
  | m + 1, out => by
    rw [Function.iterate_succ_apply', pushConst_iter u m out]
    have := drop_append_drop out (concatN m (fun _ => u)) u
    rw [length_concatN_const] at this
    rw [this, concatN, Nat.succ_mul]

/-- The word of `X⁻¹ e`, as computed by `rhoP`. -/
def rhoW (N K : ℕ) (e : List Bool) : List Bool :=
  (e ++ (takeD ((N - 1) * K) (e.drop K) ++ subW (zeroW K) (takeD K e))).drop ((N - 1) * K + K)

theorem length_rhoW (N K : ℕ) (e : List Bool) : (rhoW N K e).length = e.length := by
  simp [rhoW]

namespace Prog

open scoped Prog

/-- A relabelled `bzip`. -/
theorem run_bzip_map {u : Fin 28 → Fin k} (hu : Function.Injective u) {K N : ℕ} {P : Prog 18}
    {f : List Bool → List Bool → List Bool} (hP : BlockSpec K P f)
    (hf : ∀ x y, x.length = K → y.length = K → (f x y).length = K) (s : Store k)
    (hs : ∀ i : Fin 28, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) (hy : (s (u 2)).length = N * K) :
    run (map u (bzip P)) s =
      Function.update s (u 0) (concatN N (fun i => f (block K i (s (u 1))) (block K i (s (u 2))))) :=
  run_map_eq_update hu _ s 0 _ (run_bzip hP hf (s ∘ u) hs hK hN hx hy)

/-! ### Copies of a block -/

def rv : Fin 5 → Fin 9 := ![5, 0, 6, 7, 3]
theorem rv_inj : Function.Injective rv := by decide

/-- `0 := N` copies of the first `K` bits of `s 1`. -/
def repP : Prog 9 := cp 0 2 ⨾ forN 8 4 (cp 5 1 ⨾ map rv mvP ⨾ clr 5)

theorem run_repP {K N : ℕ} (s : Store 9) (hs : ∀ i : Fin 9, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hw : (s 2).length = N * K) :
    run repP s = Function.update s 0 (concatN N (fun _ => takeD K (s 1))) := by
  have hc : ∀ i : Fin 9, 5 ≤ i.val → i ≠ 8 → s i = [] := fun i hi _ => hs i hi
  have hloop := run_forN 8 4 (cp 5 1 ⨾ map rv mvP ⨾ clr 5) (fun o => Function.update s 0 o)
    (fun o => (o ++ takeD K (s 1)).drop (takeD K (s 1)).length) (fun o w => by
      simp only [run_seq, run_copy, run_clear]
      rw [run_mvP_map rv_inj _ ?_ ?_]
      · funext t; fin_cases t <;> simp [rv, hK, hc]
      all_goals simp [rv, hc]) (s 2) (Function.update s 0 (s 2)) rfl
  simp only [repP, run_seq, run_copy]
  rw [hloop, pushConst_iter, length_takeD]
  have h4 : Function.update s 0 (s 2) 4 = s 4 := by simp
  rw [h4, hN, drop_append_of_length hw]
  funext t; fin_cases t <;> simp [hs 8 (by decide)]

theorem run_repP_map {u : Fin 9 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 9, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hw : (s (u 2)).length = N * K) :
    run (map u repP) s = Function.update s (u 0) (concatN N (fun _ => takeD K (s (u 1)))) :=
  run_map_eq_update hu _ s 0 _ (run_repP (s ∘ u) hs hK hN hw)

/-! ### Multiplication by `X⁻¹` -/

def rvA : Fin 5 → Fin 19 := ![4, 5, 6, 7, 2]
def rvB : Fin 5 → Fin 19 := ![4, 0, 6, 7, 2]
def rvC : Fin 5 → Fin 19 := ![9, 0, 6, 7, 2]
def rvS : Fin 11 → Fin 19 := ![9, 11, 10, 5, 12, 13, 14, 15, 16, 17, 18]
theorem rvA_inj : Function.Injective rvA := by decide
theorem rvB_inj : Function.Injective rvB := by decide
theorem rvC_inj : Function.Injective rvC := by decide
theorem rvS_inj : Function.Injective rvS := by decide

/-- Tapes `4` the stream of `e`, `5` its first block, `6` a bit, `7` `8` counters, `9` the negated
block, `10` zero, `11 … 18` the subtractor's scratch. -/
def rhoA : Prog 19 := cp 0 1 ⨾ cp 4 1 ⨾ cp 5 2 ⨾ map rvA mvP ⨾ cp 8 3 ⨾ tl 8
def rhoC : Prog 19 :=
  cp 10 2 ⨾ setZero 10 ⨾ map rvS subP ⨾ map rvC mvP ⨾ clr 4 ⨾ clr 5 ⨾ clr 9 ⨾ clr 10

/-- `0 := rhoW N K (s 1)`: move the first block aside, move the `N - 1` others to the output,
then the negated first block. -/
def rhoP : Prog 19 := rhoA ⨾ loop 8 (map rvB mvP) ⨾ rhoC

def mvK (K : ℕ) : List Bool × List Bool → List Bool × List Bool
  | (sv, ov) => (sv.drop K, (ov ++ takeD K sv).drop K)

theorem mvK_iter (K : ℕ) : ∀ (m : ℕ) (sv ov : List Bool),
    (mvK K)^[m] (sv, ov) = (sv.drop (m * K), (ov ++ takeD (m * K) sv).drop (m * K))
  | 0, sv, ov => by simp [takeD]
  | m + 1, sv, ov => by
    rw [Function.iterate_succ_apply', mvK_iter K m, mvK]
    have := drop_append_drop ov (takeD (m * K) sv) (takeD K (sv.drop (m * K)))
    simp only [length_takeD] at this
    rw [this, ← takeD_add, List.drop_drop, Nat.succ_mul]

set_option linter.unusedSimpArgs false in
theorem run_rhoP {K N : ℕ} (s : Store 19) (hs : ∀ i : Fin 19, 4 ≤ i.val → s i = [])
    (hK : (s 2).length = K) (hN : (s 3).length = N) :
    run rhoP s = Function.update s 0 (rhoW N K (s 1)) := by
  have hc : ∀ i : Fin 19, 4 ≤ i.val → s i = [] := hs
  set e := s 1
  let G : List Bool × List Bool → Store 19 := fun a =>
    Function.update (Function.update (Function.update s 4 a.1) 0 a.2) 5 (takeD K e)
  have hA : run rhoA s = Function.update (G (e.drop K, e)) 8 (s 3).tail := by
    simp only [rhoA, run_seq, run_copy, run_tail]
    rw [run_mvP_map rvA_inj _ ?_ ?_]
    · funext t; fin_cases t <;> simp [G, rvA, hK, hc, e]
    all_goals simp [rvA, hc]
  have hL := run_loop_iter 8 (map rvB mvP) G (mvK K) (fun _ => True) (fun a w _ => by
      rw [run_mvP_map rvB_inj _ ?_ ?_]
      · funext t; fin_cases t <;> simp [G, rvB, hK, hc, mvK]
      all_goals simp [G, rvB, hc]) (fun _ _ => trivial) (s 3).tail (e.drop K, e) trivial
  rw [rhoP, run_seq, run_seq, hA, hL, mvK_iter, List.length_tail, hN]
  have hneg : (subW (zeroW K) (takeD K e)).length = K := by simp [zeroW]
  simp only [rhoC, run_seq, run_copy, run_setZero, run_clear]
  rw [run_map_eq_update rvS_inj subP _ 0 _ (run_subP _ ?_ ?_), run_mvP_map rvC_inj _ ?_ ?_]
  · have hneg' : (subW (List.replicate K false) (takeD K e)).length = K := by simp
    have := drop_append_drop e (takeD ((N - 1) * K) (e.drop K))
      (subW (List.replicate K false) (takeD K e))
    simp only [length_takeD, hneg'] at this
    funext t
    fin_cases t <;> simp [G, rvS, rvC, hK, hc, rhoW, takeD_of_length' hneg', this, zeroW]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> [simp [G, rvS, hc]; (intro i hi; fin_cases i <;> simp [G, rvS, hc] at hi ⊢)])
    | simp [G, rvS, rvC, hc, hK, zeroW]

theorem run_rhoP_map {u : Fin 19 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 19, 4 ≤ i.val → s (u i) = []) (hK : (s (u 2)).length = K)
    (hN : (s (u 3)).length = N) :
    run (map u rhoP) s = Function.update s (u 0) (rhoW N K (s (u 1))) :=
  run_map_eq_update hu _ s 0 _ (run_rhoP (s ∘ u) hs hK hN)

end Prog

/-- **`rhoW` is the word of `X⁻¹ e`.** -/
theorem rhoW_enc {N K : ℕ} (hN : 0 < N) (a : Rq N K) :
    rhoW N K ((ringEnc N K).enc a) = (ringEnc N K).enc (rhoR a) := by
  set e := (ringEnc N K).enc a
  have he : e.length = N * K := length_ringEnc N K a
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hd : (e.drop K).length = M * K := by rw [List.length_drop, he]; ring_nf; omega
  have hsum : (M + 1 - 1) * K + K = (M + 1) * K := by simp; ring
  rw [rhoW, hsum, drop_append_of_length he, Nat.add_sub_cancel, takeD_of_length' hd]
  have hblk : concatN M (fun i => block K (i + 1) e) = e.drop K := by
    conv_rhs => rw [← concatN_block hd]
    apply concatN_congr
    intro i _
    simp only [block, List.drop_drop]
    congr 2; ring
  have hneg : (subW (zeroW K) (takeD K e)).length = K := by simp [zeroW]
  have hf : concatN (M + 1) (fun i => if i + 1 < M + 1 then block K (i + 1) e
      else subW (zeroW K) (takeD K e)) = e.drop K ++ subW (zeroW K) (takeD K e) := by
    rw [concatN, ← hblk]
    simp only [lt_self_iff_false, ↓reduceIte]
    congr 1
    apply concatN_congr
    intro i hi
    simp only [show i + 1 < M + 1 by omega, ↓reduceIte]
  rw [← hf]
  apply eq_ringEnc
  · intro i hi
    split_ifs with h
    · exact length_block he h
    · exact hneg
  · intro i hi
    simp only [rhoR, Cslib.Negacyclic.coeffs_ofCoeffs]
    split_ifs with h
    · exact dec_block_ringEnc a (i + 1)
    · rw [dec_subW K (by simp [zeroW]) (by simp), dec_zeroW,
        takeD_eq_take (by omega), show e.take K = block K 0 e by simp [block],
        dec_block_ringEnc, zero_sub]

end SigabaNeo.Tape
