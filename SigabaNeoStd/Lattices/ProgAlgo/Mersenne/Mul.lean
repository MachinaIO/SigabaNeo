import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Ring

/-!
# Negacyclic multiplication of ring words modulo `2^K − 1`

`mulRMP : Prog 37` (`0` output, `1` `x`, `2` `y`, `3` `4` templates of lengths `K`, `N`; scratch
`5 … 36`, blank before and after) writes **`mulRMW N K x y`** (`run_mulRMP`), whose ring element
is the product (`decRM_mulRMW`). Horner's rule in `X⁻¹` (`SigabaNeo.Lattices.Algo.NegaG.neg_rhoG_eG`):
`e := 0`; for each block `y_j` of `y`, `e := X⁻¹ e + y_j · x` (`rnbK`, `scRMP`, `addRMP`); finally
`−X⁻¹ e` (`rnbK`, `notP`).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The abstract round: (accumulator, stream of `y`). -/
def mstepRM (N K : ℕ) (x : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (ev, sb) => (addRMW N K (rhoMW K ev) (scRMW N K (takeD K sb) x), sb.drop K)

/-- **Negacyclic multiplication modulo `2^K − 1` on words** (Horner's rule in `X⁻¹`). -/
def mulRMW (N K : ℕ) (x y : List Bool) : List Bool :=
  notW (rhoMW K ((mstepRM N K x)^[N] (zeroW (N * K), y)).1)

theorem length_mulRMW (N K : ℕ) (x y : List Bool) : (mulRMW N K x y).length = N * K := by
  have : ∀ j, ((mstepRM N K x)^[j] (zeroW (N * K), y)).1.length = N * K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact length_addRMW N K (by rw [length_rhoMW]; exact ih) _
  simp [mulRMW, this]

theorem scG_eq_smul {R : Type} [CommRing R] {N : ℕ} (r : R) (a : Cslib.Negacyclic R N) :
    scG r a = r • a := by
  apply ext_coefG
  intro i hi
  rw [coefG_scG, coefG_of_lt _ hi, coefG_of_lt _ hi, Cslib.Negacyclic.coeffs_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm]

theorem mstepRM_iter {N K : ℕ} (hN : 0 < N) {x y : List Bool} (hx : x.length = N * K)
    (hy : y.length = N * K) : ∀ j, j ≤ N →
    ((mstepRM N K x)^[j] (zeroW (N * K), y)).1.length = N * K ∧
      ((mstepRM N K x)^[j] (zeroW (N * K), y)).2 = y.drop (j * K) ∧
      decRM N K ((mstepRM N K x)^[j] (zeroW (N * K), y)).1 = eG (decRM N K x) (decRM N K y) j
  | 0, _ => by
    refine ⟨by simp, by simp, ?_⟩
    apply ext_coefG
    intro i hi
    rw [coefG_decRM _ hi, eG, coefG_zero, Function.iterate_zero_apply]
    simp only [block, zeroW, decM, List.drop_replicate, List.take_replicate]
    rw [show List.replicate (min K (N * K - i * K)) false = zeroW _ from rfl, val_zeroW]; simp
  | j + 1, hj => by
    obtain ⟨h1, h2, h3⟩ := mstepRM_iter hN hx hy j (by omega)
    rw [Function.iterate_succ_apply']
    generalize (mstepRM N K x)^[j] (zeroW (N * K), y) = F at h1 h2 h3
    obtain ⟨ev, sb⟩ := F
    simp only at h1 h2 h3
    subst h2
    have hr : takeD K (y.drop (j * K)) = block K j y := takeD_drop_eq_block hy (by omega)
    refine ⟨length_addRMW N K (by rw [length_rhoMW]; exact h1) _, ?_, ?_⟩
    · simp only [mstepRM, List.drop_drop]; congr 1; ring
    · simp only [mstepRM]
      rw [decRM_addRMW (by rw [length_rhoMW]; exact h1) (length_scRMW N K _ hx),
        decRM_rhoMW hN h1, hr, decRM_scRMW (length_block hy (by omega)) hx, h3, eG, scG_eq_smul,
        coefG_decRM _ (by omega)]

/-- **The product**: `mulRMW` reads as `decRM x * decRM y`. -/
theorem decRM_mulRMW {N K : ℕ} {x y : List Bool} (hx : x.length = N * K)
    (hy : y.length = N * K) : decRM N K (mulRMW N K x y) = decRM N K x * decRM N K y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ext_coefG fun i hi => absurd hi (Nat.not_lt_zero _)
  obtain ⟨h1, -, h3⟩ := mstepRM_iter hN hx hy N le_rfl
  rw [mulRMW, decRM_notW (by rw [length_rhoMW]; exact h1), decRM_rhoMW hN h1, h3, neg_rhoG_eG]

namespace Prog

open scoped Prog

def vMv : Fin 5 → Fin 37 := ![6, 7, 10, 11, 3]
def vSc : Fin 29 → Fin 37 := ![8, 1, 7, 3, 4, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
def vRn : Fin 4 → Fin 37 := ![5, 3, 10, 11]
def vAd : Fin 28 → Fin 37 := ![12, 5, 8, 3, 4, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
def vNt : Fin 11 → Fin 37 := ![0, 5, 13, 14, 15, 16, 17, 18, 19, 20, 21]

theorem vMv_inj : Function.Injective vMv := by decide
theorem vSc_inj : Function.Injective vSc := by decide
theorem vRn_inj : Function.Injective vRn := by decide
theorem vAd_inj : Function.Injective vAd := by decide
theorem vNt_inj : Function.Injective vNt := by decide

/-- One round. Tapes: `5` the accumulator `e`, `6` the stream of `y`, `7` the block `y_j`, `8` the
products, `9` the counter, `10` `11` scratch of `mvP` and `rnbK`, `12` the sum; `13 … 36` the
scratch of the subprograms. -/
def mulBodyRM : Prog 37 :=
  cp 7 3 ⨾ map vMv mvP ⨾ map vSc scRMP ⨾ map vRn rnbK ⨾ map vAd addRMP ⨾ cp 5 12 ⨾ clr 7 ⨾
    clr 8 ⨾ clr 12

/-- **Negacyclic multiplication modulo `2^K − 1`.** -/
def mulRMP : Prog 37 :=
  cp 5 1 ⨾ setZero 5 ⨾ cp 6 2 ⨾ forN 9 4 mulBodyRM ⨾ map vRn rnbK ⨾ map vNt notP ⨾ clr 5 ⨾ clr 6

def mrmG (s : Store 37) : List Bool × List Bool → Store 37
  | (ev, sb) => Function.update (Function.update s 5 ev) 6 sb

set_option linter.unusedSimpArgs false in
theorem run_mulBodyRM {K N : ℕ} (s : Store 37) (hs : ∀ i : Fin 37, 5 ≤ i.val → i ≠ 9 → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) (a)
    (ha : a.1.length = N * K) (w : List Bool) :
    run mulBodyRM (Function.update (mrmG s a) 9 w) =
      Function.update (mrmG s (mstepRM N K (s 1) a)) 9 w := by
  obtain ⟨ev, sb⟩ := a
  simp only at ha
  simp only [mulBodyRM, run_seq, run_copy, run_clear]
  rw [run_mvP_map vMv_inj _ ?_ ?_, run_scRMP_map vSc_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_,
    run_rnbK_map vRn_inj _ ?_ ?_, run_addRMP_map vAd_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [mrmG, mstepRM]
    fin_cases t <;> simp [vMv, vSc, vRn, vAd, hK, hs, drop_append_of_length]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vMv, vSc, vRn, vAd, mrmG, hs] at hi ⊢)
    | simp [vMv, vSc, vRn, vAd, mrmG, hs, hK, hN, hx, ha, length_scRMW N K _ hx,
        drop_append_of_length]

set_option linter.unusedSimpArgs false in
theorem run_mulRMP {K N : ℕ} (s : Store 37) (hs : ∀ i : Fin 37, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) :
    run mulRMP s = Function.update s 0 (mulRMW N K (s 1) (s 2)) := by
  have hs' : ∀ i : Fin 37, 5 ≤ i.val → i ≠ 9 → s i = [] := fun i hi _ => hs i hi
  have hloop := run_loop_iter 9 mulBodyRM (mrmG s) (mstepRM N K (s 1)) (fun a => a.1.length = N * K)
    (fun a w ha => run_mulBodyRM s hs' hK hN hx a ha w)
    (fun a ha => by
      obtain ⟨ev, sb⟩ := a
      exact length_addRMW N K (by rw [length_rhoMW]; exact ha) _)
    (s 4) (zeroW (N * K), s 2) (by simp [zeroW])
  have e0 : run (cp 9 4) (run (cp 6 2) (run (setZero 5) (run (cp 5 1) s))) =
      Function.update (mrmG s (zeroW (N * K), s 2)) 9 (s 4) := by
    funext t; simp only [run_copy, run_setZero, mrmG]; fin_cases t <;> simp [hx, zeroW]
  simp only [mulRMP, forN, run_seq]
  rw [e0, hloop, hN]
  have hFl : ((mstepRM N K (s 1))^[N] (zeroW (N * K), s 2)).1.length = N * K := by
    have : ∀ j, ((mstepRM N K (s 1))^[j] (zeroW (N * K), s 2)).1.length = N * K := by
      intro j; induction j with
      | zero => simp [zeroW]
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact length_addRMW N K (by rw [length_rhoMW]; exact ih) _
    exact this N
  have hres : mulRMW N K (s 1) (s 2) =
      notW (rhoMW K ((mstepRM N K (s 1))^[N] (zeroW (N * K), s 2)).1) := rfl
  generalize (mstepRM N K (s 1))^[N] (zeroW (N * K), s 2) = F at hFl hres
  obtain ⟨ev, sb⟩ := F
  simp only at hFl hres
  simp only [run_clear]
  rw [run_rnbK_map vRn_inj _ ?_ ?_, run_notP_map vNt_inj _ ?_]
  · funext t
    simp only [mrmG]
    fin_cases t <;> simp [vRn, vNt, hs, hK, hres]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vRn, vNt, mrmG, hs] at hi ⊢)
    | simp [vRn, vNt, mrmG, hs]

theorem run_mulRMP_map {u : Fin 37 → Fin k} (hu : Function.Injective u) {K N : ℕ} (s : Store k)
    (hs : ∀ i : Fin 37, 5 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hx : (s (u 1)).length = N * K) :
    run (map u mulRMP) s = Function.update s (u 0) (mulRMW N K (s (u 1)) (s (u 2))) :=
  run_map_eq_update hu _ s 0 _ (run_mulRMP (s ∘ u) hs hK hN hx)

theorem noGrow_mulRMP : mulRMP.NoGrow := rfl
theorem wf_mulRMP : mulRMP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
