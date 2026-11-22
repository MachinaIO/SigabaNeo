import SigabaNeo.Lib.Lattices.ProgAlgo.RingProgs

/-!
# `mulRW` as a tape program

`mulRWP : Prog 38` (tapes `0` output, `1` `x`, `2` `y`, `3` a word of length `K`, `4` a word of
length `N`; scratch `5 … 37`, blank before and after) writes `mulRW N K x y` on words of `N · K`
bits (`run_mulRWP`). By Horner's rule in `X⁻¹` (`neg_rhoR_eR`): `e := 0`; for each block `y_j` of
`y` (in order), `e := ρ e + (y_j, …, y_j) ⊙ x` (the copies by `repP`, the block-wise products by
`bzip mulP`, `ρ` by `rhoP`, the sum by `bzip` of the adder); finally `0 - ρ e`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Encode

variable {k : ℕ}

theorem length_concatN_mulW {N K : ℕ} {x : List Bool} (hx : x.length = N * K) (g : ℕ → List Bool) :
    (concatN N (fun i => mulW (block K i x) (g i))).length = N * K :=
  length_concatN fun i hi => by rw [length_mulW, length_block hx hi]

namespace Prog

open scoped Prog

def mB : Fin 5 → Fin 38 := ![6, 7, 11, 12, 3]
def vRep : Fin 9 → Fin 38 := ![8, 7, 1, 3, 4, 15, 16, 17, 18]
def vMul : Fin 28 → Fin 38 := ![9, 1, 8, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
  28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
def vRho : Fin 19 → Fin 38 := ![13, 5, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
  28, 29]
def vAddR : Fin 28 → Fin 38 := ![5, 13, 9, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
def vSubR : Fin 28 → Fin 38 := ![0, 14, 13, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

theorem mB_inj : Function.Injective mB := by decide
theorem vRep_inj : Function.Injective vRep := by decide
theorem vMul_inj : Function.Injective vMul := by decide
theorem vRho_inj : Function.Injective vRho := by decide
theorem vAddR_inj : Function.Injective vAddR := by decide
theorem vSubR_inj : Function.Injective vSubR := by decide

/-- One round. Tapes: `5` the accumulator `e`, `6` the stream of `y`, `7` the block `y_j`, `8` its
copies, `9` the products, `10` the counter, `11` a bit, `12` a counter, `13` `ρ e`, `14` zero;
`15 … 37` the scratch of the subprograms. -/
def mulBodyR : Prog 38 :=
  cp 7 3 ⨾ map mB mvP ⨾ map vRep repP ⨾ map vMul (bzip mulP) ⨾ map vRho rhoP ⨾
    map vAddR (bzip (zipB faOp false)) ⨾ clr 7 ⨾ clr 8 ⨾ clr 9 ⨾ clr 13

def mulFinR : Prog 38 :=
  map vRho rhoP ⨾ cp 14 1 ⨾ setZero 14 ⨾ map vSubR (bzip (zipB fsOp false)) ⨾ clr 5 ⨾ clr 6 ⨾
    clr 13 ⨾ clr 14

/-- **Negacyclic multiplication of ring words.** -/
def mulRWP : Prog 38 := cp 5 1 ⨾ setZero 5 ⨾ cp 6 2 ⨾ forN 10 4 mulBodyR ⨾ mulFinR

/-- The abstract round: (accumulator, stream of `y`). -/
def mstepR (N K : ℕ) (x : List Bool) : List Bool × List Bool → List Bool × List Bool
  | (ev, sb) =>
    (addRW N K (rhoW N K ev) (concatN N (fun i => mulW (block K i x)
      (block K i (concatN N (fun _ => takeD K sb))))), sb.drop K)

def mrG (s : Store 38) : List Bool × List Bool → Store 38
  | (ev, sb) => Function.update (Function.update s 5 ev) 6 sb

set_option linter.unusedSimpArgs false in
theorem run_mulBodyR {K N : ℕ} (s : Store 38) (hs : ∀ i : Fin 38, 5 ≤ i.val → i ≠ 10 → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K) (a)
    (ha : a.1.length = N * K) (w : List Bool) :
    run mulBodyR (Function.update (mrG s a) 10 w) =
      Function.update (mrG s (mstepR N K (s 1) a)) 10 w := by
  obtain ⟨ev, sb⟩ := a
  simp only at ha
  have hfm : ∀ x y : List Bool, x.length = K → y.length = K → (mulW x y).length = K :=
    fun x y hx _ => by simp [hx]
  have hfa : ∀ x y : List Bool, x.length = K → y.length = K → (addW x y).length = K :=
    fun x y hx _ => by simp [hx]
  simp only [mulBodyR, run_seq, run_copy, run_clear]
  rw [run_mvP_map mB_inj _ ?_ ?_, run_repP_map vRep_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_,
    run_bzip_map vMul_inj (N := N) (blockSpec_mul K) hfm _ ?_ ?_ ?_ ?_ ?_,
    run_rhoP_map vRho_inj (K := K) (N := N) _ ?_ ?_ ?_,
    run_bzip_map vAddR_inj (N := N) (blockSpec_add K) hfa _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [mrG, mstepR, addRW]
    fin_cases t <;> simp [mB, vRep, vMul, vRho, vAddR, hK, hs, drop_append_of_length]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [mB, vRep, vMul, vRho, vAddR, mrG, hs] at hi ⊢)
    | simp [mB, vRep, vMul, vRho, vAddR, mrG, hs, hK, hN, hx, ha, length_concatN_const,
        length_rhoW, length_concatN_mulW hx, drop_append_of_length]

/-- The accumulator after `j` rounds is the word of `eR a b j`. -/
theorem mstepR_iter {N K : ℕ} (hN : 0 < N) (a b : Rq N K) :
    ∀ j, j ≤ N → (mstepR N K ((ringEnc N K).enc a))^[j] (zeroW (N * K), (ringEnc N K).enc b) =
      ((ringEnc N K).enc (eR a b j), ((ringEnc N K).enc b).drop (j * K))
  | 0, _ => by simp [eR, enc_zeroR]
  | j + 1, hj => by
    rw [Function.iterate_succ_apply', mstepR_iter hN a b j (by omega), mstepR]
    have hy := length_ringEnc N K b
    have hx := length_ringEnc N K a
    have hu : (takeD K (((ringEnc N K).enc b).drop (j * K))).length = K := length_takeD _ _
    have hT : concatN N (fun i => mulW (block K i ((ringEnc N K).enc a))
        (block K i (concatN N (fun _ => takeD K (((ringEnc N K).enc b).drop (j * K)))))) =
        (ringEnc N K).enc (scR (coefOf b j) a) := by
      apply eq_ringEnc
      · intro i hi; rw [length_mulW, length_block hx hi]
      · intro i hi
        rw [block_concatN (fun _ _ => hu)]
        simp only [hi, ↓reduceIte]
        rw [takeD_drop_eq_block hy (by omega),
          dec_mulW K (length_block hx hi), dec_block_ringEnc, dec_block_ringEnc]
        simp [scR, coefOf, hi]
    rw [hT, rhoW_enc hN, addRW_enc, List.drop_drop]
    refine Prod.ext rfl ?_
    simp only
    congr 1; ring

theorem mulRW_eq_fin {N K : ℕ} {x y : List Bool} (hx : x.length = N * K) (hy : y.length = N * K) :
    subRW N K (List.replicate (N * K) false) (rhoW N K ((mstepR N K x)^[N] (zeroW (N * K), y)).1) =
      mulRW N K x y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rfl
  rw [← enc_decR hx, ← enc_decR hy, mstepR_iter hN _ _ N le_rfl, rhoW_enc hN,
    show List.replicate (N * K) false = zeroW (N * K) from rfl, ← enc_zeroR, subRW_enc, mulRW_enc,
    zero_sub, neg_rhoR_eR]

set_option linter.unusedSimpArgs false in
theorem run_mulRWP {K N : ℕ} (s : Store 38) (hs : ∀ i : Fin 38, 5 ≤ i.val → s i = [])
    (hK : (s 3).length = K) (hN : (s 4).length = N) (hx : (s 1).length = N * K)
    (hy : (s 2).length = N * K) :
    run mulRWP s = Function.update s 0 (mulRW N K (s 1) (s 2)) := by
  have hs' : ∀ i : Fin 38, 5 ≤ i.val → i ≠ 10 → s i = [] := fun i hi _ => hs i hi
  have hloop := run_loop_iter 10 mulBodyR (mrG s) (mstepR N K (s 1)) (fun a => a.1.length = N * K)
    (fun a w ha => run_mulBodyR s hs' hK hN hx a ha w)
    (fun a ha => by
      obtain ⟨ev, sb⟩ := a
      exact length_addRW N K (by rw [length_rhoW]; exact ha) _)
    (s 4) (zeroW (N * K), s 2) (by simp [zeroW])
  have e0 : run (cp 10 4) (run (cp 6 2) (run (setZero 5) (run (cp 5 1) s))) =
      Function.update (mrG s (zeroW (N * K), s 2)) 10 (s 4) := by
    funext t; simp only [run_copy, run_setZero, mrG]; fin_cases t <;> simp [hx, zeroW]
  have hfs : ∀ x y : List Bool, x.length = K → y.length = K → (subW x y).length = K :=
    fun x y hx _ => by simp [hx]
  simp only [mulRWP, forN, run_seq]
  rw [e0, hloop, hN]
  generalize hF : (mstepR N K (s 1))^[N] (zeroW (N * K), s 2) = F
  have hFl : F.1.length = N * K := by
    rw [← hF]
    have : ∀ j, ((mstepR N K (s 1))^[j] (zeroW (N * K), s 2)).1.length = N * K := by
      intro j; induction j with
      | zero => simp [zeroW]
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact length_addRW N K (by rw [length_rhoW]; exact ih) _
    exact this N
  have hres := mulRW_eq_fin hx hy
  rw [hF] at hres
  obtain ⟨ev, sb⟩ := F
  simp only at hFl hres
  simp only [mulFinR, run_seq, run_copy, run_setZero, run_clear]
  rw [run_rhoP_map vRho_inj (K := K) (N := N) _ ?_ ?_ ?_,
    run_bzip_map vSubR_inj (N := N) (blockSpec_sub K) hfs _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    simp only [mrG]
    fin_cases t <;> simp [vRho, vSubR, hs, hx, ← hres, subRW]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [vRho, vSubR, mrG, hs] at hi ⊢)
    | simp [vRho, vSubR, mrG, hs, hK, hN, hx, hFl, length_rhoW]

theorem noGrow_mulRWP : mulRWP.NoGrow := rfl
theorem wf_mulRWP : mulRWP.WF := wf_of_wfB (by decide)

end Prog

end SigabaNeo.Tape
