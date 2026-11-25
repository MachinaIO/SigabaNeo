import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.GadRow
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.Bounds

/-!
# One encoding row modulo `2^K − 1`

An encoding of `Enc` (`c = s A⁽⁰⁾ + A⁽¹⁾ − z G + e`, entrywise) is a row of ring words
`canonW (s a₀ + a₁ − z + e)` over four streams of entries. `encRowP : Prog 56` writes
**`rowW N K L s A₀ A₁ Z E`** (`run_encRowP`), the concatenation over `c < L` of the canonical words
of `s · A₀_c + A₁_c − Z_c + E_c` (`rowE`, `decRM_rowE`):

* tapes: `0` the output register (any word of `L · N K` bits before), `1` `s`, `2` `A₀`, `3` `A₁`,
  `4` `Z`, `5` `E` (streams of `L` ring words), templates `6` (`K`), `7` (`N`), `8` (`N K`),
  `9` (`L`); scratch `10 … 55`, blank before and after;
* per entry: the four entries are moved into registers (`mvP`), then `mulRMP`, `addRMP`,
  `subRMP`, `addRMP`, `canonRP`, and the canonical word is shifted into the output (`mvP`).

**Cost** (`check_encRowP`, the abstract interpreter, variables `top, N, K, L`): from the inputs at
their lengths and every tape at most `M`, at most `(2 M + 3) · L · (200 + 400 N + 400 N K +
100 N² + 200 N² K + 30 N² K² + 50 K) + 200 (2 M + 3)` steps (`time_encRowP`), dominated by the
`L` ring products (`22 N² K²` sweeps each).
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

/-- The word of an entry: `s a₀ + a₁ − z + e`. -/
def rowE (N K : ℕ) (s a0 a1 z e : List Bool) : List Bool :=
  addRMW N K (subRMW N K (addRMW N K (mulRMW N K s a0) a1) z) e

theorem length_rowE (N K : ℕ) (s a0 a1 z e : List Bool) : (rowE N K s a0 a1 z e).length = N * K :=
  length_addRMW N K (length_subRMW N K (length_addRMW N K (length_mulRMW N K s a0) _) _) _

/-- Entry `c` of a stream of ring words. -/
def blk (NK c : ℕ) (x : List Bool) : List Bool := takeD NK (x.drop (c * NK))

/-- **The row**: the canonical words of `s A₀_c + A₁_c − Z_c + E_c`, `c < L`. -/
def rowW (N K L : ℕ) (s a0 a1 z e : List Bool) : List Bool :=
  concatN L fun c => canonW N K (rowE N K s (blk (N * K) c a0) (blk (N * K) c a1) (blk (N * K) c z)
    (blk (N * K) c e))

/-- The state of a round: the four streams, the four registers, the output. -/
abbrev RS := List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool ×
  List Bool × List Bool

/-- The abstract round. -/
def rstep (N K : ℕ) (s : List Bool) : RS → RS
  | (v0, v1, vz, ve, _, _, _, _, out) =>
    (v0.drop (N * K), v1.drop (N * K), vz.drop (N * K), ve.drop (N * K),
      takeD (N * K) v0, takeD (N * K) v1, takeD (N * K) vz, takeD (N * K) ve,
      (out ++ canonW N K (rowE N K s (takeD (N * K) v0) (takeD (N * K) v1) (takeD (N * K) vz)
        (takeD (N * K) ve))).drop (N * K))

/-- The entries of the first `c` rounds. -/
def rowC (N K : ℕ) (s v0 v1 vz ve : List Bool) (c : ℕ) : List Bool :=
  concatN c fun j => canonW N K (rowE N K s (blk (N * K) j v0) (blk (N * K) j v1) (blk (N * K) j vz)
    (blk (N * K) j ve))

theorem length_rowC (N K : ℕ) (s v0 v1 vz ve : List Bool) (c : ℕ) :
    (rowC N K s v0 v1 vz ve c).length = c * (N * K) :=
  length_concatN fun j _ => length_canonW N K (length_rowE N K _ _ _ _ _)

theorem rstep_iter (N K : ℕ) (s : List Bool) : ∀ (c : ℕ) (v0 v1 vz ve r0 r1 rz re out : List Bool),
    (rstep N K s)^[c] (v0, v1, vz, ve, r0, r1, rz, re, out) =
      (v0.drop (c * (N * K)), v1.drop (c * (N * K)), vz.drop (c * (N * K)), ve.drop (c * (N * K)),
        (if c = 0 then r0 else blk (N * K) (c - 1) v0), (if c = 0 then r1 else blk (N * K) (c - 1) v1),
        (if c = 0 then rz else blk (N * K) (c - 1) vz), (if c = 0 then re else blk (N * K) (c - 1) ve),
        (out ++ rowC N K s v0 v1 vz ve c).drop (c * (N * K)))
  | 0, v0, v1, vz, ve, r0, r1, rz, re, out => by simp [rowC, concatN]
  | c + 1, v0, v1, vz, ve, r0, r1, rz, re, out => by
    rw [Function.iterate_succ_apply', rstep_iter N K s c]
    have hl := length_rowC N K s v0 v1 vz ve c
    have hd := drop_append_drop out (rowC N K s v0 v1 vz ve c)
      (canonW N K (rowE N K s (blk (N * K) c v0) (blk (N * K) c v1) (blk (N * K) c vz)
        (blk (N * K) c ve)))
    rw [hl, length_canonW N K (length_rowE N K _ _ _ _ _)] at hd
    have e1 : ∀ v : List Bool, (v.drop (c * (N * K))).drop (N * K) = v.drop ((c + 1) * (N * K)) :=
      fun v => by rw [List.drop_drop]; congr 1; ring
    simp only [rstep, Prod.mk.injEq, e1, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
    refine ⟨trivial, trivial, trivial, trivial, rfl, rfl, rfl, rfl, ?_⟩
    have e2 : rowC N K s v0 v1 vz ve (c + 1) = rowC N K s v0 v1 vz ve c ++
        canonW N K (rowE N K s (blk (N * K) c v0) (blk (N * K) c v1) (blk (N * K) c vz)
          (blk (N * K) c ve)) := rfl
    rw [e2, show (c + 1) * (N * K) = c * (N * K) + N * K by ring, ← hd]
    rfl

namespace Prog

open scoped Prog

def eMv0 : Fin 5 → Fin 56 := ![10, 14, 24, 25, 8]
def eMv1 : Fin 5 → Fin 56 := ![11, 15, 24, 25, 8]
def eMvz : Fin 5 → Fin 56 := ![12, 16, 24, 25, 8]
def eMve : Fin 5 → Fin 56 := ![13, 17, 24, 25, 8]
/-- `mulRMP`: `18 := s · r₀`. -/
def eMul : Fin 37 → Fin 56 := ![18, 1, 14, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
/-- `addRMP`: `19 := 18 + r₁`. -/
def eAd1 : Fin 28 → Fin 56 := ![19, 18, 15, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
/-- `subRMP`: `20 := 19 − r_z`. -/
def eSub : Fin 28 → Fin 56 := ![20, 19, 16, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
/-- `addRMP`: `21 := 20 + r_e`. -/
def eAd2 : Fin 28 → Fin 56 := ![21, 20, 17, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
/-- `canonRP`: `22 := canonW 21` (dummy operand `8`). -/
def eCan : Fin 28 → Fin 56 := ![22, 21, 8, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
/-- `mvP` from `22` into the output `0`. -/
def eMvO : Fin 5 → Fin 56 := ![22, 0, 24, 25, 8]

set_option maxRecDepth 10000 in
theorem eMv0_inj : Function.Injective eMv0 := by decide
set_option maxRecDepth 10000 in
theorem eMv1_inj : Function.Injective eMv1 := by decide
set_option maxRecDepth 10000 in
theorem eMvz_inj : Function.Injective eMvz := by decide
set_option maxRecDepth 10000 in
theorem eMve_inj : Function.Injective eMve := by decide
set_option maxRecDepth 10000 in
theorem eMul_inj : Function.Injective eMul := by decide
set_option maxRecDepth 10000 in
theorem eAd1_inj : Function.Injective eAd1 := by decide
set_option maxRecDepth 10000 in
theorem eSub_inj : Function.Injective eSub := by decide
set_option maxRecDepth 10000 in
theorem eAd2_inj : Function.Injective eAd2 := by decide
set_option maxRecDepth 10000 in
theorem eCan_inj : Function.Injective eCan := by decide
set_option maxRecDepth 10000 in
theorem eMvO_inj : Function.Injective eMvO := by decide

/-- One entry. -/
def rowBody : Prog 56 :=
  map eMv0 mvP ⨾ map eMv1 mvP ⨾ map eMvz mvP ⨾ map eMve mvP ⨾ map eMul mulRMP ⨾ map eAd1 addRMP ⨾
    map eSub subRMP ⨾ map eAd2 addRMP ⨾ map eCan canonRP ⨾ map eMvO mvP ⨾ clr 18 ⨾ clr 19 ⨾
    clr 20 ⨾ clr 21

/-- **One encoding row.** -/
def encRowP : Prog 56 :=
  cp 10 2 ⨾ cp 11 3 ⨾ cp 12 4 ⨾ cp 13 5 ⨾ cp 14 8 ⨾ cp 15 8 ⨾ cp 16 8 ⨾ cp 17 8 ⨾
    forN 23 9 rowBody ⨾ clr 10 ⨾ clr 11 ⨾ clr 12 ⨾ clr 13 ⨾ clr 14 ⨾ clr 15 ⨾ clr 16 ⨾ clr 17

/-- The store of a round. -/
def rG (S : Store 56) : RS → Store 56
  | (v0, v1, vz, ve, r0, r1, rz, re, out) =>
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S 10 v0) 11 v1) 12 vz)
        13 ve) 14 r0) 15 r1) 16 rz) 17 re) 0 out

/-- The scratch of a round is blank (the counter `23` excepted). -/
def RClean (S : Store 56) : Prop := ∀ i : Fin 56, 18 ≤ i.val → i.val ≠ 23 → S i = []

set_option maxHeartbeats 16000000 in
theorem run_rowBody {K N : ℕ} (hK : 0 < K) (S : Store 56) (hS : RClean S) (hK' : (S 6).length = K)
    (hN : (S 7).length = N) (hNK : (S 8).length = N * K) (hs : (S 1).length = N * K) (a : RS)
    (h0 : a.2.2.2.2.1.length = N * K) (h1 : a.2.2.2.2.2.1.length = N * K)
    (hz : a.2.2.2.2.2.2.1.length = N * K) (he : a.2.2.2.2.2.2.2.1.length = N * K)
    (w : List Bool) :
    run rowBody (Function.update (rG S a) 23 w) = Function.update (rG S (rstep N K (S 1) a)) 23 w := by
  obtain ⟨v0, v1, vz, ve, r0, r1, rz, re, out⟩ := a
  simp only at h0 h1 hz he
  have hS : ∀ i : Fin 56, 18 ≤ i.val → i.val ≠ 23 → S i = [] := hS
  have t0 : (takeD (N * K) v0).length = N * K := length_takeD _ _
  have t1 : (takeD (N * K) v1).length = N * K := length_takeD _ _
  have tz : (takeD (N * K) vz).length = N * K := length_takeD _ _
  have te : (takeD (N * K) ve).length = N * K := length_takeD _ _
  have lm := length_mulRMW N K (S 1) (takeD (N * K) v0)
  have la := length_addRMW N K lm (takeD (N * K) v1)
  have ls := length_subRMW N K la (takeD (N * K) vz)
  have la2 := length_addRMW N K ls (takeD (N * K) ve)
  have lc := length_canonW N K la2
  simp only [rowBody, run_seq, run_clear]
  rw [run_mvP_map eMv0_inj _ (by simp [eMv0, rG, hS]) (by simp [eMv0, rG, hS])]
  rw [run_mvP_map eMv1_inj _ (by simp [eMv1, eMv0, rG, hS]) (by simp [eMv1, eMv0, rG, hS])]
  rw [run_mvP_map eMvz_inj _ (by simp [eMvz, eMv1, eMv0, rG, hS])
    (by simp [eMvz, eMv1, eMv0, rG, hS])]
  rw [run_mvP_map eMve_inj _ (by simp [eMve, eMvz, eMv1, eMv0, rG, hS])
    (by simp [eMve, eMvz, eMv1, eMv0, rG, hS])]
  rw [run_mulRMP_map eMul_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [eMul, eMve, eMvz, eMv1, eMv0, rG, hS] at hi ⊢
  · simp [eMul, eMve, eMvz, eMv1, eMv0, rG, hK']
  · simp [eMul, eMve, eMvz, eMv1, eMv0, rG, hN]
  · simp [eMul, eMve, eMvz, eMv1, eMv0, rG, hs]
  rw [run_addRMP_map eAd1_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hS] at hi ⊢
  · simp [eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hK']
  · simp [eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hN]
  · simp [eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, lm, hNK, h0, drop_append_of_length, t0]
  · simp [eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hNK, h1, drop_append_of_length, t1]
  rw [run_subRMP_map eSub_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hS] at hi ⊢
  · simp [eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hK']
  · simp [eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hN]
  · simp [eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, la, hNK, h0, h1, drop_append_of_length,
      t0, t1]
  · simp [eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hNK, hz, drop_append_of_length, tz]
  rw [run_addRMP_map eAd2_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hS] at hi ⊢
  · simp [eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hK']
  · simp [eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hN]
  · simp [eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, ls, hNK, h0, h1, hz,
      drop_append_of_length, t0, t1, tz]
  · simp [eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hNK, he, drop_append_of_length, te]
  rw [run_canonRP_map eCan_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;>
      simp [eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hS] at hi ⊢
  · simp [eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hK']
  · simp [eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hN]
  · simp [eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, la2, hNK, h0, h1, hz, he,
      drop_append_of_length, t0, t1, tz, te]
  · simp [eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hNK]
  rw [run_mvP_map eMvO_inj _ (by simp [eMvO, eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0,
      rG, hS]) (by simp [eMvO, eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, rG, hS])]
  funext t
  simp only [rG, rstep]
  fin_cases t <;> simp [eMvO, eCan, eAd2, eSub, eAd1, eMul, eMve, eMvz, eMv1, eMv0, hS, hNK, h0, h1,
    hz, he, t0, t1, tz, te, lc, drop_append_of_length, List.drop_of_length_le, takeD_of_length' lc,
    rowE]

/-- **One encoding row**: `0 := rowW N K L s A₀ A₁ Z E`. -/
theorem run_encRowP {K N L : ℕ} (hK : 0 < K) (s : Store 56)
    (hs : ∀ i : Fin 56, 10 ≤ i.val → s i = []) (hK' : (s 6).length = K) (hN : (s 7).length = N)
    (hNK : (s 8).length = N * K) (hL : (s 9).length = L) (h1 : (s 1).length = N * K)
    (hO : (s 0).length = L * (N * K)) :
    run encRowP s = Function.update s 0 (rowW N K L (s 1) (s 2) (s 3) (s 4) (s 5)) := by
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
  rw [show L * (N * K) = (s 0).length from hO.symm, drop_append_of_length rfl]
  funext t
  fin_cases t <;> simp [rG, s1, hs, rowW, rowC, blk, hO]

theorem noGrow_encRowP : encRowP.NoGrow := rfl
theorem wf_encRowP : encRowP.WF := wf_of_wfB (by decide)

section Cert

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- The streams of `L` ring words. -/
def pLNK : Poly := mo 1 [1, 1, 1]

/-- The inputs of `encRowP` (variables `top, N, K, L`); scratch below the top size. -/
def σRow' : Asg := [pTop, pNK, pLNK, pLNK, pLNK, pLNK, pK, pN, pNK, pm]
def σRow : Asg := σRow' ++ List.replicate 46 pTop

/-- A bound of the sweeps of `encRowP`. -/
def wRow : Poly := [([], 200), ([0, 0, 0, 1], 200), ([0, 1, 0, 1], 400), ([0, 1, 1, 1], 400),
  ([0, 2, 0, 1], 100), ([0, 2, 1, 1], 200), ([0, 2, 2, 1], 30), ([0, 0, 1, 1], 50)]

set_option maxRecDepth 100000 in
/-- **The certificate of `encRowP`.** -/
theorem check_encRowP : check 8 encRowP σRow σRow' wRow = true := by decide +kernel

/-- **The time of one encoding row** from the inputs at their lengths and tapes at most `M`. -/
theorem time_encRowP {M N K L : ℕ} {ℓ : Fin 56 → ℕ} (hℓ : ℓ ≤ bnd (vars M N K L 0 0 0) σRow)
    (hM : ∀ t, ℓ t ≤ M) :
    timeBoundT encRowP ℓ ≤ (2 * M + 3) * (200 + L * (200 + 400 * N + 400 * (N * K) +
      100 * N ^ 2 + 200 * (N ^ 2 * K) + 30 * (N ^ 2 * K ^ 2) + 50 * K)) := by
  refine (bounds_of_check check_encRowP (vars M N K L 0 0 0) hℓ hM).2.2.trans (le_of_eq ?_)
  simp [wRow, pEval, mEval, vars, top]
  ring

end Cert

end Prog

/-! ### The ring elements -/

theorem length_blk (NK c : ℕ) (x : List Bool) : (blk NK c x).length = NK := length_takeD _ _

/-- **An entry reads as `s a₀ + a₁ − z + e`.** -/
theorem decRM_rowE {N K : ℕ} {s a0 a1 z e : List Bool} (hs : s.length = N * K)
    (h0 : a0.length = N * K) (h1 : a1.length = N * K) (hz : z.length = N * K)
    (he : e.length = N * K) :
    decRM N K (rowE N K s a0 a1 z e) =
      decRM N K s * decRM N K a0 + decRM N K a1 - decRM N K z + decRM N K e := by
  have lm := length_mulRMW N K s a0
  have la := length_addRMW N K lm a1
  have ls := length_subRMW N K la z
  rw [rowE, decRM_addRMW ls he, decRM_subRMW la hz, decRM_addRMW lm h1, decRM_mulRMW hs h0]

/-- **The row, entry by entry**: the canonical words of `s A₀_c + A₁_c − Z_c + E_c`. -/
theorem rowW_eq {N K L : ℕ} (hK : 0 < K) {s : List Bool} (hs : s.length = N * K)
    (a0 a1 z e : List Bool) :
    rowW N K L s a0 a1 z e = concatN L fun c => encRM N K (decRM N K s *
      decRM N K (blk (N * K) c a0) + decRM N K (blk (N * K) c a1) -
        decRM N K (blk (N * K) c z) + decRM N K (blk (N * K) c e)) := by
  unfold rowW
  refine concatN_congr fun c _ => ?_
  rw [canonW_eq hK (length_rowE N K _ _ _ _ _), decRM_rowE hs (length_blk _ _ _)
    (length_blk _ _ _) (length_blk _ _ _) (length_blk _ _ _)]

end SigabaNeo.Tape
