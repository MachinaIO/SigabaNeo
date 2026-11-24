import PE.Impl.ExpLUT.Prog.SetupP
import PE.Impl.DualUse.Prog.SetupEncDescA
import SigabaNeo.Lib.Machines.Prog.FrameSize
import SigabaNeo.Lib.Machines.Prog.VecBound

/-!
# The description length of `Setup`

The state count of `setupP X` is the sampler's plus a constant plus `195 m + 36` per counter
template (`natP`), for counts below `2^m` (`size_setupP_le`): every count is at most
`n · N K` for the numbers `n` of ring elements of the fields (`SetupCounts`). Hence
**`descLen_setupMP_le`**: `descLen ≤ 6 B 3^128 (516 + B)` with
`B = X.P.size + 34 (195 m + 36) + 2 · 10^6 + 4`.

The clock of the machine is `totalTimeT (setupP X) 126 124 nInS` (`time_setupMP`, the loader, the
per-tape bound `timeBoundT` of the program and the emitter); its closed form is not derived yet.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.DualUse.Prog

variable {D : Dims} {χT : PMF (Rg D)}

theorem size_ucTail : ucTail.size ≤ 100000 := by decide +kernel
theorem size_detCore : detCore.size ≤ 1000000 := by decide +kernel
theorem size_outP : (outP).size ≤ 100000 := by decide +kernel
theorem size_appUC : (appendTapeP (0 : Fin 40) 33 35 36).size ≤ 10000 := by decide +kernel
theorem size_forCoin : (forN (4 : Fin 7) 3 (coinAp 0 2)).size ≤ 1000 := by decide +kernel

/-- The counts of `Setup` are below `2^m`: every field's number of ring elements `n` has
`n · N K < 2^m`. -/
def SetupCounts (D : Dims) (m : ℕ) : Prop :=
  ∀ n ∈ [D.mb, nB2 D, nH D, nA D, nA0 D, nAin D, nAaut D, 2, D.K], n * (D.N * D.K) < 2 ^ m

theorem size_coinsF_le {n m : ℕ} (h : n < 2 ^ m) : (coinsF n).size ≤ 195 * m + 36 + 1036 := by
  have h1 := size_natP_le (3 : Fin 7) 4 n m h
  have h2 := size_forCoin
  simp only [coinsF, withCount, XProg.size_seq]
  have : (prog (.prim (.clear (3 : Fin 7)))).size = 36 := rfl
  omega

theorem size_unifCanonP_le {n m : ℕ} (hn : n * (D.N * D.K) < 2 ^ m)
    (hK : D.K * (D.N * D.K) < 2 ^ m) :
    (unifCanonP D.N D.K n).size ≤ 3 * (195 * m + 36) + 112036 := by
  have hNK : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
  have hK' : D.K < 2 ^ m := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hNK) hK
  have hnN : n * D.N < 2 ^ m :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ D.K_pos)) hn
  have h1 := size_coinsF_le hn
  have h2 := size_natP_le (7 : Fin 40) 34 D.K m hK'
  have h3 := size_natP_le (8 : Fin 40) 34 (n * D.N) m hnN
  have h4 := size_ucTail
  have h5 := size_appUC
  simp only [unifCanonP, XProg.size_seq, XProg.size_frame, XProg.size_prog]
  omega

theorem size_repF_le (P : XProg 7) {n m : ℕ} (h : n < 2 ^ m) :
    (repF n P).size ≤ P.size + 195 * m + 36 + 111 := by
  have h1 := size_natP_le (5 : Fin 7) 6 n m h
  simp only [repF, withCount, forN, XProg.size_seq, XProg.size_loop, XProg.size_prog]
  have e : ∀ p : Prim 7, (Prog.prim p).size = (3 + 2 * p.pad) * 12 := fun _ => rfl
  simp only [e, Prim.pad]
  omega

theorem size_tmplP_le {m : ℕ} (hK : D.K * (D.N * D.K) < 2 ^ m) (hmb : D.mb < 2 ^ m) :
    (tmplP D).size ≤ 9 * (195 * m + 36) + 60 := by
  have hNK : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
  have hNK' : D.N * D.K < 2 ^ m := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ D.K_pos) hK
  have hK' : D.K < 2 ^ m := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hNK) hK
  have hN : D.N < 2 ^ m := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ D.K_pos) hNK'
  have h1 : 1 < 2 ^ m := lt_of_le_of_lt hNK hNK'
  have := size_natP_le (40 : Fin 128) 125 D.K m hK'
  have := size_natP_le (41 : Fin 128) 125 D.N m hN
  have := size_natP_le (42 : Fin 128) 125 (D.N * D.K) m hNK'
  have := size_natP_le (43 : Fin 128) 125 1 m h1
  have := size_natP_le (45 : Fin 128) 125 D.K m hK'
  have := size_natP_le (46 : Fin 128) 125 (D.K * (D.N * D.K)) m hK
  have := size_natP_le (47 : Fin 128) 125 (D.K - 1) m (by omega)
  have := size_natP_le (48 : Fin 128) 125 (D.N * D.K - 1) m (by omega)
  have := size_natP_le (44 : Fin 128) 125 D.mb m hmb
  have e : (prog (.prim (.cons (48 : Fin 128) true))).size = 60 := rfl
  simp only [tmplP, XProg.size_seq] at *
  omega

theorem size_setupP_le (X : RingSampler D χT) {m : ℕ} (hm : SetupCounts D m) :
    (setupP X).size ≤ X.P.size + 34 * (195 * m + 36) + 2000000 := by
  have hNK : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
  have hK := hm D.K (by simp)
  have hmb := hm D.mb (by simp)
  have hmb' : D.mb < 2 ^ m := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hNK) hmb
  have hmbK : D.mb * D.K < 2 ^ m :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ D.N_pos)) hmb
  have := size_unifCanonP_le hmb hK
  have := size_unifCanonP_le (hm (nB2 D) (by simp)) hK
  have := size_unifCanonP_le (hm (nH D) (by simp)) hK
  have := size_unifCanonP_le (hm (nA D) (by simp)) hK
  have := size_unifCanonP_le (hm (nA0 D) (by simp)) hK
  have := size_unifCanonP_le (hm (nAin D) (by simp)) hK
  have := size_unifCanonP_le (hm (nAaut D) (by simp)) hK
  have := size_unifCanonP_le (hm 2 (by simp)) hK
  have := size_repF_le X.P hmbK
  have := size_tmplP_le hK hmb'
  have := size_detCore
  have := size_outP
  simp only [setupP, XProg.size_seq, XProg.size_frame, XProg.size_prog] at *
  omega

/-- **The clock of `Setup`**: loader, per-tape bound of the program, emitter. -/
theorem time_setupMP (X : RingSampler D χT) :
    (setupMP X).time = totalTimeT (setupP X) 126 124 nInS := rfl

/-- **The description length of `Setup`**. -/
theorem descLen_setupMP_le (X : RingSampler D χT) {m : ℕ} (hm : SetupCounts D m) :
    (setupMP X).descLen ≤ 6 * (X.P.size + 34 * (195 * m + 36) + 2000004) * 3 ^ 128 *
      (4 + 4 * 128 + (X.P.size + 34 * (195 * m + 36) + 2000004)) := by
  have h := size_setupP_le X hm
  have e : (setupMP X).descLen = 6 * ((setupP X).size + 4) * 3 ^ 128 * 3 ^ 0 *
      Machine.entryBits 128 ((setupP X).size + 4) 0 := by
    rw [Machine.descLen, setupMP, states_toMachineT, XProg.card_state]
    rfl
  rw [e]
  exact descLen_arithA (by omega)

end AdvancedEncryption.ExpLUT.Prog
