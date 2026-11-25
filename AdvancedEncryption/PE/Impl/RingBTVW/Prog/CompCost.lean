import PE.Impl.RingBTVW.Prog.Comps
import PE.Impl.RingBTVW.Params.Conf
import PE.Impl.RingBTVW.Prog.CompLib
import PE.Impl.RingBTVW.Prog.SzWide

/-!
# The public-key, challenge and simulation-data components at `confA`

At `confP` (the sizes of `confA`: `N = 2^36`, `K = 2^27`, `k = K + 1`, `d = 2^65`, `nA = 128`):

* the public-key components `pub3L`, `pubIL`, `pub5L` on inputs of at most `2^195` bits (the
  setups' output bound, `len_setup3D_conf`) take at most `2^458` steps and leave at most `2^196`
  bits (`time_pub3L_conf`, `len_pub3L_conf`, …);
* the challenge components `chal3L`, `chal5L`, `chalIL2` on inputs of at most `2^193` bits (the
  packed secrets, `nS3_conf`, …) take at most `2^458` steps and leave at most `2^196` bits;
* the simulation-data programs `sd3P`, `sd5P` (inside the key component) on secrets of at most
  `2^193` bits take at most `2^520` steps and leave at most `2^259` bits (their
  templates reach `2^257`);
* their states: at most `2^24` (public keys), `2^25` (challenges, simulation data;
  `Prog/SzWide.lean` for templates beyond `2^240`).

The bounds are those of `PE.Impl.RingBTVW.Prog.Blocks` (`UBZ`), evaluated by `norm_num` after
`comp_unfold`.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

-- The time and size bounds of the components, unfolded into arithmetic on the parameters.
section Eval

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem sizepub3_conf : sizepub3 hkp confP ≤ 2 ^ 195 := by comp_unfold; norm_num

theorem sizepub5_conf : sizepub5 hkp confP ≤ 2 ^ 195 := by comp_unfold; norm_num

theorem sizeChal3_conf : sizeChal3 hkp confP ≤ 2 ^ 196 := by comp_unfold; norm_num

theorem sizeChal5_conf : sizeChal5 hkp confP ≤ 2 ^ 196 := by comp_unfold; norm_num

theorem sizeSd3_conf : sizeSd3 hkp confP ≤ 2 ^ 258 := by
  simp only [sizeSd3]; comp_unfold; norm_num

theorem sizeSd5_conf : sizeSd5 hkp confP ≤ 2 ^ 258 := by
  simp only [sizeSd5]; comp_unfold; norm_num

theorem timepub3_conf :
    timepub3 hkp confP (2 ^ 195 + sizepub3 hkp confP) + timeFin (2 ^ 195 + sizepub3 hkp confP) ≤
      2 ^ 458 := by
  comp_unfold; norm_num

theorem timepub5_conf :
    timepub5 hkp confP (2 ^ 195 + sizepub5 hkp confP) + timeFin (2 ^ 195 + sizepub5 hkp confP) ≤
      2 ^ 458 := by
  comp_unfold; norm_num

theorem timeChal3_conf :
    timeChal3 hkp confP (2 ^ 193 + sizeChal3 hkp confP) + timeFin (2 ^ 193 + sizeChal3 hkp confP) ≤
      2 ^ 458 := by
  comp_unfold; norm_num

theorem timeChal5_conf :
    timeChal5 hkp confP (2 ^ 193 + sizeChal5 hkp confP) + timeFin (2 ^ 193 + sizeChal5 hkp confP) ≤
      2 ^ 458 := by
  comp_unfold; norm_num

theorem timeChalI_conf : timeChalI hkp confP (2 ^ 193) (2 ^ 193) ≤ 2 ^ 400 := by
  simp only [timeChalI, tChal, tFlip, tFH, tMv, countT, tApp, tBit, sChalI, preI, coinsEnc,
    inst3Enc, eEnc]
  comp_unfold; norm_num

theorem lenChalI_conf : 2 * (sChalI hkp confP (2 ^ 193) (2 ^ 193) + (offK hkp confP + (Kp - 1)) + 1) ≤
    2 ^ 196 := by
  simp only [sChalI, preI, coinsEnc, inst3Enc, eEnc]
  comp_unfold; norm_num

theorem timeSd3_conf :
    timeSd3 hkp confP (2 ^ 193 + sizeSd3 hkp confP) + timeFin (2 ^ 193 + sizeSd3 hkp confP) ≤
      2 ^ 520 := by
  simp only [timeSd3, sizeSd3]; comp_unfold; norm_num

theorem timeSd5_conf :
    timeSd5 hkp confP (2 ^ 193 + sizeSd5 hkp confP) + timeFin (2 ^ 193 + sizeSd5 hkp confP) ≤
      2 ^ 520 := by
  simp only [timeSd5, sizeSd5]; comp_unfold; norm_num

end Eval

/-! ### The lifted components at `confP` -/

section Lifted

variable {a b : ℕ}

set_option exponentiation.threshold 1000

theorem pow195_add {s : ℕ} (h : s ≤ 2 ^ 195) : 2 ^ 195 + s ≤ 2 ^ 196 := by
  have : (2 : ℕ) ^ 196 = 2 ^ 195 + 2 ^ 195 := by norm_num
  omega

theorem pow193_add {s : ℕ} (h : s ≤ 2 ^ 196) : 2 ^ 193 + s ≤ 2 ^ 197 := by
  have : (2 : ℕ) ^ 197 = 2 ^ 196 + 2 ^ 196 := by norm_num
  have : (2 : ℕ) ^ 193 ≤ 2 ^ 196 := by norm_num
  omega

theorem pow258_add {s : ℕ} (h : s ≤ 2 ^ 258) : 2 ^ 193 + s ≤ 2 ^ 259 := by
  have : (2 : ℕ) ^ 259 = 2 ^ 258 + 2 ^ 258 := by norm_num
  have : (2 : ℕ) ^ 193 ≤ 2 ^ 258 := by norm_num
  omega

theorem time_pub3L_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    timeBoundT (pub3L hkp confP) (io2 a b 0) ≤ 2 ^ 458 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pub3L hkp confP _ _).trans (by rw [max_self]; exact timepub3_conf))

theorem len_pub3L_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    lenBoundT (pub3L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 196) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pub3L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow195_add sizepub3_conf)
      le_rfl))

theorem time_pubIL_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    timeBoundT (pubIL hkp confP) (io2 a b 0) ≤ 2 ^ 458 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pubIL hkp confP _ _).trans (by rw [max_self]; exact timepub3_conf))

theorem len_pubIL_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    lenBoundT (pubIL hkp confP) (io2 a b 0) ≤ io2 (2 ^ 196) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pubIL hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow195_add sizepub3_conf)
      le_rfl))

theorem time_pub5L_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    timeBoundT (pub5L hkp confP) (io2 a b 0) ≤ 2 ^ 458 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pub5L hkp confP _ _).trans (by rw [max_self]; exact timepub5_conf))

theorem len_pub5L_conf (ha : a ≤ 2 ^ 195) (hb : b ≤ 2 ^ 195) :
    lenBoundT (pub5L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 196) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pub5L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow195_add sizepub5_conf)
      le_rfl))

theorem time_chal3L_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    timeBoundT (chal3L hkp confP) (io2 a b 0) ≤ 2 ^ 458 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_chal3L hkp confP _ _).trans (by rw [max_self]; exact timeChal3_conf))

theorem len_chal3L_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    lenBoundT (chal3L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 197) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_chal3L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow193_add sizeChal3_conf)
      le_rfl))

theorem time_chal5L_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    timeBoundT (chal5L hkp confP) (io2 a b 0) ≤ 2 ^ 458 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_chal5L hkp confP _ _).trans (by rw [max_self]; exact timeChal5_conf))

theorem len_chal5L_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    lenBoundT (chal5L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 197) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_chal5L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow193_add sizeChal5_conf)
      le_rfl))

theorem time_chalIL2_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    timeBoundT (chalIL2 hkp confP) (io2 a b 0) ≤ 2 ^ 400 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans ((time_chalIL2 hkp confP _ _).trans timeChalI_conf)

theorem len_chalIL2_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    lenBoundT (chalIL2 hkp confP) (io2 a b 0) ≤ io2 (2 ^ 197) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans ((len_chalIL2 hkp confP _ _).trans
    (io2_mono (le_trans (by simpa only [kp] using lenChalI_conf) (by norm_num : (2 : ℕ) ^ 196 ≤ 2 ^ 197))
      le_rfl))

/-- **The simulation-data program of hybrid 3 and the ideal side** on secrets of at most `2^193`
bits. -/
theorem time_sd3P_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    timeBoundT (sd3P hkp confP) (io2 a b 0) ≤ 2 ^ 520 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_sd3P hkp confP _ _).trans (by rw [max_self]; exact timeSd3_conf))

theorem len_sd3P_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    lenBoundT (sd3P hkp confP) (io2 a b 0) ≤ io2 (2 ^ 259) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_sd3P hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow258_add sizeSd3_conf)
      le_rfl))

theorem time_sd5P_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    timeBoundT (sd5P hkp confP) (io2 a b 0) ≤ 2 ^ 520 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_sd5P hkp confP _ _).trans (by rw [max_self]; exact timeSd5_conf))

theorem len_sd5P_conf (ha : a ≤ 2 ^ 193) (hb : b ≤ 2 ^ 193) :
    lenBoundT (sd5P hkp confP) (io2 a b 0) ≤ io2 (2 ^ 259) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_sd5P hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow258_add sizeSd5_conf)
      le_rfl))

end Lifted

/-! ### State counts at `confP` -/

section States

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

theorem sz_finP (o : Fin 82) : SZ (finP o) (60 + 36 * 82) :=
  (sz_prim _).seq ((sz_clearL scrL).mono (by rw [scrL_length]))

theorem hB240 : (2 : ℕ) ^ 196 < 2 ^ 240 := by norm_num
theorem hB260 : (2 : ℕ) ^ 258 < 2 ^ 260 := by norm_num

theorem size_pub3P_conf : (pub3P hkp confP).size ≤ 2 ^ 24 := by
  unfold pub3P
  exact ((sz_pub3Body hkp confP (2 ^ 196) (sizepub3_conf.trans (by norm_num)) hB240).seq
    (sz_finP 15)).mono (by norm_num)

theorem size_pub3L_conf : (pub3L hkp confP).size ≤ 2 ^ 24 := by
  rw [pub3L, lift256, liftP, size_frame]; exact size_pub3P_conf

theorem size_pubIL_conf : (pubIL hkp confP).size ≤ 2 ^ 24 := by
  rw [pubIL, lift256, liftP, size_frame, pubIP]; exact size_pub3P_conf

theorem size_chal3L_conf : (chal3L hkp confP).size ≤ 2 ^ 25 := by
  rw [chal3L, lift256, liftP, size_frame, chal3P]
  exact ((sz_chal3Body hkp confP (2 ^ 196) sizeChal3_conf hB240).seq
    (sz_finP 10)).mono (by norm_num)

theorem size_pub5L_conf : (pub5L hkp confP).size ≤ 2 ^ 24 := by
  rw [pub5L, lift256, liftP, size_frame, pub5P]
  exact ((sz_pub5Body hkp confP (2 ^ 196) (sizepub5_conf.trans (by norm_num)) hB240).seq
    (sz_finP 15)).mono (by norm_num)

theorem size_chal5L_conf : (chal5L hkp confP).size ≤ 2 ^ 25 := by
  rw [chal5L, lift256, liftP, size_frame, chal5P]
  exact ((sz_chal5Body hkp confP (2 ^ 196) sizeChal5_conf hB240).seq
    (sz_finP 10)).mono (by norm_num)

/-- **The simulation-data programs** (inside the key component). -/
theorem size_sd3P_conf : (sd3P hkp confP).size ≤ 2 ^ 25 := by
  unfold sd3P
  exact ((sz_sd3BodyW hkp confP (2 ^ 258) sizeSd3_conf hB260).seq (sz_finP 13)).mono (by norm_num)

theorem size_sdIP_conf : (sdIP hkp confP).size ≤ 2 ^ 25 := by
  unfold sdIP; exact size_sd3P_conf

theorem size_sd5P_conf : (sd5P hkp confP).size ≤ 2 ^ 25 := by
  unfold sd5P
  exact ((sz_sd5BodyW hkp confP (2 ^ 258) sizeSd5_conf hB260).seq (sz_finP 13)).mono (by norm_num)

theorem size_chalBodyP (D P : ℕ) (hD : D < 2 ^ 240) (hP : P < 2 ^ 240) :
    (chalBodyP D P).size ≤ 2 * 46836 + 2000 := by
  have h1 := size_natP_le (k := 7) 3 4 D 240 hD
  have h2 := size_natP_le (k := 7) 3 4 P 240 hP
  simp only [chalBodyP, dropF, flipP, withCount, XProg.forN, flipHead, appendTapeP, clrS, nopX,
    size_seq, size_loop, size_ifBit, size_prog, Prog.size, Prim.pad]
  omega

theorem size_chalIL2_conf : (chalIL2 hkp confP).size ≤ 2 ^ 17 := by
  rw [chalIL2, lift256, liftP, size_frame, chalIL, lift82, liftP, size_frame, chalIP]
  have h := lenChalI_conf
  simp only [sChalI] at h
  exact (size_chalBodyP _ _ (by omega) (by omega)).trans (by norm_num)

end States

end AdvancedEncryption.RingBTVW.Prog
