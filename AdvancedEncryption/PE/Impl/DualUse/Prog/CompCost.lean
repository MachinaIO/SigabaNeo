import PE.Impl.DualUse.Prog.Comps
import PE.Impl.DualUse.Params.Conf

/-!
# The public-key, challenge and simulation-data components at the concrete parameters

At `confP` (`N = 2^33`, `K = 2^25`, `k = K + 1`, `d = 2^60`), on inputs of at most `2^180` bits
(every secret word of the three reductions is shorter, `PE.Impl.DualUse.Prog.CompBounds`), the
lifted components `pub3L`, `pubIL`, `pub5L`, `chal3L`, `chal5L` cost at most `2^419`
(public keys), `2^430` (`chal3L`) and `2^440` (`chal5L`) steps, and their outputs have at most
`2^181` bits. The bounds are those of `PE.Impl.DualUse.Prog.Blocks` (`UBZ`: every
loop is charged the length of its own counter), evaluated by `norm_num`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

theorem len_Attr {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).Attr)).length = 10 := len_fin 10

theorem len_Index {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).ctBits.Index)).length = 2 * (2 * k * (k * N)) := by
  show (Enum.list (α := Fin 2 × (RingBTVW.Col k × (Fin k × Fin N)))).length = _
  simp only [Enum.length_prod, len_fin, len_col]

theorem confP_d : confP.d = 2 ^ 60 := dp_def

theorem scrL_length : scrL.length = 81 := rfl

theorem io2_mono {R : ℕ} {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    io2 (R := R) a b 0 ≤ io2 A B 0 := fun i => by
  simp only [io2]; split_ifs <;> omega

/-- Unfold the time and size bounds of the components into arithmetic on the parameters. -/
macro "comp_unfold" : tactic => `(tactic| (
  simp only [timepub3, sizepub3, timepub5, sizepub5, timeChal3, sizeChal3, timechal3Tail,
    sizechal3Tail, timeChal5, sizeChal5, timechal5Tail, sizechal5Tail, timeSd3, sizeSd3, timeSd5,
    sizeSd5, timesdTail, sizesdTail, timeGetB, timeMmB, timeAddB, timeSubB, timeJoinB, timeGadB,
    timeOneB, timePsiCore, timeBjCore, timeTrB, timeSelB, timeHashB, timeFlipB, timeFin, sizeMmB,
    sizeAddB, sizePsiCore, sizeBjCore, sizeTrB, sizeSelB, sizeHashB, sizeGadB, o3B, o3s, o3e0, o3R,
    o3x, o3w, o3p, o3e1, o3e, o3e', o5a, o5z, o5p, o5v, o5va, o5vz, o5vp, o5x, o5u, o5w, o5R, o5e,
    offK, P1, fPsi, fWm, fencLen, wEnc, rmTEnc, rmEnc, matTEnc, eEnc, pkEnc, ctEnc, rowL, fJ, fT, fC,
    fD, fR, Enum.length_prod, len_fin, len_col, len_trap, len_Attr, len_Index,
    len_JC, len_AI, scrL_length, max_self]
  simp only [confP_d, kp, Kp_def, Np_def]))

section Eval

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

theorem timepub3_conf :
    timepub3 hkp confP (2 ^ 180 + sizepub3 hkp confP) + timeFin (2 ^ 180 + sizepub3 hkp confP) ≤
      2 ^ 419 := by
  comp_unfold; norm_num

theorem sizepub3_conf : sizepub3 hkp confP ≤ 2 ^ 180 := by comp_unfold; norm_num

theorem timeChal3_conf :
    timeChal3 hkp confP (2 ^ 180 + sizeChal3 hkp confP) + timeFin (2 ^ 180 + sizeChal3 hkp confP) ≤
      2 ^ 430 := by
  comp_unfold; norm_num

theorem sizeChal3_conf : sizeChal3 hkp confP ≤ 2 ^ 178 := by comp_unfold; norm_num

theorem timepub5_conf :
    timepub5 hkp confP (2 ^ 180 + sizepub5 hkp confP) + timeFin (2 ^ 180 + sizepub5 hkp confP) ≤
      2 ^ 419 := by
  comp_unfold; norm_num

theorem sizepub5_conf : sizepub5 hkp confP ≤ 2 ^ 180 := by comp_unfold; norm_num

theorem timeChal5_conf :
    timeChal5 hkp confP (2 ^ 180 + sizeChal5 hkp confP) + timeFin (2 ^ 180 + sizeChal5 hkp confP) ≤
      2 ^ 440 := by
  comp_unfold; norm_num

theorem sizeChal5_conf : sizeChal5 hkp confP ≤ 2 ^ 178 := by comp_unfold; norm_num

theorem timeChalI_conf : timeChalI hkp confP (2 ^ 180) (2 ^ 180) ≤ 2 ^ 380 := by
  simp only [timeChalI, tChal, tFlip, tFH, tMv, countT, tApp, tBit, sChalI, preI, coinsEnc,
    inst3Enc, restEnc, eEnc]
  comp_unfold; norm_num

theorem lenChalI_conf : 2 * (sChalI hkp confP (2 ^ 180) (2 ^ 180) + (offK hkp confP + (Kp - 1)) + 1) ≤
    2 ^ 182 := by
  simp only [sChalI, preI, coinsEnc, inst3Enc, restEnc, eEnc]
  comp_unfold; norm_num

theorem sizeSd3_conf : sizeSd3 hkp confP ≤ 2 ^ 239 := by
  simp only [sizeSd3]; comp_unfold; norm_num

theorem sizeSd5_conf : sizeSd5 hkp confP ≤ 2 ^ 239 := by
  simp only [sizeSd5]; comp_unfold; norm_num

end Eval

/-! ### The lifted components at `confP` -/

section Lifted

variable {a b : ℕ}

theorem pow180_add {s : ℕ} (h : s ≤ 2 ^ 180) : 2 ^ 180 + s ≤ 2 ^ 181 := by
  have : (2 : ℕ) ^ 181 = 2 ^ 180 + 2 ^ 180 := by norm_num
  omega

theorem pow178_add {s : ℕ} (h : s ≤ 2 ^ 178) : 2 ^ 180 + s ≤ 2 ^ 181 := by
  have : (2 : ℕ) ^ 181 = 2 ^ 180 + 2 ^ 180 := by norm_num
  have : (2 : ℕ) ^ 178 ≤ 2 ^ 180 := by norm_num
  omega

theorem time_pub3L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (pub3L hkp confP) (io2 a b 0) ≤ 2 ^ 419 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pub3L hkp confP _ _).trans (by rw [max_self]; exact timepub3_conf))

theorem len_pub3L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (pub3L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 181) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pub3L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow180_add sizepub3_conf)
      le_rfl))

theorem time_pubIL_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (pubIL hkp confP) (io2 a b 0) ≤ 2 ^ 419 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pubIL hkp confP _ _).trans (by rw [max_self]; exact timepub3_conf))

theorem len_pubIL_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (pubIL hkp confP) (io2 a b 0) ≤ io2 (2 ^ 181) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pubIL hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow180_add sizepub3_conf)
      le_rfl))

theorem time_pub5L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (pub5L hkp confP) (io2 a b 0) ≤ 2 ^ 419 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_pub5L hkp confP _ _).trans (by rw [max_self]; exact timepub5_conf))

theorem len_pub5L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (pub5L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 181) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_pub5L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow180_add sizepub5_conf)
      le_rfl))

theorem time_chal3L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (chal3L hkp confP) (io2 a b 0) ≤ 2 ^ 430 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_chal3L hkp confP _ _).trans (by rw [max_self]; exact timeChal3_conf))

theorem len_chal3L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (chal3L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 181) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_chal3L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow178_add sizeChal3_conf)
      le_rfl))

theorem time_chal5L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (chal5L hkp confP) (io2 a b 0) ≤ 2 ^ 440 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans
    ((time_chal5L hkp confP _ _).trans (by rw [max_self]; exact timeChal5_conf))

theorem len_chal5L_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (chal5L hkp confP) (io2 a b 0) ≤ io2 (2 ^ 181) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans
    ((len_chal5L hkp confP _ _).trans (io2_mono (by rw [max_self]; exact pow178_add sizeChal5_conf)
      le_rfl))

theorem time_chalIL2_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    timeBoundT (chalIL2 hkp confP) (io2 a b 0) ≤ 2 ^ 380 :=
  (timeBoundT_mono _ (io2_mono ha hb)).trans ((time_chalIL2 hkp confP _ _).trans timeChalI_conf)

theorem len_chalIL2_conf (ha : a ≤ 2 ^ 180) (hb : b ≤ 2 ^ 180) :
    lenBoundT (chalIL2 hkp confP) (io2 a b 0) ≤ io2 (2 ^ 182) 0 0 :=
  (lenBoundT_mono _ (io2_mono ha hb)).trans ((len_chalIL2 hkp confP _ _).trans
    (io2_mono (by simpa only [kp] using lenChalI_conf) le_rfl))

end Lifted

/-! ### State counts at `confP` -/

section States

set_option maxRecDepth 100000

theorem sz_finP (o : Fin 82) : SZ (finP o) (60 + 36 * 82) :=
  (sz_prim _).seq ((sz_clearL scrL).mono (by rw [scrL_length]))

theorem hB240 : (2 : ℕ) ^ 182 < 2 ^ 240 := by norm_num
theorem hB239 : (2 : ℕ) ^ 239 < 2 ^ 240 := by norm_num

theorem size_pub3P_conf : (pub3P hkp confP).size ≤ 2 ^ 24 := by
  unfold pub3P
  exact ((sz_pub3Body hkp confP (2 ^ 182) (sizepub3_conf.trans (by norm_num)) hB240).seq
    (sz_finP 15)).mono (by norm_num)

theorem size_pub3L_conf : (pub3L hkp confP).size ≤ 2 ^ 24 := by
  rw [pub3L, lift256, liftP, size_frame]; exact size_pub3P_conf

theorem size_pubIL_conf : (pubIL hkp confP).size ≤ 2 ^ 24 := by
  rw [pubIL, lift256, liftP, size_frame, pubIP]; exact size_pub3P_conf

theorem size_chal3L_conf : (chal3L hkp confP).size ≤ 2 ^ 25 := by
  rw [chal3L, lift256, liftP, size_frame, chal3P]
  exact ((sz_chal3Body hkp confP (2 ^ 182) (sizeChal3_conf.trans (by norm_num)) hB240).seq
    (sz_finP 10)).mono (by norm_num)

theorem size_pub5L_conf : (pub5L hkp confP).size ≤ 2 ^ 24 := by
  rw [pub5L, lift256, liftP, size_frame, pub5P]
  exact ((sz_pub5Body hkp confP (2 ^ 182) (sizepub5_conf.trans (by norm_num)) hB240).seq
    (sz_finP 15)).mono (by norm_num)

theorem size_chal5L_conf : (chal5L hkp confP).size ≤ 2 ^ 25 := by
  rw [chal5L, lift256, liftP, size_frame, chal5P]
  exact ((sz_chal5Body hkp confP (2 ^ 182) (sizeChal5_conf.trans (by norm_num)) hB240).seq
    (sz_finP 10)).mono (by norm_num)

/-- **The simulation-data programs** (inside the key component). -/
theorem size_sd3P_conf : (sd3P hkp confP).size ≤ 2 ^ 25 := by
  unfold sd3P
  exact ((sz_sd3Body hkp confP (2 ^ 239) sizeSd3_conf hB239).seq (sz_finP 13)).mono (by norm_num)

theorem size_sdIP_conf : (sdIP hkp confP).size ≤ 2 ^ 25 := by
  unfold sdIP; exact size_sd3P_conf

theorem size_sd5P_conf : (sd5P hkp confP).size ≤ 2 ^ 25 := by
  unfold sd5P
  exact ((sz_sd5Body hkp confP (2 ^ 239) sizeSd5_conf hB239).seq (sz_finP 13)).mono (by norm_num)

end States

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.DualUse.Params

theorem size_chalBodyP (D P : ℕ) (hD : D < 2 ^ 240) (hP : P < 2 ^ 240) :
    (chalBodyP D P).size ≤ 2 * 46836 + 2000 := by
  have h1 := size_natP_le (k := 7) 3 4 D 240 hD
  have h2 := size_natP_le (k := 7) 3 4 P 240 hP
  simp only [chalBodyP, dropF, flipP, withCount, XProg.forN, flipHead, appendTapeP, clrS, nopX,
    size_seq, size_loop, size_ifBit, size_prog, Prog.size, Prim.pad]
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
theorem size_chalIL2_conf : (chalIL2 hkp confP).size ≤ 2 ^ 17 := by
  rw [chalIL2, lift256, liftP, size_frame, chalIL, lift82, liftP, size_frame, chalIP]
  have h := lenChalI_conf
  simp only [sChalI] at h
  exact (size_chalBodyP _ _ (by omega) (by omega)).trans (by norm_num)

end AdvancedEncryption.DualUse.Prog
