import PE.Impl.RingBTVW.Prog.Comps
import PE.Impl.RingBTVW.Params.Conf

/-!
# Helpers for the cost numerals at `confP`

The lengths of the enumerations of the attribute bits and of the ciphertext bits, `confP.d = 2^65`,
and the unfolding macro `comp_unfold` (the time and size bounds of the components into arithmetic on
the parameters) shared by the cost files.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg AdvancedEncryption.RingBTVW.Params
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

theorem len_Attr {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).Attr)).length = nA := len_fin nA

theorem len_Index {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) :
    (Enum.list (α := (Sdw (N := N) hk).ctBits.Index)).length = 2 * (2 * k * (k * N)) := by
  show (Enum.list (α := Fin 2 × (RingBTVW.Fresh.Col k × (Fin k × Fin N)))).length = _
  simp only [Enum.length_prod, len_fin, len_col]

theorem confP_d : confP.d = 2 ^ 62 := dp_def

theorem scrL_length : scrL.length = 81 := rfl

theorem io2_mono {R : ℕ} {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    io2 (R := R) a b 0 ≤ io2 A B 0 := fun i => by
  simp only [io2]; split_ifs <;> omega

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

end AdvancedEncryption.RingBTVW.Prog
