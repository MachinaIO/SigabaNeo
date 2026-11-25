import PE.Impl.ExpLUT.Prog.RedKeyC3MA
import PE.Impl.ExpLUT.Prog.RedKeyPktOk

/-!
# Cost certificate of `mid`, phase M3 (part 2): the `AD` mirrors of the phases of `pkOf pkt`

`pkOf pkt = pkConstC Dc ; pkCfC Dc ; pktC Dc` with
`pktC Dc = pkMoveC ; templates(sw) ; pkWalkC ; templates(pb) ; pbPubC ; templates(lp) ; pkFinC`.
Every `natC`/template argument is replaced by a closed numeral upper bound (exact for the
`SeConst` templates, which `RedKeyC4H.c4In` requires exactly; the field offsets by the word
lengths). The descriptions (`AD.Er`) are proved in `RedKeyC3MB`.
-/

set_option linter.style.longLine false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC3M

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog AdvancedEncryption.ExpLUT.Prog.RedKeyC4
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

/-- `m̄` at `Dc`. -/
def m3Mb : ℕ := 3 * 2 ^ 40 + 408
/-- The number of slabs at `Dc` (`m̄ + b · 4K`). -/
def m3NSl : ℕ := m3Mb + 22 * (4 * 2 ^ 16)

/-- `pkConstC`: `clr 6 ; bitsC 5 rB1 6 ; templates`. -/
def m3ConstL : List (Fin 64 × ℕ) :=
  [(rKc, 9), (rBit1, 1), (rTb, 22), (seTRec, (32 * 2 ^ 48 + 12 * 2 ^ 16) * 2 ^ 40),
   (rTK, 2 ^ 16), (rTK1, 2 ^ 16 - 1), (rZ, 2 ^ 40), (rT2K, 2 ^ 17), (rTKNK, 2 ^ 56),
   (rT2KNK, 2 ^ 57), (rT4KNK, 2 ^ 58), (rOne, 2 ^ 40), (rMu0, 2 ^ 40), (rT4K, 2 ^ 18),
   (rTW, 2 ^ 22), (rTtab, 14 * 2 ^ 22), (rXc, 2 ^ 40), (rTe, 14)]

def m3Const : AD := .s (.a (.c (.clr 6))) (.s (.a (.c (bitsC 5 rB1 6))) (twL m3ConstL))

/-- `pkCfC Dc` (`natC` leaves: `cpLen − predLen = 13 · 2^22`, `nSl`, `m̄`). -/
def m3Cf : AD := .a (.s (.c (.cp 4 rCs)) (.s (.nat 29 rB1 (13 * 2 ^ 22)) (.s (.c (.app rCs 29))
  (.s (.c (.cp 30 rCs)) (.s (.c (.clr rCs)) (.s (.nat seLoopC rB1 m3NSl) (.s (.c (.cp 32 seLoopC))
  (.s (.c (.rep 32 (.app rCs 30))) (.s (.nat 29 rB1 m3Mb) (.c (.app rCs 29)))))))))))

def m3SwL : List (Fin 64 × ℕ) :=
  [(swT8, 8), (swT14, 2 ^ 14), (swT2N, 2 ^ 25), (swOne, 1), (pkT1, 2 ^ 40 - 1), (swT14b, 14),
   (swTtab, 14 * 2 ^ 22), (swB1, 1), (swT16, 16)]

def m3PbL : List (Fin 64 × ℕ) :=
  [(ptTB, 22), (ptT16, 16), (ptTM, 2 ^ 58), (ptTAa, 2 ^ 92), (pbTN, 2 ^ 40), (pbTV, 2 ^ 57),
   (pbTC, 2 ^ 17), (pbKg, 9), (pbOH, 2 ^ 98), (pbOh, 2 ^ 110), (pbOAa, 2 ^ 98), (pbOAin, 2 ^ 98),
   (pbOa, 2 ^ 98), (pbOcb, 2 ^ 110), (pbOA0, 2 ^ 98)]

def m3LpL : List (Fin 64 × ℕ) :=
  [(ptTSP, (2 ^ 52 + 2 ^ 18 + 1) * 2 ^ 40), (ptTm, m3Mb), (ptTC, 2 ^ 17), (ptTD, 2 ^ 34),
   (ptOne, 1), (4, 2 ^ 40 - 1), (ptZero, 2 ^ 40), (ptZ2, 2 ^ 57), (ptZL, (2 ^ 22 - 1) * 2 ^ 57),
   (ptTZb, 2 ^ 21 * m3Mb), (ptTR0b, 2 ^ 17 * m3Mb), (ptTRinb, 2 ^ 55 * m3Mb), (ptB1, 1),
   (pkZoff, 2 ^ 99), (1, 44), (2, 1)]

/-- The input box of M3 (`RedKeyC.c3InB`). -/
def m3In : List ℕ := (((List.replicate 64 0).set 0 (2 ^ 101)).set 1 (2 ^ 110)).set 2 (2 ^ 102) |>.set 3 (211 * 2 ^ 22)

end AdvancedEncryption.ExpLUT.Prog.RedKeyC3M
