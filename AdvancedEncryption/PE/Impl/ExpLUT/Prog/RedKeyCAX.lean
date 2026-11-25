import PE.Impl.ExpLUT.Prog.RedKeyCA
import PE.Impl.ExpLUT.Prog.RedKeyPktOk
import PE.Impl.ExpLUT.Prog.RedKeyMidM
/-!
# Exploration mirrors of the MVM phases of `mid (pkOf pkt)` (ninth session)

The phases with `natC`/template leaves replaced by `CaX.n`/`CaX.t` with **estimated** sizes
(`2^100` for every `mpkW` offset/field, `2^110` for `rawEnc`/`ctW` ones, `gD ≤ 2^30`,
`ptND ≤ 2^36`, `pkNRin ≤ 2^57`; exact: `Dc.N = 2^24`, `Dc.K = 2^16`, `Dc.mb = 3·2^40+408`,
`predLen = 211·2^22`, `tlK = 14·2^22`). Run (in a scratch file importing this module, with
`lake env lean`), e.g.

    #eval caReport (2^120) cxNn cxKn cxM2 cxM2In        -- M2: T = 2^333 (8 s)
    #eval caReport (2^150) cxNn cxKn (.s cxPkConst (.s cxPkCf cxPkt)) cxM3In   -- M3: T = 2^314
    #eval caReport (2^250) cxNn cxKn (.s cxPkConst (.s cxPkCf (.s cxPkt cxSimKey))) cxM3In

(`simKeyC` takes ~3 min compiled.) The third run shows the static blow-up of `sePostC`
(registers `8`, `24` at `2^151` in this over-approximation, `≈ 2^150.39` exactly): see
`RedKeyPLAN.md`, ninth session.
-/

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyC

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.RedKeyPkt AdvancedEncryption.ExpLUT.Prog.RedKeyMid

def cxKn : ℕ := 2^16
def cxNn : ℕ := 2^24
def cxNK : ℕ := 2^40
def cxMb : ℕ := 3 * 2^40 + 408
def cxNT : ℕ := cxMb * cxKn * cxNK
def cxP100 : ℕ := 2^100
def cxRf (src dst : Fin 64) (offb lenb : ℕ) : CaX :=
  .s (.c (.cp 29 src)) (.s (.n 30 offb) (.s (.c (.drop 29 30)) (.s (.n 30 lenb) (.c (takeC dst 29 30)))))
def cxBits0 : CaX := .s (.c (.clr 6)) (.c (bitsC 5 rB1 6))
def cxEvalInit : CaX := .s cxBits0 (.t [(rKc, 2^30), (rBit1, 1), (rTb, 22), (rTBlk, 16*cxKn^3*cxNK), (rTK, cxKn), (rTK1, cxKn), (rZ, cxNK),
   (rT2K, 2*cxKn), (rTKNK, cxKn*cxNK), (rT2KNK, 2*cxKn*cxNK), (rT4KNK, 4*cxKn*cxNK), (rOne, cxNK), (rMu0, cxNK), (rT4K, 4*cxKn), (rTW, 2^22),
   (rTtab, 14*2^22), (rXc, cxNK), (rTe, 14), (rT15, 15)])
def cxKeyPrep : CaX :=
  .s cxBits0 (.s (cxRf 0 17 0 cxP100) (.s (cxRf 0 16 cxP100 cxNT) (.s cxEvalInit
   (.s (cxRf 17 2 cxP100 cxP100) (.s (cxRf 17 4 cxP100 cxP100) (.s (cxRf 17 0 cxP100 cxP100) (.s (cxRf 17 1 cxP100 cxP100)
   (.s (.c evalScratchC) (.s (.c evalC) (.c (.seq (.cp 8 rA) (.cp 14 17))))))))))))
def cxM2 : CaX := .s (.n 6 cxNT) (.s (.c (.seq (.cp 0 2) (.app 0 6))) cxKeyPrep)
def cxTmplK : List ℕ := (List.replicate 64 0).set 35 cxKn
def cxM2In : List ℕ := (((List.replicate 64 0).set 2 cxP100).set 3 (211*2^22)).set rB1.val 1

def cxP110 : ℕ := 2^110
def cxNSl : ℕ := cxMb + 22 * (4 * cxKn)
def cxPkConst : CaX := .s cxBits0 (.t [(rKc, 2^30), (rBit1, 1), (rTb, 22), (seTRec, (32*cxKn^3+12*cxKn)*cxNK), (rTK, cxKn), (rTK1, cxKn), (rZ, cxNK),
   (rT2K, 2*cxKn), (rTKNK, cxKn*cxNK), (rT2KNK, 2*cxKn*cxNK), (rT4KNK, 4*cxKn*cxNK), (rOne, cxNK), (rMu0, cxNK), (rT4K, 4*cxKn), (rTW, 2^22),
   (rTtab, 14*2^22), (rXc, cxNK), (rTe, 14)])
def cxPkCf : CaX := .s (.c (.cp 4 rCs)) (.s (.n 29 (14*2^26)) (.s (.c (.seq (.app rCs 29) (.seq (.cp 30 rCs) (.clr rCs))))
  (.s (.n seLoopC cxNSl) (.s (.c (.seq (.cp 32 seLoopC) (.rep 32 (.app rCs 30)))) (.s (.n 29 cxMb) (.c (.app rCs 29)))))))
def cxPkt : CaX := .s (.c pkMoveC) (.s (.t [(swT8, 8), (swT14, 2^14), (swT2N, 2*cxNn), (swOne, 1), (pkT1, cxNK), (swT14b, 14), (swTtab, 14*2^22), (swB1, 1), (swT16, 16)])
  (.s (.c pkWalkC) (.s (.t [(ptTB, 22), (ptT16, 16), (ptTM, 4*cxKn*cxNK), (ptTAa, 16*cxKn^3*cxNK), (pbTN, cxNK), (pbTV, 2*cxKn*cxNK), (pbTC, 2*cxKn), (pbKg, 2^30),
   (pbOH, cxP100), (pbOh, cxP110), (pbOAa, cxP100), (pbOAin, cxP100), (pbOa, cxP100), (pbOcb, cxP110), (pbOA0, cxP100)])
  (.s (.c pbPubC) (.s (.t [(ptTSP, (16*cxKn^3+4*cxKn+1)*cxNK), (ptTm, cxMb), (ptTC, 2*cxKn), (ptTD, 2^36), (ptOne, 1), (4, cxNK), (ptZero, cxNK),
    (ptZ2, 2*cxKn*cxNK), (ptZL, 2^22*2*cxKn*cxNK), (ptTZb, 2^21*cxMb), (ptTR0b, 2^17*cxMb), (ptTRinb, 2^57*cxMb), (ptB1, 1), (pkZoff, cxP110),
    (1, 44), (2, 1)]) (.c pkFinC))))))
def cxM3In : List ℕ := ((((List.replicate 64 0).set 0 cxP110).set 1 cxP110).set 2 cxP100).set 3 (211*2^22)


/-- `simKeyC Dc` (fix A: the count `seMb := 0^{m̄}` is a `natC` leaf). -/
def cxSimKey : CaX := .s (.c seLoopKC) (.s (.n seMb cxMb) (.c sePostC))

def cxM4 : CaX := .s cxPkConst (.s cxPkCf (.s cxPkt (.s cxSimKey (.s (.c (.cp 14 2)) 
  (.s (.c (.seq (.cp rxW rTW) <| .seq (.cp rxTb rTb) <| .seq (.cp rxOne rOne) <|
  .seq (.eqb rxTru rxW rTW) <| .seq (.eqb rxFal rxTb rxW) (.eqb rB1 rxTb rxW)))
  (.s (cxRf 14 rxH cxP100 cxP100) (.s (.n rxTs (2^22 * cxMb)) (.c simXC))))))))


def cxWalk : CaX := .s cxPkConst (.s cxPkCf (.s (.c pkMoveC) (.s (.t [(swT8, 8), (swT14, 2^14), (swT2N, 2*cxNn), (swOne, 1), (pkT1, cxNK), (swT14b, 14), (swTtab, 14*2^22), (swB1, 1), (swT16, 16)])
  (.c pkWalkC))))

end AdvancedEncryption.ExpLUT.Prog.RedKeyC
