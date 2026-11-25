import PE.Impl.ExpLUT.Prog.RedKeyPktExec
/-!
# The packet stream, part 16: `PktOk pkt` and the middle phases of `keyP`

**`pkt = pktC Dc`** (`RedKeyPktAsm`), **`wf_pkt`**, **`pktOk_pkt : PktOk pkt`** (the footprint by
`pktC_keeps`, the stream by `exec_pktC` at `Dc`, where `2^22 ≤ 2N`), and the closing theorem
**`rkMidOk_pkt : RkMidOk (mid (pkOf pkt))`** (`rkMidOk_pkOf`).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Tape.MVM
open AdvancedEncryption.ExpLUT.Prog.RedKeyMid

theorem pk_two_pow_le_Dc : 2 ^ 22 ≤ 2 * Dc.N := by
  show 2 ^ 22 ≤ 2 * 2 ^ AdvancedEncryption.ExpLUT.Params.en
  norm_num [AdvancedEncryption.ExpLUT.Params.en]

/-- **The packet-stream code of phase M3.** -/
noncomputable def pkt : Code := pktC Dc

/-- **`pkt` is well formed.** -/
theorem wf_pkt : pkt.WFc := wf_pktC Dc

/-- **The packet-stream contract.** -/
theorem pktOk_pkt : PktOk pkt :=
  ⟨fun r hr => pktC_keeps Dc r hr, fun σ C hC w h0 h1 h2 h4 =>
    exec_pktC Dc pk_two_pow_le_Dc σ _ _ C hC w h0 h1 h2 h4⟩

/-- **The middle phases of `keyP`** (`m1P … midFin` with `pkOf pkt`). -/
theorem rkMidOk_pkt : RedKeyM.RkMidOk (mid (pkOf pkt)) := rkMidOk_pkOf pktOk_pkt

/-- `pkOf pkt` is well formed. -/
theorem wf_pkOf_pkt : (pkOf pkt).WFc := wf_pkOf wf_pkt

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
