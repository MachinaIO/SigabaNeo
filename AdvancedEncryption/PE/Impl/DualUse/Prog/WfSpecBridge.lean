import PE.Impl.DualUse.Prog.WfB2S
import PE.Impl.DualUse.Prog.KeyP

/-!
# From the stream block's spec to the shells' spec (Stage II, not wired)

The key component and the shells ask the `W_f` block for `WfSpec hk c wfB W`: on the block word
`blockWord W C` of a predicate of the class, the word of `simW sd C`. The stream block of WS6
(`wfB2S`) meets `WfSpecR hk c wfB W Ic`: on the stream `RP.rpW W rp` of any register program within
the bounds, the word of `simWP sd (predR rp ins')`.

**`wfSpec_of_wfSpecR`**: `WfSpec` follows from `WfSpecR` as soon as every predicate of the class of
at most `c.L` bits has a register program `rp` with `blockWord W C = RP.rpW W rp`, the bounds of
`WfSpecR`, and `predC C = predR rp ins'` for its last instruction (the hypothesis `hrep`). At the
switch (`blockWord W C := rpW W (bpRP (tablesOf C))`, `predC := bpPred ∘ tablesOf`) `hrep` is
WS1's: `rp := bpRP (tablesOf C)`, `length_bpRP < 2^50`, `bnd_bpRP` for `nA + W' ≤ 512`, and the
predicate as the value of the last instruction's destination.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
open AdvancedEncryption.RingBTVW

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- **`WfSpec` from the stream spec** and a register program for every predicate of the class. -/
theorem wfSpec_of_wfSpecR {wfB : XProg 256} {W Ic : ℕ} (h : WfSpecR hk c wfB W Ic)
    (hrep : ∀ C : List Bool, C.length ≤ c.L → ValidC C →
      ∃ (W' : ℕ) (rp : RP (Fin nA) W') (ins' : Instr (Fin nA) W'),
        blockWord W C = RP.rpW W rp ∧ nA + W' ≤ W ∧ rp.length ≤ Ic ∧ rp.getLast? = some ins' ∧
          predC C = WB2.predR rp ins') :
    WfSpec hk c wfB W where
  wf := h.wf
  law sd C hL hC := by
    obtain ⟨W', rp, ins', hb, hW, hI, hl, hp⟩ := hrep C hL hC
    rw [hb, h.law sd rp ins' hW hI hl, ← hp]
    rfl

end AdvancedEncryption.DualUse.Prog
