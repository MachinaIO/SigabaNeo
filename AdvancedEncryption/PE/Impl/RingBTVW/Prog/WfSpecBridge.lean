import PE.Impl.RingBTVW.Prog.WfB2S
import PE.Impl.RingBTVW.Prog.KeyP

/-!
# From the stream block's spec to the shells' spec (Stage II, not wired)

The key component and the shells ask the `W_f` block for `WfSpec hk c wfB W`: on the block word
`blockWord W C` of a predicate of the class, the word of `simW sd C`. The stream block of WS6
(`wfB2S`) meets `WfSpecR hk c wfB W Ic`: on the stream `RP.rpW W rp` of any register program within
the bounds, the word of `simWP sd (predR rp ins')`.

**`wfSpecS_of_wfSpecR`**: the block on the stream (`WfSpecS`, the tail of the block word
`blockWord W C = bit0 C :: rpW W (bpRP (tablesOf C))`) from `WfSpecR`: `rp := bpRP (tablesOf C)`,
`length_bpRP < 2^50`, `nA + 93 ≤ W`, and the predicate as the value of the last instruction's
destination `rOUT` (`bpRP_getLast`). **`wfSpec_tailB`**: the block behind the bit (`tail 1` first)
meets `WfSpec` on the block word, for the key component of the reductions.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
open AdvancedEncryption.RingBTVW.Fresh

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

theorem tree_getLast {ι : Type*} {W : ℕ} (L : MuxTree.Layout ι W) (leaf : ℕ → Bool) :
    ∀ (m base : ℕ) (dst : Fin W),
      (MuxTree.tree L leaf m base dst).getLast? = some ⟨dst, .reg L.x1, .reg L.x2⟩
  | 0, _, _ => by simp [MuxTree.tree, MuxTree.node]
  | m + 1, _, _ => by
    rw [MuxTree.tree, List.getLast?_append, MuxTree.node]
    simp

open AdvancedEncryption.PE.Gates.BPCircuit in
theorem bpRP_getLast (F : AdvancedEncryption.PE.BranchingProgram.BP) :
    (bpRP F).getLast? = some ⟨rOUT, .reg (lay 15).x1, .reg (lay 15).x2⟩ := by
  rw [bpRP, lastRP, List.getLast?_append, List.getLast?_append, tree_getLast]
  simp

open AdvancedEncryption.PE.Gates.BPCircuit in
theorem predC_eq_pred (C : List Bool) : predC C = RP.pred (bpRP (tablesOf C)) rOUT := rfl

theorem predR_eq_pred {W' : ℕ} (rp : RP (Fin nA) W') (ins' : Instr (Fin nA) W') :
    WB2.predR rp ins' = RP.pred rp ins'.dst := rfl

open AdvancedEncryption.PE.Gates.BPCircuit in
/-- **`WfSpecS` from the stream spec** at the store width `W ≥ 311` and the instruction bound
`Ic ≥ 2^50`: the stream of a program word is that of `bpRP (tablesOf C)`, of
`633 · 2^21 − 266 < 2^50` instructions on `93` registers, and its predicate is the value of the
last instruction's destination `rOUT` (`bpPred = RP.pred · rOUT`). -/
theorem wfSpecS_of_wfSpecR {wfB : XProg 256} {W Ic : ℕ} (h : WfSpecR hk c wfB W Ic)
    (hW : 311 ≤ W) (hIc : 2 ^ 50 ≤ Ic) : WfSpecS hk c wfB W where
  wf := h.wf
  law sd C _ _ := by
    have hp : WB2.predR (bpRP (tablesOf C)) ⟨rOUT, .reg (lay 15).x1, .reg (lay 15).x2⟩ = predC C := by
      rw [predR_eq_pred, predC_eq_pred]
    rw [blockWord_eq, List.tail_cons, h.law sd (bpRP (tablesOf C)) _ (by have : nA = 128 := rfl; omega)
      ((le_of_eq (length_bpRP _)).trans (le_trans (by norm_num) hIc)) (bpRP_getLast _), hp,
      ← simW_eq_P]

/-- The stream block behind the bit `f(0)`: the head of tape `1` dropped first. -/
def tailB (wfB : XProg 256) : XProg 256 := XProg.seq (XProg.prog (.prim (.tail 1))) wfB

/-- **`WfSpec` (on the block word) from `WfSpecS` (on the stream)**, for the key component of the
reductions, which does not use the bit `f(0)`. -/
theorem wfSpec_tailB {wfB : XProg 256} {W : ℕ} (h : WfSpecS hk c wfB W) :
    WfSpec hk c (tailB wfB) W where
  wf := ⟨trivial, h.wf⟩
  law sd C hL hC := by
    rw [tailB, XProg.law_seq_pure (XProg.law_prim _ _)]
    have e : Prim.apply (.tail 1) (io2 (R := 254) ((sdEnc hk c).enc sd) (blockWord W C) []) =
        io2 (R := 254) ((sdEnc hk c).enc sd) (blockWord W C).tail [] := by
      funext t
      by_cases h1 : t = 1
      · subst h1; simp [Prim.apply, io2]
      · have h1' : t.val ≠ 1 := fun e => h1 (Fin.ext e)
        simp only [Prim.apply, Function.update_of_ne h1, io2, h1', if_false]
    rw [e, h.law sd C hL hC]

end AdvancedEncryption.RingBTVW.Prog
