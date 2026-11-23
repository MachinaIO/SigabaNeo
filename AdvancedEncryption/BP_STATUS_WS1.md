# WS1 status

- M0 committed 91a3fb00 (PE/BranchingProgram.lean, Homomorphic/RegProg.lean, neutral names in ImplBase.lean). Full AdvancedEncryption build green.
- M3 committed e58a15c7: `Homomorphic/MuxTree.lean`, `Gates/BPCircuit.lean` (`evalBool_bpPred`,
  `depth_bpPred ≤ 1054`, `length_bpRP = 1443 · 2^39 − 770`, `bnd_bpRP < 312`), `Gates/BPWord.lean`
  (`bpLen`, `bpWord`, `tablesOf`, `tablesOf_bpWord`, `bpWord_tablesOf`, `attrOf`, `encAttr_onto`,
  `card_attr`, `bpEvalFun`, `bpEvalMachine`, `bp_authorized_iff`, `expressive_bp`).
- Stage I committed b308da4c in the WS1 DualUse files. Full build green.

Warning for every workstream: never `unfold bpPred`, `bpRP` or `RP.toSLP` of a concrete program
(Lean then tries to evaluate 2^49 instructions and runs out of memory). Go through
`RP.pred`/`RP.valueOf_pred` (or `RP.run_eq_valueOf` with a variable program) and the theorems above.
