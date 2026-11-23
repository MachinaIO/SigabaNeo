# WS5 status (KeyGen and Dec shells, front end)

Branch `t3/bp-ws5`, base `e5632ceb`.

## Stage I (tree still date windows)

* **`Prog/FrontSpec.lean`** (new): the interface of a front end.
  `frontG n V bw C` (`[]` if `|C| > n`, `[false]` if not `V C`, `true :: bw C` otherwise);
  `FrontSpecG fr n V bw FT FL FS` for `fr : XProg (R + 2)` (wf, coin-free, law, phase bound
  `Ph fr (io2 T 0 0) (FT T) (io2 (FL T) 0 0)`, `size ≤ FS`); `FrontSpec fr n W` at `ValidC`,
  `blockWord W`. Frames in the shells: `FrEmb e` (`0 ↦ 1`, `j ↦ j + 82`), with `io2_frEmb`,
  `embedF_frEmb`, `law_frame_frEmb`; `eF : Fin 72 ↪ Fin 256` for the Stage-II front end.
* **`KeyFront.lean`**: `frontSpec_frontP : FrontSpec (frontP n W) n W (frontT n W)
  (fun _ => frontL n W) (frontP n W).size` (`frontT`, `frontL`, `cfX_frontP` moved here).
* **`BfSpec`, `CfSpec`, `WfSpec`** are stated on `ValidC` and `blockWord W` (defeq at Stage I).
* **Generic shells** (front end and its frame as parameters), the old names are the
  date-window instances and keep their exact shape (so `KeyPTimeV`, `WfB2Conf`, `AHConcrete*`
  are untouched):
  * `keyPF hk c sdP e fr wfB cf`, `law_keyPF`, `wf_keyPF`, `time_keyPF` (front bounds `FT`, `FL`,
    branch bound `keyMF`); `keyP := keyPF … eFr (frontP c.L W) …`.
  * `keyGenF`, `law_keyGenF`, `wf_keyGenF`, `keyMachineF`, `run_keyMachineF`; `ph_keyGenF` with
    `keyGTF`, `keyBTF`, `keyBLF` (closed forms in `FT (8 (nKG + 2))`, `FL (8 (nKG + 2))`).
  * `decGenF`, `law_decGenF`, `wf_decGenF`, `coinFree_decGenF`, `decMachineF`,
    `deterministic_decMachineF`, `decMachineF_law`; `ph_decGenF` with `decGTF`, `decBTF`,
    `decBLF` (in `FT (16 (nDec + 2))`, `FL (16 (nDec + 2))`).
  * The old `law_keyP`, `law_keyGenP`, `run_keyMachineP`, `law_decGenP`, `ph_keyGenP`,
    `ph_decGenP` are one-line instances at `frEmb_eFr`, `frontSpec_frontP`.

## Stage II preparation (new files, not wired)

* **`Prog/FrontBP.lean`**: `frontBPn n m : XProg 72` (generic in the guard `n` and the word length
  `m`; `frontBP n := frontBPn n bpLen`): guard `leP n` (tapes `0, 64, 65`), length test `lenEqP m`
  (tapes `0, 64 … 68`), for words of `m` bits the cut `cutPn m` (tape `0` replaced by its first `m`
  bits through a template on tape `69`; semantically the identity, it makes the static bound of
  tape `0` equal to `m`), tapes `1 … 63` cleared, the compiler `bpCompC` on the first `64` tapes,
  `true` consed; every tape but `0` cleared.
  **`law_frontBPn`** / **`law_frontBP`**: `(frontBP n).law (io2 C [] []) = pure (io2 (frontG n
  (·.length = bpLen) bwBP C) [] [])`, `bwBP C = rpW 512 (bpRP (tablesOf C))` (from `law_bpCompC`,
  `run_lenEqP`, `run_leP`; nothing about the circuit is unfolded). `wf_frontBP`, `coinFree_frontBP`.
* **`Prog/FrontBPCost.lean`**: `ph_frontBPn`: from `io2 T 0 0`, at most `frontBTn n m T` steps,
  output at most `frontBA m = m + allG + S0 + 1` bits **whatever `T`** (`frontBA_le`: `≤ 2^63` for
  `m ≤ 2^49`), the other tapes blank; `frontBTn_le`: `frontBTn n m T ≤ 2^6 · X^2` for
  `m ≤ bpLenA`, `m ≤ 2^49`, `n, T + 1 ≤ X`, `2^64 ≤ X` (the compiler `≤ 2^126`, the length test
  quadratic); `size_frontBPn_le`: `≤ 36 n + 60 m + 500 log₂ m + 2^27 + 2^19`, `size_frontBP_le`:
  `≤ 36 n + 2^56`; **`frontSpecG_frontBPn`**, **`frontSpecG_frontBP`**.
  At the switch (`ValidC C := C.length = bpLen`, `blockWord 512 = bwBP`) `frontSpecG_frontBP c.L`
  is `FrontSpec (frontBP c.L) c.L 512 (frontBTn c.L bpLen) (fun _ => frontBA bpLen)
  (36 c.L + 2^56)`, and the shells are `keyGenF hk c eF (frontBP c.L) …`,
  `decGenF hk c eF (frontBP c.L) …`, `keyPF hk c sdP eF (frontBP c.L) …` (`frEmb_eF`,
  `R = 70 ≤ 166`).

* **Merged `t3/bp-ws6b`** (24df3c2a, stream block `wfB2S`, `WfSpecR`).
* **`Prog/WfSpecBridge.lean`**: `wfSpec_of_wfSpecR`: `WfSpecR hk c wfB W Ic` gives
  `WfSpec hk c wfB W` given, for every predicate of the class of at most `c.L` bits, a register
  program `rp` with `blockWord W C = rpW W rp`, `nA + W' ≤ W`, `rp.length ≤ Ic`, last instruction
  `ins'` and `predC C = predR rp ins'` (WS1's facts at the switch: `bpRP (tablesOf C)`,
  `length_bpRP < 2^50`, `bnd_bpRP`).
* **`KeyPTimeV.time_keyPFV`** (added lemma): WS9's per-tape `time_keyPV` for any front end
  (`keyPF`, `FrEmb e`, front bounds `FT`, `FL`): with `frontBP` the block's input is
  `wfIn Lsd (frontBA bpLen)`, `frontBA bpLen ≤ 2^63 ≤ Lgn = 2^64`, the shape of
  `time_wfB2S_conf`.

## Commits

| What | Commit |
| --- | --- |
| Stage I (FrontSpec, generic shells), `FrontBP`, `FrontBPCost` | `64229c47` |
| Merge `t3/bp-ws6b` | `bcd5e54e` |
| `WfSpecBridge`, `time_keyPFV`, status | (this commit) |

Axioms of `frontSpecG_frontBP`, `frontBTn_le`, `law_keyGenF`, `ph_keyGenF`, `law_decGenF`,
`ph_decGenF`, `law_keyPF`, `time_keyPF`, `time_keyPFV`, `wfSpec_of_wfSpecR`, `frontSpec_frontP`:
`propext`, `Classical.choice`, `Quot.sound`. Full build green after the merge.

## Tape counts (for WS9 / WS8)

The compiler needs `64` tapes; the front end has `72` and is **framed** inside the shells on the
tapes `1, 83, …, 153`. **KeyGen, Dec and the key component keep `256` tapes** (`XProg 256`), so
the factor `3^tapes` of `descLen` and of the reduction constant does not change (`3^256`).
The front end's states go from `≤ 2^238` (`frontP` at `confP`) to `≤ 36 c.L + 2^56`.

## Clock effect

The block's input bound is `frontBA bpLen ≤ 2^63` (below the `2^64` of the block certificate),
independent of the input bound of the shell. The front end costs `≤ 2^6 X^2` with
`X ≥ 8 (nKG + 2)`, i.e. far below the block (`2^628`) for `X ≤ 2^300`.

## Open (not done here)

* The numerals at `confA` are not done: `KeyTightWin`, and the `frontL`, `frontT`, `2^238` uses in
  `KeyCostConf`, `KeyTightConf`, `DecCostConf`, `DecTightConf`, `DescConf` are still the
  date-window numbers. At the switch they take `frontBTn c.L bpLen` (`frontBTn_le`:
  `≤ 2^6 X^2`, `X ≥ 8 (nKG + 2)`), `frontBA bpLen ≤ 2^63`, `36 c.L + 2^56`, and the block bounds
  of `time_wfB2S_conf`, `size_wfB2S_conf`; then `ksz_arith`, `dsz_arith` at `X = 2^257`. The
  clocks `time_keyMachineP_conf'`, `time_decMachineP_conf'` (`≤ 2^629` expected) and the
  description lengths (`≤ 2^951` expected) are therefore **not proved yet**.
* `BfX`, `CfX` (the key-row and `c_f̂` blocks built on the `W_f` machinery) still take the gate
  list; their stream versions (`BfSpec`, `CfSpec` from `WfSpecR`-like specs) follow WS6b's.
* Not changed (other owners): nothing needs a change outside WS5 files for Stage I.
