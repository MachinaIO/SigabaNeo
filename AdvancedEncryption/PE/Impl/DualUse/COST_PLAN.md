# Cost budget of the reductions (plan, 2026-11-22)

## Budget
`attributeHiding_of_comps_rlwe` needs `64 · 2^256 · C ≤ 2^kb` with `kb ≤ H ≈ 991` (N = 2^33).
`C ≤ 2^(r+g+11+65k'/41) + 2^(t+6)` (`compConst_le_two_pow`): `2^t` bounds the per-query handler
time (dominated by the key component), `2^r` the states (program sizes `≤ 2^s`, `s + 30 ≤ r`),
`k' ≥ P.tapes + R + 30` the tapes (≈ 304 at R = 254, i.e. 2^482 from `3^tapes`).
Target: per-query time ≤ ~2^556, sizes ≤ 2^25 (r ≈ 55), so C < 2^568 and `64·2^256·C < 2^830`.

## Why the current key component does not fit
Every `Prim` costs a sweep of the longest tape in its frame (`2·supB + 3`). Moving m bits on a
tape sharing a frame with an L-bit tape costs ≈ m·L; only `XProg.frame` shrinks L.
Sizes: wire value V = d·2k·N·K ≈ 2^144.1 bits; f̂ has g ≈ 2^158.6 gates; slpEvalP's store
≈ 2^302.7 bits; the unary gate stream 2·W·g ≈ 2^318.2 bits; `sd` ≈ 2^234 bits.
Real time of the current design: `fhatGen` ≥ 2^810 (VM list tapes ≈ 2^491 bits), slpEvalP
selection ≈ 2^765, unframed `simStepP` ≈ 2^700. Uniform bounds `tbC·(L+1)^tbD` are worse still.

## Plan (two-level structured evaluation; no global gate list, no RegVM, no 2^303 store)
1. **SLP relocation lemma** (Lib, generic): the gates a builder appends to `p` evaluate as a local
   SLP whose inputs are the values of the referenced wires. Instantiate for the modular adder in
   `pairRound`, the leaf/term block, the constant/gadget term (`GSWCircuit.lean`, `FhatLoop.lean`:
   `compileSLPL → nandBlockL → coefCircuitL = leaves + rounds/pairRound + foldSum`).
2. **`slpEvalX`**: slpEvalP as an XProg with `simStepP ginvTopP` in a `frame` (own tapes
   ≤ 2^144.1) and selection in a frame with the small store; per-tape bound via AbsBound
   (summarise `matMulP` as in `SpecT.lean`). Used only on the fixed adder SLP (≈ 2^32.1 gates,
   stream ≈ 2^65 bits, store ≈ 2^176.2 bits; ≈ 2^377.6 per adder gate).
3. **Outer program** (plain Prog loops over template tapes N, k, 2kN, 4kN, 61): per predicate
   gate (≤ 375), per output coefficient (4kN = 2^61): build the leaf list (FIFO ≈ 2^230 bits),
   then ≤ 61 halving rounds calling the adder. ≈ 2^534 (FIFO) + 2^536.2 (arithmetic).
   Wire bundles 2^231 bits each, ≤ 385 of them.
4. **Final sum**: `simKeyP`/`boundsT_keySumP` on the output bundle only, identity positions
   (W ≈ 2^87): ≈ 2^551–2^552.5 (2^466 if framed). Ring-GSW simulation of the predicate ≈ 2^390.
5. Result: key handler ≈ 2^553–2^555.
6. **Done** (e6050aa): `compConst_le_two_pow` takes `c.L ≤ 2^lc`, `lc + 30 ≤ r`.
7. **Shrink program sizes**: `putW` ≈ 36 states/bit and template literals `rp (lenA …)` (2^144),
   `rp W` make s ≈ 150–165. Generate templates by doubling/product loops from small constants
   (also K, d): s ≈ 25. Same for setup/pub/chal/sd components and the decoder.
8. **Per-tape bounds for setup/pub/chal/sd and the decoder**: their uniform bounds on 2^234-bit
   states give ≥ 2^936; honest ≈ 2^470. Use `timeBoundT`/AbsBound with frames.
Larger N is a fallback lever (time ≈ N^5, H ≈ linear in N).

## Status of the block-structured `W_f` (branch `t3/wfb2-block-structured`, 2026-11-23)

Design actually taken (it replaces steps 1–2 above by a cheaper route with the same costs):

* **Shadows instead of relocated local SLPs** (`Lib/Lattices/Homomorphic/SLPShadow.lean`,
  `Lib/Lattices/Algo/FhatShadow.lean`): under any semantics `valueOf inp one step`, every builder's
  output wires evaluate to a fixed function of the values it reads (`sh_addNand … sh_modAdd`,
  `sh_modSub`, `sh_coefCircuitL`, `sh_nandBlockL`), and `valueOf_fhatSLPL`: the output wires of
  `fhatSLPL` evaluate to `fhatV` (one `nandV` per predicate gate, `coefV` per output coefficient).
  No local gate streams are needed: the machine evaluates the shadows directly.
* **Framed abstract interpreter** (`Lib/Machines/Prog/XAbs.lean`): `XAst H n` (leaves, frames,
  branches, loops, calls of certified `Sound` summaries at substituted variables `pSubst`, framed
  calls with summaries valid under a hypothesis `H` — e.g. a step whose cost is a variable),
  `xabs_sound`: absolute per-tape time bounds charging each frame only its own tapes.
  `XFlat.lean`: frames are semantically relabellings (`law_eq_run_flat`).
* **The step**: `Lib/Lattices/ProgAlgo/SimStepT.lean`, `xsound_simStepP` (top-gadget simulation
  step on joint words, `≈ (2V+3)·(matMul sweeps)`, every primitive charged `qT ≈ V`).
* **Word machine** `Lib/Machines/Prog/ValVM.lean`: 64 word tapes + a generic framed step
  (`VStep`, `StepCert`), codes `gate/mvV/mv/cp/drop/clr/tl/rep/seq/ifb/nop`, total semantics
  `exec`, compiler `compileA` to `XAst` (each instruction framed on its own tapes),
  `law_compileA` (correctness). Certificates of machine code evaluate fast (e.g. `modAddC`:
  `≈ 47 K · C_step + O(V² K²)`).
* **Arithmetic on the machine**, each proven equal to its shadow for the step `fV`:
  `ValArith.lean` (full adder, `rippleC`, zips `zipC` with mux/and/not/copy, constants,
  `modAddC = modAddV`, `modSubC = modSubV` for `q = 2^K`, `k = K + 1`, terms `termSubC/termAddC`),
  `ValLeaves.lean` (`exec_jloopC`, a loop of terms into the leaves buffer), `ValRounds.lean`
  (`exec_prC` = `pairRoundV` with odd carries, `exec_roundsC`, one number after `clog₂ n` rounds),
  `ValCoef.lean` (`exec_cblockC`: the terms of one column `c'`, the coefficients read from the
  reversed row without a rotation buffer; `terms_column`; `exec_colC`, the `2k` columns;
  `fl_leavesV`), `ValCoefFull.lean` (**`exec_coefC`**: an output coefficient of a NAND block,
  `OUT = flatten (coefV … (enumT N k) … A B Gv a col t)`, from the column digits
  `digitsOf B col c'` and the reversed rows `rowRev A a c'`; constant `CW` supplied).

Remaining (in order):
1. The constant `constV zv k (gvExp q o)` on `CW` per `o` (one `one` at bit `col.2` iff
   `t = 0 ∧ a = col.1 ∧ col.2 < K`), the templates `TM0 = N−1−t`, `TT1 = t+1` per `t`.
2. Block level: per predicate gate, loops over `(a, col, t)` in `enumO` order; per gate and `a` the
   reversed coefficient-major rows `R_{a,c'}` of the operand bundle `A` (transposition of the
   `k × N` blocks, O(N² k) value moves per row, ≈ 2^465 per gate), per `col` the digit stream
   `B(0,col,·,·) ++ B(1,col,·,·)` (contiguous in BI order); outputs per `(a, col)` transposed back to
   BI order ⇒ `nandV`.
3. Gate loop over `parse C` with bundle selection (`repV`: input bundles from `sdEnc sd` in BI order,
   the constant bundle `constRepVV`, earlier blocks), the predicate's Ring-GSW simulation
   (`slpEvalP … ginvGswP`, needs a per-tape bound), `simKeyP` on the output bundle (identity
   positions), templates by doubling loops (`V`, `kV`, `NkV`, `(2kN+1)kV`, …).
4. `valueOf_congr_step`: shadows over `fV` equal shadows over the step on `V`-bit values.
5. Assembly `wfB2`, `wfSpec_wfB2`, its certificate (`xcheck` by `decide +kernel`, symbolic in
   `N, K, k, d, C_step`), `time_keyP` with per-tape hypotheses for the `W_f` block, size bound,
   numerics at `confP`.

### WS-T1 continued (2026-11-23): decisions for the remaining steps

* **128 word tapes** (`ValVM`, 264 tapes): `coefC` writes 40 of the first 61 words and keeps only
  `45, 61, 62, 63` free; the block level needs ~40 more words.
* **No `xcheck` certificate of machine code**: `xabs` on `compileA cert coefC` did not finish in
  5 minutes even as compiled `#eval` (nested `fixIter` over 5 loop levels, `pSubst` of the step's
  polynomial at each `gate`), so `decide +kernel` is out of reach. Replacement: the machine never
  lengthens a word (shift registers, templates), so a **static bound** `B : Fin 128 → ℕ` with
  `B s ≤ B d` for every `cp d s` and `V ≤ B d` for every `gate d` bounds every word during the
  whole run; the cost is then a structural recursion `costC B c` (a loop `rep c b` costs
  `B c · (costC B b + sweep)`), proven `≥ timeBoundT (compileA c)` once for all codes, and
  evaluated at `confP` by `norm_num`.
* **Forward references** (`repV`: `bs.getD m const`): the bundles are kept in a rotated shift
  register `R_t = const^(W−10−t) ++ [const, in₀ … in₉, r₀ … r_{t−1}]` (`W + 1` slots, `W` the unary
  width of the gate word, `BndG W gs`); an operand `j ≤ W` is read from `R_t ++ R_t` at slot
  `(W − 10 − t) + j`, which is `r_m` for `j = 11 + m < 11 + t` and `const` otherwise. No
  topological property of the gate list is needed.
* The predicate's Ring-GSW simulation reuses the same gate loop with slots of one value and the
  block `gate` (a second instance of the machine, step `simStepP ginvGswP`).
* Program sizes: every template comes from `natP` (doubling, `O(log n)` states), every input from
  loops of the machine over the word `sdEnc sd` (no unrolled `itemsP` over `Enum.list`).
* **Width**: the machine has 120 words (256 tapes, the width of the key component); its run is
  framed into `keyP` by a permutation of the 256 tapes.
* **Done** (Lib/Lattices/ProgAlgo): `ValBlock` (column loop, `rrC`, `trC`), `ValNand`
  (**`exec_nandC`**: a NAND block, `RES = bw (nandV … A B)`), `ValGates` (**`exec_gloopC`**: the
  gates of a predicate over the rotated store, generic in the block `BlockSpec`), `ValFhat`
  (`blockSpec_nandC`, `blockSpec_gate`, **`getLast_gl_nandW`**: the last result is
  `bw (fhatV …)` at the output wire; **`valueOf_fV`**: item 4).
* **Cost plan for the machine** (replacing `xcheck`): every instruction will clear its scratch tapes
  (`X0 … X2`) at its end, so each instruction's frame is charged only its own words; then
  `timeBoundT (compileA c) ≤ costC B c` by structural recursion with the static bounds `B`.
  Estimated totals at `confP`: arithmetic ≈ 2^536, block moves ≈ 2^528, transposes ≈ 2^475,
  store reads ≈ 2^488, `simKeyP` on the output bundle ≈ 2^547, setup ≈ 2^500: ≈ 2^547.2.
* **Done, Lib** (cont.): `ValConst` (**`exec_cbC`**, the constant bundle), `ValIns`
  (**`exec_insC`**, the inputs of `f̂` from the streams of the `B_j`, `W_j`, `ψᵢ`), `ValGsw`
  (`gl_values`, `getLast_gl_values`, `exec_insGC`), `ValMain` (**`exec_fhatC`**: `OUTW = bw (fhatV …)`
  from `FInit`; **`exec_gswC`**: `OUTW = valueOf …` of the predicate from `GInit`; `exec_posC`: the
  unary positions). `compileA` clears the scratch of every instruction (`mvPc`, `dropPc`, `inP`).
* **In progress, `PE/Impl/DualUse/Prog/WfB2.lean`**: `wfB2 hk c W = frame eW (wfBody hk c W)`,
  the body in the machine's coordinates (`eW` swaps `0 ↔ word 88`, `1 ↔ word GS`, `2 ↔ 255`):
  `prepT` (gate count by `convP`, `simTmplP`, `natP` templates `stepT`, `wordsT`, `OB`, `ZB`) →
  `runT = compileA … fhatFullC` (streams, `one`, `fhatC`, output to word `45`) → `prepG` →
  `runG = compileA … gswFullC` (… `gswC`, `posC`) → `keyPrep` (templates of `simKeyP` on the step
  tapes) → `simKeyP` framed by `oK2` → `clrsP finClr`. Proven so far: `law_prepT`, the lookups of
  its store (`S1_key`, `S1_eq_S0`, `S1_OB`, `S1_ZB`, `X2_apply`, `Y4_apply`, `X5_apply`).
  Remaining for `wfSpec_wfB2`: `S1 = enc s₀ Vt w` with `SimPre`, `FInit` after `streamsT`/`oneC`;
  law of `runT` (`law_compileA`, `stepSpec_simTop`), `prepG` (same pattern), `runG`, `keyPrep`,
  `run_simKeyP` + the identification with `simKeyStoreW` (`valueOf_fhatSLPL`, `valueOf_fV`,
  `getElem_wireIx`), the cleanup and the frame `eW`.
  Then the cost: per-instruction bounds of `compileA` with static word bounds, the steps'
  summaries (`xsound_simStepP`; the Ring-GSW step needs its own), `natP`/`simTmplP`/`simKeyP`
  bounds, `time_keyP` with the per-tape bound of `wfB2`, the size, the numerics at `confP`.

### Status (2026-11-23, later): `wfSpec_wfB2` proven

* **`wfSpec_wfB2`** (`PE/Impl/DualUse/Prog/WfB2.lean`): `WfSpec hk c (wfB2 hk c W) W` for
  `c : Conf N K (K + 1)`, `0 < N`, `0 < K`, and every window predicate with `parse C ≠ []`,
  `|parse C| + 10 ≤ W`, `BndG W (parse C)`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  Chain: `law_prepT` → `law_runT` (`law_compileA`, `vstepT` from `stepSpec_simTop`, `s1_simPre`,
  `fInit_w2`, `exec_fhatC`) → `law_prepG` (`s3_simPre`) → `law_runG` (`gInit_w5`, `exec_gswC`,
  `exec_posC`) → `law_keyPrep` → `law_keyF` (`key_run`: `run_simKeyP_B2`, the identification
  `fhatOut_eq` / `predOut_eq` with the stores `storeT` / `storeG` of `simKeyStoreW`, `biIx_out`:
  the output coefficient `(0, colE c, i, j)` sits at `(c k + i) N + j` of the bundle) →
  `law_clrsP` → the frame `eW` (`swp_eq`).
* Well-formedness: `Lib/Lattices/ProgAlgo/ValWF.lean` (`wf_compileA`: a compiled code is well
  formed when no loop body writes its counter, `loopOkB`, checked by `decide +kernel`).
* `wordsG` gained the template `TNK` (`oneC` moves `oneW` with it).

### The cost of `wfB2` (route)

* Loops of compiled code are not framed: a round of `rep` costs `2·M + 3` with `M` the longest of
  the 256 tapes (≈ 2^239, the doubled store `TD2`). The rounds number ≈ 2^190 (≈ the steps), so the
  sweeps add ≈ 2^431, far below the step's arithmetic: no change of the compiler is needed.
* `costC`: structural recursion over a code from static word bounds `B` (closed under `cp`, `gate`),
  the step's bound `Tst` (from `xsound_simStepP`; the Ring-GSW step needs its own certificate),
  `V`, `M`; per instruction the closed-form bounds of `inP`, `outP`, `mvPc`, `dropPc`.
