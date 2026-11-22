# Cost budget of the reductions (plan, 2026-11-22)

## Budget
`attributeHiding_of_comps_rlwe` needs `64 · 2^256 · C ≤ 2^kb`; since plan B (below) `kb ≤ 2650 ≤ H` at N = 2^34 (`Params/Strength.lean`; was 991 at N = 2^33).
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
   **Status (steps 7, 8 done except the key component)**, at `confP`, query/state inputs ≤ 2^180:
   setup3D/5D/ID ≤ 2^403 steps, outputs ≤ 2^182, ≤ 2^25 states (`SetupL`); pub3/pubI/pub5 ≤ 2^423,
   chal3 ≤ 2^430, chal5 ≤ 2^440, chalIL2 ≤ 2^380 (outputs ≤ 2^182), all ≤ 2^25 states, sd3/sdI/sd5
   ≤ 2^25 states (`CompCost`); decoders ≤ 2^350 steps, ≤ 2^16 states, 14 tapes (`DecodeCost`);
   auth (`authL`, a search over valid date pairs with a gate generator) ≤ 2^275 steps for queries
   ≤ 2^240 bits, output 1 bit, ≤ 2^19 states (`AuthL`, certified by the numeric interpreter
   `NB.check`, `SigabaNeo.Lib.Machines.Prog.NumBound`).
Larger N is a fallback lever (time ≈ N^5, H ≈ linear in N).

## KeyGen/Dec machines (WS-S2 state, 1e9a533)
`keyMachineP`/`decMachineP` (`Prog/KeyGenP.lean`, `Prog/DecGenP.lean`, swapped in by `ImplP.lean`)
are proven; their clocks are `timeBoundT` terms, not yet closed. To close them:
1. `leP`/`unfrP`/`frP` occur as `prog (Prog.map u p)`; redo `ubp_*` (`FrameIO.lean`) for any
   injective relabelling `u` (only `ubp_prim`/`ubp_prim0`/`ubp_loop` are used), or use
   `frame e (prog p)` with a law lemma for coin-free `p`.
2. `timeBoundT_frontP`/`timeBoundT_cutLook` need the scratch tapes at length 0; bound the
   guard → parse → front prefix by per-tape bounds by hand (or generalise `cutLook` to `Z`).
3. Pieces: key try `23(M+1)² + 11494·(2M+1)^8`, `putT`/`prefT`/`tmplT`, `ub_clearL`, `ubp_tailsP`;
   `tbC`/`tbD` of `decFP`/`ballP` by `decide +kernel`; `bfX`/`cfX` through `∀ M, UB … M (T M) (L M)`.
The `BfSpec`/`CfSpec` instances come from the generic two-level evaluator (WS-T1).

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

## Plan B (2026-11-23): more Ring-LWE strength instead of a tight budget
The registry's `RingLWE.H` (`Estimator.estimatorBits`) saturates near 1024 bits: every lattice scan stops
at `β < 1754` (the estimator's `conf.max_beta`, ≈ 2^512), exhaustive search is cut at 10000 bits, and the
all-infinite fallback is `bitsCap = 1024`. At N = 2^33 the attacks need β ≈ 4041 (≈ 1193 bits with the
scan extended), at N = 2^34 β ≈ 9400 (≈ 2700 bits). Decision of the owner: extend the estimator and raise N.
* **B1** (branch `t3/estimator-large-params`): one configurable max block size (raised), a fallback bounded by
  the reduction cost at that block size, evaluation fast enough for `decide +kernel` at n = 2^34,
  q = 2^(2^25); `kb ≤ RingLWE.H (params3/params5)` at N = 2^34 in `Params/Strength.lean`.
* **B2** (branch `t3/confp-n34`): `Np = 2^34`, `dp = 2^61` (LHL needs |Wd| ≥ 2KN + 600), all `*_conf` lemmas.
With kb ≈ 2000+, the budget `64·2^256·C ≤ 2^kb` leaves room far above the per-query target of 2^556.

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
* **Done** (`Lib/Lattices/ProgAlgo/ValCost.lean`): certificates of the instruction programs
  (`inP`: `7 + 6V` sweeps, `mvPc`: `4 + 6|c|`, `dropPc`: `3 + 3|c|`, `outP`: `4`, `cp`/`clr`/`tl`/`nop`:
  `1`), each charged its own frame (`frame_of_check`); `Inv X β T`; **`inv_compileA`**: from bounds
  below `encB bs V B`, a code with `validB` (gate results and copies fit their words) takes at most
  `costC bs V Tst M B c` steps and keeps the bounds, given the step's per-tape summary below `bs`.
  `costC` evaluates in the kernel in seconds (`decide +kernel`); the word bounds `B` must be tight
  (a uniform `2^240` gives `2^2315` through the nested loop counters).
* Ring-GSW step: `Lib/Lattices/ProgAlgo/SimStepGT.lean` (`aStepG`, the certificate of
  `simStepP ginvGswP`: split, two `ginvP` calls, join, `simPost` with `r = 2`).
* Phases (to do): `Ph X βin T βout`; `prepT`/`prepG` per-tape (`natP_bounds`: exact templates;
  `convP` framed on small tapes, `Prog.timeBound` at the gate list's size; `boundsT_simTmplP`); the
  counter `tX0` of `tmplP` gets the largest template as abstract bound, so `prepT`/`prepG` end with
  `clr tX0` (the run needs blank scratch); `keyPrep` → `boundsT_simKeyP`; the final clear; the frame
  `eW`; then `time_keyP` with a per-tape hypothesis at the call of the block (`io2 Lsd (frontL …) 0`).
* **Flow-sensitive bounds** (`absC`, `absC_sound` in `ValCost.lean`): a single static bound per
  word is too coarse (word `72` is a 2-round counter of `nandC` and carries `2^233` bits in
  `insC`: `costC` gives `2^799`). `absC` tracks a list of 120 word bounds through the code (copies,
  results, clears as strong updates, loops at a joined invariant `findInv`, branches joined) and
  `absC_sound` proves `Ph (compileA cert c).toX (encB bs V (gB L)) T (encB bs V (gB L'))`.
* **Numbers at `confP`** (`N = 2^33`, `K = 2^25`, `k = K + 1`, `d = 2^60`, `W = 512`,
  `|sdEnc| ≤ 2^233`, gate list `≤ 2^20` bits): `pEval ρ cStep2 ≤ 2^379` (kernel), the Ring-GSW step
  `≤ 2^380`; `absC` on `fhatFullC`: `2^543`; on `gswFullC`: `2^470`; `simKeyP`:
  `(2·2^229 + 3) · simKeySweeps ≈ 2^229 · 2^316`; total ≈ `2^547`.
* `prepT`/`prepG` frame `convP` (charged its small tapes) and `simTmplP`, clear word `12` after
  `convP` (its abstract bound would exceed `simTmplP`'s input bounds) and the counter `tX0` after the
  templates. `XProg.Ph` (`Lib/Machines/Prog/PhaseB.lean`), `ph_tmplP`, `ph_putW`.
* `W = 512` covers the window predicates (`length_winGates`: ≤ 375 gates); `BndG 512` and
  `parse C ≠ []` for window words remain to be shown for the instance at `confP`.

### Status (2026-11-23, evening): the time of `wfB2` at `confP`

* **`time_wfB2_conf`** (`Prog/WfB2Conf.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`):
  from `sdEnc` of at most `2^234` bits and a gate list of at most `2^20` bits,
  `timeBoundT (wfB2 hk c 512) ≤ 2^555`, every tape below `2^240` afterwards, under the
  hypotheses `N = 2^33`, `K = 2^25`, `c.d = 2^60`, `treeHeight ≤ 64`, the stream offsets
  `≤ 2^234`. Route: `XProg.Ph` phases (`ph_prepT`, `ph_runT` = `absC_sound` + `xsound_simStepP`,
  `ph_prepG`, `ph_runG` = `absC_sound` + `xsound_simStepG`, `ph_keyPrep`, `ph_simKey`
  (`boundsT_simKeyP`), `ph_finClr`), glued by kernel checks on closed numerals (`chk_*`,
  `decide +kernel`, ≈ 3 min): the run of `f̂` `≤ 2^554`, the predicate's run `≤ 2^480`,
  `simKeyP` `≤ 2^548`, the preparations ≈ `2^490`.
* Changes to `wfB2` for the bounds (laws re-proven): `convP` replaced by `countP` (the gate count,
  `Lib/Machines/Prog/CountP.lean`: law and per-tape bounds); `convP`/`simTmplP` framed; clears of
  word `12`, of the counter `tX0` of `tmplP`, of step tape `92` (blank in the Ring-GSW step), all the
  step's tapes before `simKeyP`; `nBI` in closed form.
* **Next**: the abstract bound of the gate count after `countP` is the length of the gate list's
  tape (one bit per round), and the front end of `keyP` bounds that tape by `frontL c.L W` (the
  size of its lookup table, ≈ 2^35): the gate loop would be charged ≈ 2^35 rounds. Fix: truncate the
  count to `W` bits after `countP` (identity, `|gs| + 10 ≤ W`), making the runs' cost independent of
  the gate list's bound; then `time_keyP` with a per-tape hypothesis on the block at
  `io2 Lsd (frontL c.L W) 0`, the size bound, `hP` for the windows at `W = 512`.
* **Done** (later): `capP` (`Lib/Machines/Prog/CountP.lean`) caps the gate count at `W` after
  `countP`, so the runs are charged `≤ W + 1023` gate rounds whatever the gate list's bound;
  `time_wfB2_conf` now holds for gate lists of up to `2^64` bits: **`≤ 2^549` steps**
  (run of `f̂` `≤ 2^545`, predicate `≤ 2^480`, `simKeyP` `≤ 2^548`).
  `KeyPTime2.lean`: **`time_keyP2`**, `time_keyP` with the block bounded at the per-tape bounds of
  its call `io2 Lsd (frontL c.L W) 0` (`ub_winB2`, `ub_branchB2`); **`time_keyP_wfB2`**
  (`WfB2Conf.lean`): the key component with `wfB2` at the sizes of `confP`, block time `2^549`.
* Remaining hypotheses of the instance at `confP`: `treeHeight Np kp ≤ 64`, the stream offsets
  and `|sdEnc|` `≤ 2^234`, `frontL c.L 512 ≤ 2^64`; the windows' `parse C ≠ []`,
  `|parse C| + 10 ≤ 512`, `BndG 512` for `wfSpec_wfB2`; the size bound.
* **Done** (`Prog/WfB2Size.lean`): **`size_wfB2_conf`**, `XProg.size (wfB2 hk c 512) ≤ 2^25` at
  the sizes of `confP` (`size_wfB2`: a part depending on `W` only, `fixSz 512 ≤ 10·2^20` by
  kernel check — the run of `f̂` ≈ 97 gates × `|simStepP ginvTopP|` ≈ 2^23.1 — plus five
  template programs, `≤ 136 · (241 · 195 + 36)` states by `size_natP_lt`,
  `Lib/Machines/Prog/NatPSize.lean`). Total ≈ 2^24.
* **Done** (`Prog/WfB2Inst.lean`): every hypothesis at `confP` discharged.
  `gates_facts`/`hP_win`: a window predicate parses to `predGates` of a compiled `BExp`, nonempty,
  `≤ 375` gates, wire indices `≤ 385` (`Lib/Machines/GatesSLPBound.lean`: compiled programs are
  closed, `bnd_predGates`); `treeHeight_conf` (`= 60`); `offs_conf` (closed forms of the offsets
  and of `|sdEnc|`, `≤ 2^234`); `dateBound_le` (`≤ 2^20`) and `frontL_le` (`≤ 2^64`, through
  `lookCount_le`, `Lib/Machines/Prog/Lookup.lean`; stated for a variable `n ≤ 2^20` first,
  since the kernel would otherwise evaluate `dateBound`).
  **`wfB2_confP`**: `WfSpec hkp confP (wfB2 hkp confP 512) 512`, at most `2^25` states, at most
  **`2^549` steps** (≤ the target `2^556`) with every tape below `2^240`, on SimData words of at
  most `2^234` bits and gate lists of at most `2^64` bits. **`time_keyP_confP`**: the key
  component with this block at `confP`; it only assumes the SimData program's time and output
  length (`≤ 2^234`, e.g. `fixLen (sdEnc hkp confP)`, `offs_conf`). Axioms: `propext`,
  `Classical.choice`, `Quot.sound`.
* **Open, outside the `W_f` block**: the rest of `time_keyP_confP`'s bound still uses uniform
  bounds, in particular `keyTryT M = 23 (M+1)^2 + tbC · (2M+1)^tbD` for the key try at
  `M ≈ 2^240` (plan item 8); the per-query total `≲ 2^556` needs a per-tape bound of the key try
  in the same style (`absC`/`Ph`).

### Status (2026-11-23, night): the `W_f` numerics at `N = 2^34`, `d = 2^61`

* `WfB2Conf.lean` re-established at the merged `confP` (`Np = 2^34`, `dp = 2^61`, `Kp = 2^25`):
  `Nc = 2^34`, `dc = 2^61`, **`Lb = 2^240`** (the SimData components' output bound
  `2^180 + sizeSd3/5 ≤ 2^240`; the stream offsets and `|sdEnc|` are `≤ 2^238`, `offs_conf`),
  `M31c = 2^160` (templates `≤ 2^146`), **`Mall = 2^250`** (tapes `≤ 2^242`), `Msk = 2^233`
  (frame of `simKeyP` `≤ 2^232`). The certificate lists `L1c`, `L1Gc` are the values of `absC` on
  `L0c`, `L0Gc`, obtained by kernel reduction of the same terms (`Lean.Kernel.whnf` on an
  encoding of the result as one numeral; the interpreter's `#eval` is far slower), and checked by
  `chk_r1`/`chk_r2` (`decide +kernel`, the module ≈ 3 min).
* Steps: run of `f̂` `≤ 2^551` (≈ `2^550.65`), predicate's run `≤ 2^485` (≈ `2^484.2`),
  `simKeyP` `≤ 2^555` (`(2·2^233 + 3) · 2^320.6`): **`time_wfB2_conf ≤ 2^556`**.
  `size_wfB2_conf`: still `≤ 2^25` (templates below `2^251`).
* **`wfB2_confP`**: `WfSpec hkp confP (wfB2 hkp confP 512) 512`, at most `2^25` states, and for
  `Lsd ≤ 2^240`, `Lg ≤ 2^64`: at most **`2^556` steps**, every tape at most **`2^250`** bits.
  **`time_keyP_confP`**: the key component with block time `2^556` and tape bound `2^250`, for a
  SimData output of at most `2^240` bits.
