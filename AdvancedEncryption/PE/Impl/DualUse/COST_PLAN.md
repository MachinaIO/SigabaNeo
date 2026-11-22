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

## Status of the assembly (branch `t3/ah-assembly`, 2026-11-23)
`AHConcrete.lean`: the three reductions at `confP` assembled (`StepComps`, `step3/step5/stepI`,
`StepComps.comps/bounds/bundle`); each constant `≤ 2^2383` (`const_le`, through
`compConst_le_two_pow` with `r = 270, t = 2376, p = 14, s = 240, τ = 2371, ℓ = 252, lc = 20,
k' = 298, g = 11`), so `64 · 2^256 · C ≤ 2^2645` and **`kb = 2645 ≤ 2650`** suffices
(`attributeHiding_conf`; from the registry, `attributeHiding_conf_registry`,
`attributeHiding_implP_registry`). Per-query time: setup `2^403`, pub `2^425`, auth `2^275`,
chal `2^440`, key `2^T + 2^2045` (the uniform key-try bound `20000 (2M+1)^8` at `M ≈ 2^251`,
`KeyCostP`).
* **Remaining hypothesis: the `W_f` block**, `WfSpec hkp confP wfB Wg` and `WfCost wfB Wg T`
  (time `≤ 2^T`, tapes `≤ 2^250`, `≤ 2^200` states on `wfIn (2^240) (frontL confP.L Wg)`), with
  `T ≤ 2370`, `384 ≤ Wg ≤ 2^200`. `wfB2_confP` (WS-T1) was certified at `N = 2^33, d = 2^60` and
  does not build against `confP` at `N = 2^34`; WS-T1b re-certifies it (with `Lb = 2^240`).
* Fixed on the way: `SimValid` now includes the binarity of `Rᵢ`, `W_j` (`SimCovered` was false
  as stated; `simCovered_conf` from `goodTrap_sim`); the public-key components bounded on the
  setup's output bound `2^182` (`time_pub3L_conf'`, …); `dateBound ≤ 2^20` and the front end's
  table (`Gates/WindowBound.lean`); `time_keyPT` (per-tape `W_f` bound, `KeyPTimeT.lean`).
