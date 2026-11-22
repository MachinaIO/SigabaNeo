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
   **Status (steps 7, 8 done except the key component)**, at `confP`, query/state inputs ≤ 2^180:
   setup3D/5D/ID ≤ 2^403 steps, outputs ≤ 2^182, ≤ 2^25 states (`SetupL`); pub3/pubI/pub5 ≤ 2^419,
   chal3 ≤ 2^430, chal5 ≤ 2^440, chalIL2 ≤ 2^380 (outputs ≤ 2^182), all ≤ 2^25 states, sd3/sdI/sd5
   ≤ 2^25 states (`CompCost`); decoders ≤ 2^350 steps, ≤ 2^16 states, 14 tapes (`DecodeCost`);
   auth (`authL`, a search over valid date pairs with a gate generator) ≤ 2^275 steps for queries
   ≤ 2^240 bits, output 1 bit, ≤ 2^19 states (`AuthL`, certified by the numeric interpreter
   `NB.check`, `SigabaNeo.Lib.Machines.Prog.NumBound`).
Larger N is a fallback lever (time ≈ N^5, H ≈ linear in N).
