# PE from lookup tables over exponents (ePrint 2026/2539 §5), for the 128-bit BP universe

Goal: a second `Submission` for `PE.BranchingProgram.primitive` (the same universe as
`PE/Impl/RingBTVW/Submission.lean`: 16 symbols of 8 bits, 32-bit states, `T = 16`), implementing
the scheme of §5 of Suegami, *Implementing Predicate Encryption for Branching Programs* (ePrint
2026/2539), with

* `Correct`, `Expressive` without hypotheses,
* `AttributeHiding` from **circular Ring-LWE with automorphism keys only** (Assumption 1 of the
  paper), registered as a new assumption whose security function is `RingLWE.H` of the underlying
  Ring-LWE parameters,
* an explicit cost `N` (`PE.cost`), to compare with the dual-use submission's `2^818`.

Paper text: `/tmp/claude-1000/-home-sora--t3-worktrees-Sigaba-Neo-t3-a239ea29-31b0ba76dba98eb8/2a7cf063-0bca-4a2c-aa10-30404a9dee87/scratchpad/p2539.txt`
(PDF: `/home/sora/.t3/userdata/attachments/c798bca8-9f71-4d41-8efb-f13098955073-0bf20d2a-73db-4838-9684-f70e636f1411-pdf.pdf`).
Sections: 2 (overview), 3.2 (σ_k, H, K, J; Assumption 1), 4 (Add/SMul/Mul/Aut, Lemma 7 sieve,
Lemma 8 LUT, Lemma 9 BP evaluation), 5.1 (scheme), 5.2 (correctness), Appendix A (proof:
simulation forms, Lemma 10, Corollary 1, Lemma 11, hybrids H0–H5).

Rules: everything fully proved, no `sorry`, no `native_decide`, axioms `[propext,
Classical.choice, Quot.sound]` only. Generic lattice math goes in `SigabaNeoStd/Lattices`,
generic machine code in `SigabaNeoStd/Machines`, the scheme in `AdvancedEncryption/PE/Impl/ExpLUT`.
Mirror the structure and reuse the infrastructure of `PE/Impl/RingBTVW` (read its `DESIGN.md`,
`COST_PLAN.md`, `AdvancedEncryption/BP_PLAN.md`) wherever possible.

## Design decisions (deviations from the paper, all as in `RingBTVW`)

1. **Odd modulus `q = 2^K − 1`.** The sieve divides by `W` (`α_{k,L} = W⁻¹ Σ_j …`), so `q` must be
   odd; the dual-use `q = 2^K` cannot work (the scaled gadget `W^T G` is no trapdoor). With
   `q = 2^K − 1` a residue is a `K`-bit word read modulo `q` (two words for `0`), negation is
   bitwise NOT, addition is addition with end-around carry, multiplication by `2^i` is a rotation and
   `W⁻¹ = 2^{K−40}`. Binary gadget `g = (1, 2, …, 2^{K−1})`, `τ = K`; `G⁻¹` = the bits of any `K`-bit
   representative. `⌊q/2⌉ = 2^{K−1}`. Nothing needs primality: the LHL used is
   `SigabaNeo.Lattices.isTwoUniversal_binaryHash` (any finite commutative ring).
2. **Binary / box laws instead of Gaussians.** Programming matrices `R`, `Z_t` and the TrapGen
   trapdoor `T` are binary (entries `0/1 ∈ R`); errors are the centered-binomial/box laws of
   `RingBTVW`; noise flooding by boxes (`closeTo_floodLaw_add`); keys by one try of box rejection
   (`SigabaNeo.Lattices.boxSample`), whose law does not depend on the trapdoor (`boxSample_eq`),
   so hybrid H3 is exact and the final hybrids need no trapdoor at all.
3. **Statistical TrapGen** `B⁽¹⁾ = [Ā | g − Ā T]` with uniform `Ā ∈ R^{1×m̄}` and binary `T`.
   The programming matrices are supported on the `Ā` columns only, so the simulation matrices
   `R̂` never touch the gadget columns; the box sampler's gadget coordinates `z` are the last `τ`
   columns of every block `β_i = δ_i ⊗ σ_i(B⁽¹⁾)`, for both the real trapdoor
   (`blockdiag σ_i(T)`) and the simulated one (Lemma 11's `X`, then `T_sim z = X·G⁻¹(…)`).
4. **Binary basis** `K = {g^{2^j}}`, `b = log₂ W = 40`, `W = w|Σ| = 2^32 · 2^8 = 2^40`, hence
   ring degree `n = 2^41` (`W < n`). (The radix optimization of §6.1 is not used.)
5. **Simulator**: uniform words of the ciphertext's shape (the components that H5 makes uniform;
   `C_k` is recomputed from the uniform helpers by the evaluator anyway).

## Hybrids (selective `x*`, adaptive keys, as in Appendix A)

* H0 = real. H1: programming (`a_t = B⁽¹⁾Z_t + X^{w x*_t} G⁽¹⁾`, `A_0 = BR_0 + G`,
  `A^in = BR + dG`, `A^aut_k = σ_k(B)R + dG`; the challenger draws `s̄` and the ciphertext coins
  first) — LHL with seed the `Ā` columns. H2: encodings from `b` — flooding. H3: keys by
  `boxSample` with the trapdoor of Lemma 11 — exact. H3′: `B⁽¹⁾` uniform — LHL on `(Ā, Ā T)`.
  H4: `b`, `h_k`, `c_m` uniform — **circular Ring-LWE** (the only computational step; its reduction
  must be an explicit machine with a cost bound, as `RingBTVW/ReductionMachine` + `Prog/KeyCostV`).
  H5: programmed pairs, `C^in_t`, `c_m` uniform — LHL with the 3-row seed `(B; b)`; keys are the
  box law of `M_F`, a function of `mpk`. H6: `B⁽¹⁾` from TrapGen again — LHL; H6 is the ideal
  experiment with the uniform simulator.

## Concrete parameters (to be fixed by the noise certificates)

`n = 2^41`, `q = 2^K − 1` with `K = 2^17` expected (log₂ q ≈ 2·T·(b+2)·log₂(2τn) + key-box bits
≈ 85 000), `m̄ ≈ 3nK + 2·(stat. budget)`, flooding and key boxes as needed. Estimated cost: KeyGen
and Dec ≈ `W · b · T` automorphisms of `8τ³` ring multiplications — far below `2^818`.

### Worst-case budget (binary `R`, `Z`, so `R* = Z* = 1`; `B_χ = 16`)

All logs base 2, `τ = K = 2^17`, `D = 2τn = 2^59`, `mB ≈ 3nK = 2^59.6`, `N_key ≈ W·mB = 2^99.6`.

| Quantity | Formula | log₂ |
|---|---|---|
| flooding width `σ_fl` | `2^200 · mB n B_χ` | ≈ 305 |
| `γ` | `W D^{b+2}` | 2518 |
| `B_F` (Lemma 9) | `γ^T (σ_fl + Δ)` | ≈ 43 129 |
| `B_R̂` (Cor. 1) | `γ^T (1 + Δ_sim)` | ≈ 42 824 |
| `‖X‖∞` (Lemma 11) | `D^b (B_R̂ + 2)` | ≈ 45 184 |
| `‖T_sim z‖∞` | `Wτ n ‖X‖∞` | ≈ 45 282 |
| small key box | `2^{130} · N_key n · ‖T_sim z‖∞` (abort ≤ 2^-128) | ≈ 45 553 |
| decryption noise | `N_key n · key · B_F` | ≈ 88 824 < K − 2 |

So `K = 2^17` suffices with margin; `m̄ = 3nK + 2·(stat. bits + log #programmed columns) ≈ 3·2^58 + 400`.

## Work packages

| Id | Package | Depends on |
|---|---|---|
| A | `Lib/Lattices/Automorphism`: `σ_k` on `Negacyclic (ZMod q) n`, composition, fixes constants, coefficient permutation up to sign (norms), `H`, binary basis, Lemma 7, Lemma 8 identities | – |
| B | `Lib/Lattices/CircularRingLWE.lean` (Assumption 1 as a `SigabaNeo.Assumption`, `H := RingLWE.H` of the base parameters) + certified strength at the concrete parameters (as `RingBTVW/Params/Strength`) | – |
| C | `ExpLUT/Ops`, `ExpLUT/Eval`, `ExpLUT/Scheme`, `ExpLUT/Correctness`: the operations of §4 over an abstract ring with automorphisms, exact identities and noise bounds, Lemma 9, the scheme of §5.1 with the box/binary laws, Theorem 1 | A's interface (abstract) |
| D | `ExpLUT/SimForm`, `ExpLUT/SimTrap`, `ExpLUT/Hybrid*`, `ExpLUT/Security`: Lemma 10, Corollary 1, Lemma 11, the hybrids, the reduction to circular Ring-LWE (math level) | C |
| E | Machine arithmetic modulo `2^K − 1` on ring words (add, neg, sub, mul, rotations, `σ_k`, gadget digits), as `Lib/Lattices/ProgAlgo/RingProgs` | – |
| F | Machines `Setup`, `Enc`, `KeyGen`, `Dec`, `Eval` realizing C's laws exactly; time and descLen bounds | C, E |
| G | Reduction machine of H4 with a cost bound; `HardAt` assembly (`AHConcrete` analogue) | D, F |
| X (optional, low priority) | Exact (`=`) step lemmas for the data-independent parts of the machine library (`Lib/Machines`, `ProgAlgo`), next to the existing `≤` bounds; the costs stay tight upper bounds | – |
| H | `ExpLUT/Submission.lean`: registry (circular Ring-LWE), `spec_submission`, `valid_submission`, cost comparison write-up | all |

## Status

(updated as packages land)

### Continuation: executable complete helper phase (2026-11-24)

`Prog/EncHelpers` defines **`helperRoundP D t`** and **`helperPairsP D j n`** on 69
tapes. Each round installs its forward/inverse exponent templates, executes the
existing helper-pair code, and clears both temporary template tapes. The complete
program is a concrete unrolled sequence, not a supplied abstract core. It is proved
well formed and coin free. `run_helperPairsP` proves the entire stream-consuming
execution; **`run_helperPairsP_ciphertext`** identifies its output with `ct.h` in
the scheme's `Jh` enumeration (for `0 < D.b`, as in the concrete dimensions).

The literal templates are charged: **`size_helperPairsP`** proves exact description
size `36 + n*(hBlkP.size + 144 + 60*2^D.b)` when `j+n ≤ D.b`. The two unary
exponent words in each round together have `2^D.b` bits. This is a description-size
result, not a runtime bound. The program preserves the secret, fixed templates,
and all unrelated tapes, and restores the temporary template tapes to blank.

Enc still needs the analogous concrete outer automorphism program, the `b` phase,
initialization and phase placement, the final machine/specification and clock.
Other KeyGen/Dec/reduction/Submission obligations remain open.

Validation: aggregate build passed (9610 jobs; `/tmp/explut-helpers-program-build.log`).
Seven audited execution/codec/well-formedness/size theorems use only subsets of the
standard three axioms (`/tmp/explut-helpers-program-axioms.log`). No new-module
warnings or proof placeholders; `git diff --check` passed.

### Continuation: complete composed encryption tail (2026-11-24)

`Prog/EncTailCodec` defines the explicit `TailInput` store invariant and proves
**`run_tailP_ciphertext`** for the actual four-phase `tailP`. The proof transports
scratch/template invariants and the remaining input fields through `cinbotP`, `cinP`,
`c0P`, and `cmP`; the bottom-row output length is proved preserved before the digit
phase. `tailOutput_eq` combines the four shift-register operations into the exact
append/drop of `tailWord`, and `ctEnc_prefix_tail` splits the scheme codec there.
**`run_tailP_serialized`** proves that a prefix-filled output register is completed
to the entire `ctEnc` word by the actual tail program.

The prefix-filled premise is still to be established by the preceding `b`, helper,
and automorphism loops and their initialization. This is a completed tail stage,
not a completed Enc machine or `EncSpec`. The full machine/clock and other
KeyGen/Dec/reduction/Submission obligations remain open.

Validation: aggregate build passed (9608 jobs; `/tmp/explut-complete-tail-build.log`).
Five audited composition/serialization theorems use only the standard three axioms
(`/tmp/explut-complete-tail-axioms.log`). No new-module warnings or proof placeholders;
`git diff --check` passed.

### Continuation: actual ciphertext fields at sixteen positions (2026-11-24)

`Prog/EncInputCodec` proves `posBlocks_codec` and `attributeBlocks_codec`, matching
the natural-indexed loops with `Pos` and `encAttribute w8`. **`run_cinbotP_ciphertext`**
and **`run_cinP_ciphertext`** now consume the scheme's public-key/coin codecs and write
exactly the `cinBot` and `cin` fields of `encrypt`, with all source streams emptied.
`inputDigits_encrypt` identifies the decoded secret in the machine row formula with
`r.s`. **`run_lastRows_ciphertext`** composes the actual `c0P` and `cmP` programs and
proves their output is the ordered `c0`/`cm` ciphertext fields, including both shifts.

The final whole-tail composition, Enc initialization/outer helper and automorphism
loops, full machine and clock, and KeyGen/Dec/reduction/Submission work remain open.

Validation: aggregate build passed (9606 jobs; `/tmp/explut-input-codec-build.log`).
Six audited codec/execution theorems use only the standard three axioms
(`/tmp/explut-input-codec-axioms.log`). No new-module warnings or proof placeholders;
`git diff --check` passed.

### Continuation: complete attribute loops (2026-11-24)

`Prog/EncInputPhase` proves `cbRow_symbol8_append`: the first symbol controls the
monomial and later symbols do not affect it. `assemble_cinMat` proves the actual
shift-register assembly produces the canonical two-row `cinMat` codec. The proofs
use only the first eight rotation template values, matching the actual periodic
template layout; they do not impose an impossible equality on all natural indices.

`ciStep_encoded` and **`run_cinBody_encoded`** close one complete attribute round,
including source consumption and the digit-family output codec. `ciStep_stream` and
**`run_cinP_stream`** cover the entire outer attribute digit loop for arbitrary `n`.
`cbStep_stream` and **`run_cinbotP_stream`** likewise cover all bottom rows. Output
capacity and template invariants are explicit; output shifts are included, not
silently replaced by unbounded appends. These are actual executable loop results.

The remaining Enc work includes specializing natural-indexed position streams to
`Pos`/`encAttribute`, assembling initialization and all phases into the final machine,
and proving its clock. Other KeyGen/Dec/reduction/Submission obligations remain open.

Validation: aggregate build passed (9604 jobs; `/tmp/explut-input-phase-build.log`).
All eight audited attribute-phase theorems use only the standard three axioms
(`/tmp/explut-input-phase-axioms.log`). No new-module warnings or proof placeholders;
`git diff --check` passed.

### Continuation: digit codec and complete automorphism block (2026-11-24)

`Prog/EncDigitCodec` closes the entry/digit enumeration bridge. `entryBlocks_codec`
is the matrix's row-major codec; `digitBlocks_codec` proves the nested loops agree
with `Dig = Fin 2 × Col K × Fin K` in its right-associated product enumeration.
`deSteps_encoded` and **`run_deP_encoded`** now use the scheme's matrix, matrix-family,
and vector-family codecs directly. The output is `digitRows`, with the exact secret
word decoded in the row formula. No stream-order premise remains in these results.

`Prog/EncAutPhase` combines helper recomputation, canonical gadget-ciphertext creation,
and the whole nested digit phase. **`autOut_encoded`** and **`run_autBlkP_encoded`**
prove the complete actual automorphism block consumes two helper matrices/error rows
and one digit-matrix/error family, and writes its digit-family ciphertext codec.
`digitRows_autTW` identifies the actual transformed secret with the scheme automorphism.
The statements are generic in the forward/inverse exponents and retain the explicit
scratch/template and output-capacity conditions. Full Enc initialization, outer loops,
input-attribute phase, final machine and clock, and the other Submission obligations
remain open.

Validation: aggregate build passed (9602 jobs; `/tmp/explut-codec-autphase-build.log`).
The seven audited codec/block theorems use only the standard three axioms
(`/tmp/explut-codec-autphase-axioms.log`); no warnings in the new modules and no
`sorry`, `native_decide`, or new axioms. `git diff --check` passed.

### Continuation: helper, automorphism, and digit phase semantics (2026-11-24)

`Prog/EncHelperMath` proves `hRow_helper` and **`run_hBlkP_scheme`**: the actual
helper-pair program writes the two scheme rows and consumes both matrix/error blocks.
Its `HelperOK` records the fixed templates and blank scratch.

`Prog/EncAutMath` proves canonical iterated automorphisms, both entry loops and
**`run_gcAutP_scheme`**. The actual gadget-ciphertext machine writes the canonical
word of `gcAut`, i.e. `σ(H) - [0; σ(h)]`, consumes both input queues, and preserves
all other store fields. Output capacity assumptions explicitly account for the shift register.

`Prog/EncDigitMath` proves `row_mat_word` for noncanonical secret words (needed for
actual automorphism outputs), `deRow_scheme`, `deIn_stream`, `deOut_scheme`,
`deOut_stream`, and **`run_deP_scheme`**. The complete nested digit machine writes
all rows in entry-then-digit order and consumes all three input streams. The latter
statement uses explicit consecutive block streams and arbitrary `n` entries; it is
not yet the final `caut`/`cin` field codec equality. Connecting those streams to the
scheme's `Dig` enumeration, assembling the full encryption store, and proving the
clock remain necessary. KeyGen, Dec, reduction handlers, Submission, and final cost
comparison are still incomplete.

Validation: aggregate build passed (9598 jobs; `/tmp/explut-helper-aut-digit-build.log`).
The eight audited machine/loop theorems use only `propext`, `Classical.choice`, and
`Quot.sound` (`/tmp/explut-helper-aut-digit-axioms.log`). No new-module warnings,
`sorry`, `native_decide`, or added axioms; `git diff --check` passed.

### Continuation: encryption tail scheme semantics (2026-11-24)

`Prog/EncTailMath` proves `decRM_rbitsW`: the actual conditional rotations multiply by
`X` to the sum of the selected positional exponents. `bitExponent_symbol8` checks the
big-endian eight-bit symbol convention with kernel-checked `decide`; `cbRow_symbol8`
connects the resulting bottom row to `-s*a + X^(w*x)*(s,1)*G + e` under the explicit
rotation-range bound `w*128 ≤ 2*N`. `hRow_c0`, `run_c0P_scheme`, and `run_cmP_scheme`
connect the initial and message rows, including the output tape's shift operation, to
the scheme. These discharge row semantics; the full stream assembly, encryption machine,
clock bounds, KeyGen/Dec completion, reduction handlers, and Submission remain open.

Validation: aggregate build passed (9592 jobs; `/tmp/explut-tail-scheme-build.log`).
The six audited tail-semantic theorems use only `propext`, `Classical.choice`, and
`Quot.sound` (`/tmp/explut-tail-scheme-axioms.log`). `git diff --check` passed.

### Continuation: complete encryption coin sampler and input pipeline (2026-11-24)

`Prog/EncCoins` now defines `encCoinWord`, `encCoinsP`, and proves `encCoinsLaw_word`,
`appendLaw_encCoinsP`, `law_encCoinsP`, and `wf_encCoinsP`. The actual seven-tape sampler draws
the secret and base errors, the four flooding fields, and the message error in the scheme's
field order. The law theorem proves their joint distribution, including independence, equals
the encoded `encCoinsLaw`. Coefficient loops avoid nesting samplers that share counter tapes.

`Prog/EncFront` parses `encodeTuple [pw, mpk, x, μ]`, discards `pw`, and leaves
`mpk ++ x ++ μ` on tape 1 with tape 0 and scratch blank (`run_parse`). `prepare` then samples
the complete coin word on tape 0 (`law_prepare`). `program` runs the supplied MVM core via
`frontIO`; `law_program` gives its exact output distribution and `wf_program` proves its
well-formedness for counter-preserving VM code. `law_program_of_core` connects this pipeline
to `encLawW` **conditional on the explicit core's word-correctness theorem**. That premise,
the actual full encryption core code, and the clock bound are still outstanding; this is not
yet a completed `EncSpec` or an instantiated encryption machine.

Aggregate build passed (9592 jobs): `/tmp/explut-encryption-front-build.log`.

### Continuation: encryption tail and VM input/output (2026-11-24)

`EncTail` now has `run_cmP`, `run_cinBody`, `run_cinP`, and **`run_tailP`**. The latter proves
the complete tail program equals `tailStore`, a pure composition of the bottom-row iteration,
attribute digit-encoding iteration, initial row, and message row. `TailOK.of_agree` and
`tailOK_ciG` carry the template/scratch invariant through composition. These are word-level
execution results; the full `EncSpec` and Enc clock remain open.

`Mersenne/VMIO` adds **`frontIO : XProg 105`**, **`law_frontIO`**, `wf_frontIO`, and
`size_frontIO_le`: two words on tapes 0 and 1 are copied to VM registers 0 and 1; fixed templates
are installed; compiled VM code runs; register 0 is returned on tape 0 and all other tapes are
cleared. This uses literal `putW` templates, with their lengths explicitly charged: if each
template has length at most `B`, size is at most `(compile c).size + 8000 + 6300 * B`.
The reduction and KeyGen callers still need to instantiate this wrapper and prove their clocks.

`Prog/EncTailMath` connects the message mask to `-(half D * msgR D μ)` (`decRM_cmMask`) and
the message row to `sec s ⬝ᵥ d + em + half D * msgR D μ` (`row_cm_message`). Aggregate build
with this bridge passed (9588 jobs; `/tmp/explut-tailmath-build.log`).

Validation: aggregate build passed (9586 jobs); `#print axioms` for `run_tailP`, `run_cinP`,
`run_cmP`, `law_frontIO`, `wf_frontIO`, and `size_frontIO_le` reports only the standard three
axioms. Logs: `/tmp/explut-tail-vmio-build.log`, `/tmp/explut-tail-vmio-axioms.log`.

### Recovery checkpoint (2026-11-24)

Recovered the uncommitted `EncTail`, `VMUtil`, and `Prog/KeyCoins` from the earlier F2b/F3c
worktrees into the aggregator. `KeyCoins` needed repairs to equivalence simplification,
enumeration indexing, the probability namespace, and the finite-set image proof.

* `EncTail.run_cinbotP`: the bottom-row loop implements `cbStep` iteration.
  Added `run_c0P` for the initial ciphertext row and `wf_tailP` for the tail program.
  The full `run_tailP` theorem is still absent; the earlier draft's reference to it was removed.
* `VMUtil`: bit constants, unary templates, stream extraction, repeated appends, and canonical
  words of constants, with their execution lemmas.
* `Prog/KeyCoins.map_uniformList_coinDec_kbOf`: decoding the fair-coin queue gives exactly the
  uniform law of the big key box. This is a sampling-law component, not the complete KeyGen machine.

The older G2b `VMFront` draft failed compilation and was not integrated. The existing tracked
`VMFront` template builder is retained. The complete Enc/KeyGen/Dec machines, reduction handlers
and their bounds, `Submission`, and final cost comparison remain outstanding.

Validation: `lake build PE.Impl.ExpLUT` passed (9584 jobs). `#print axioms` for the recovered
execution/sampling results and the added `run_c0P`/`wf_tailP` reports only subsets of
`[propext, Classical.choice, Quot.sound]`; no `sorry`, `native_decide`, or axiom declarations occur
in these three recovered files. Logs: `/tmp/explut-recovery-build.log` and
`/tmp/explut-recovery-axioms.log`. Changes at this checkpoint are uncommitted and unpushed.

### Package C (algebra of §4, scheme and correctness of §5) — done

Files (`PE.Impl.ExpLUT.*`, aggregator `PE.Impl.ExpLUT`): `Basic`, `Ops`, `LUT`, `Eval`, `Noise`,
`Canonical`, `NegacyclicNorm`, `Scheme`, `Correctness`, `CorrectBound`, `KeyGen`, `Laws`. Main
results: `encodes_mul` (eq. (1)), `encodes_aut` (eq. (2)), `encodes_rounds`/`encodes_lut_of_spec`
(Lemma 8), `encodes_eval` (Lemma 9, exact), `rowBnd_evalErr` + `stepBound_iterate_le` (Lemma 9's
`γ^T(B₀ + Δ)`), `decRow_sub_decConst` (eq. (4)), `decryptRaw_encrypt` (Theorem 1 exactly),
`decrypt_correct_of_bounds`/`decrypt_correct_of_mem_support`/`decrypt_fail_le` (Theorem 1),
`realTrap_good`, `valid_of_mem_support`, `keyLaw_eq_of_good`, `keyLaw_eq_ideal` (keys).
Axioms: `[propext, Classical.choice, Quot.sound]`.

Design points fixed by C (deviations from the paper's presentation, not from its scheme):

1. **`H` in exponent form.** `Setting.idx j` is the index of `g^j`; rows "indexed by `H`" are the
   exponents `j < W` (`Fin W`), `δ₁` is the row of exponent `0` (`Setting.row0`), the row `i·k` is
   `(i + je k) mod W` (`HelperMap.mulRow`). The group law is the field `idx_add`; for the canonical
   choice `idx j = g^j` it follows from `orderOf_gGen` (`canonSetting`), which needs **`2W ∣ n`**
   (A's hypothesis; `W < n`, `W ∣ n` is not enough). Lemma 8 for it is `lemma8_canon`.
2. **Helpers `J` abstract** (`HelperMap`: exponent `je`, `fwd t`, `inv t` with `je = 2^t`,
   `W − 2^t`), so `J` can be the set `K ∪ K⁻¹` (`inv (b−1) = fwd (b−1)`) or `Fin b × Bool`.
3. **Encodings with general payload rows** (`Encodes S s A x e c : c = sA − xG + e`); `Mul` selects
   the column `(r, i)` directly instead of multiplying by `G⁻¹(2^i 1_rᵀ)` (identical).
4. **Box sampler coordinates confirmed**: `z` = the last `τ` columns of every block `β_i`
   (`ZIdx = Fin W × Fin τ`), the short part `x` = everything else (`PIdx`), key = `assemble x z`,
   public map `pubShort x = M_F (x, 0)`, gadget `gadZ = I_W ⊗ g`, `GoodTrap T :
   pubShort (T z) + gadZ z = M_F (0, z)`. The real trapdoor is `z ↦ −(σ_i(T) z_i)_i` on the `Ā`
   columns (sign: `σ_i(B⁽¹⁾) = [σ_i(Ā) | g − σ_i(Ā)σ_i(T)]`). **For package D**: a gadget trapdoor
   `X` of Lemma 11 (`M_F X = I_W ⊗ g`) with zero rows on the `z` coordinates (true when `R̂_F`
   avoids the gadget columns of the `β_i`, as planned) gives the good trapdoor
   `T_sim z = X_P · gadDec (M_F (0, z) − gadZ z)`; then `keyLaw_eq_of_good` (or `keyLaw_eq_ideal`)
   with the same `Big`, `Small`, `dec`.
5. **Messages** `m : R` with `c_m = s dᵀ + e_m + half · m` and an abstract `decode`; Theorem 1 needs
   `decode (half · m + e) = m` for `‖e‖ ≤ corrBound` (for one bit: `decodeBit_encodeBit_add`).
6. **Noise** at an abstract norm (`NormSpec`; `cnormSpec` for `ℤ_q[X]/(X^{2^e}+1)` with binary
   digits), `D = 2τn`; closed forms need `D ≥ 2`. `B_F = (stepBound S B_fl B_χ B_fl)^[T] B_fl
   ≤ γ^T (B_fl + Δ)`, `corrBound = B_χ + |KCol| n max(B_χ, B_F) K` with `K` bounding all key
   entries (small box and decompositions).
7. **Coin laws** (`Laws`): per-entry i.i.d. laws `χT` (trapdoor), `χs`, `χ` (base: `e_b`, `e_k`,
   `e_m`), `χfl` (flooding: `e₀`, `e_t`, digit encodings), public matrices uniform.

Still open for later packages: the concrete box parameters (`Big`, `Small`, coverage of the real
trapdoor shift `rowBnd_realTrap`: `τ n B_T`), the concrete noise certificate, the bridge from the
universe's programs to `BP`.

### Package D (proof of Theorem 2, math level) — done

Files (`PE.Impl.ExpLUT.*`, in the aggregator): `SimForm`, `SimEval`, `SimBound`, `SimTrap`,
`SimKeys`, `HybLaws`, `HybView`, `Hybrid0`, `Hybrid12`, `Hybrid3`, `Reduction`, `Hybrid5`,
`Hybrid5U`, `Hybrid6`, `GameChain`. Axioms of the main results: `[propext, Classical.choice,
Quot.sound]`.

* **Simulation forms** (Definition 3, Lemma 10): `SimForm M Ab H1 i i' A μ R̂ :
  δ_iᵀ ⊗ A⁽¹⁾ − δ_{i'}ᵀ ⊗ μ G⁽¹⁾ = L R̂`, with `L = simL` on the **short** columns `LCol` of `M_F`
  (the `Ā` columns of the `β_i` and the `η_{i,k}`); explicit output matrices `simMul`, `simPerm`,
  `simAut` (`simForm_add/smul/mul/σ/maskSwitch/aut`). Rounds, tables, evaluation:
  `simRounds`, `simLut`, `simEval`; **Corollary 1** `corollary1`: for a `Programmed` public key,
  `SimForm … row0 row0 (keyPK M mpk F) (F.eval x) (simKey M mpk F ct x P)`. Bound
  (`matBnd_simKey`): `‖R̂_F‖ ≤ (stepBound S R* 1 Z*)^[T] R*` (C's Lemma 9 recurrence with
  `B_χ = 1`), `≤ γ^T (R* + Δ)` (`matBnd_simKey_closed`); binary programming gives `R* = Z* = 1`
  when `‖1‖ ≤ 1` (`progBnd_progOf`).
* **Lemma 11** (`SimTrap`): `vRounds` (the `V_i`), `simX : Matrix PIdx ZIdx` (rows on the short
  coordinates only, i.e. zero rows on `ZIdx` by construction), `pubShort_simX : M_F X = I_W ⊗ g`,
  `simTrap M mpk F R̂ z = X · gadDec (M_F (0,z) − gadZ z)`, `simTrap_good`, `keyLaw_real_eq_sim`,
  `keyLaw_sim_eq_ideal`; bounds `rowBnd_simTrap : ‖T_sim z‖ ≤ W τ n (D·+1)^[b] max(B_R̂, 1)` and
  `vBound_iterate_le : (D·+1)^[b] E + 1 ≤ D^b (E + 1)`.
* **Hybrids** (the challenge for `0`, the message as a shift of `c_m`; keys by `idealKeyLaw`, a
  function of `mpk`): `hybrid01_close` (H0 = C's `setupLaw bitLaw`/`encLaw` ≈ H1 programming,
  `delta1 = |PrI| √(|R|² 2^{−m̄})/2`), `hybrid2_close` (H2, flooding hypothesis `hflood` on
  `floodLaw` under `floodShift`), `hybrid23_close` (H3′: `B⁽¹⁾` uniform, `deltaT = τ √(|R|² 2^{−m̄})/2`),
  `reduction_real`/`reduction_unif` (H3′ = `circReal.bind red`, `circUnif.bind red` = H4),
  `hyb4_eq_L`, `hybrid45_close` (H5, 3-row seed, `delta5 = |PrI| √(|R|³ 2^{−m̄})/2`),
  `hyb5_eq_final` (H5 = uniform `mpk` × uniform ciphertext), `hybrid56_close` (H6: TrapGen again,
  `deltaT`), `idealView_eq` (H6 = `Setup`'s `mpk` × `ctU`), `ctU_shift`.
* **Circular Ring-LWE** (`Reduction`): `CircInst` (plain samples `(aB, vB)` over `BCol`, `(ad, vd)`,
  `(aH k (1,i), vH k (1,i))`; circular samples `(aH k (0,·), vH k (0,·))` with
  `vH k c = s̄ aH k c − σ_{g^{je k}}(s̄) G⁽¹⁾_c + e`), `circReal M χs χ`, `circUnif`; reduction `red`.
  Bridge to `SigabaNeo.Lattices.CircularRingLWE` (package B): a reindexing, still to do.
* **Chain** (`GameChain.chain`): for every program and continuation, real vs ideal within
  `|Attr| (delta1 + ε_fl + deltaT) + δ₄ + |Attr| (delta5 + deltaT)`, `δ₄` the advantage of the
  experiment-as-distinguisher on `circReal`/`circUnif`. Keys: `keyGenLaw_eq_ideal` (real keys =
  ideal, on `Setup`'s support), `redKeyLaw_eq_ideal` (the reduction's `T_sim` keys = ideal for
  `F(x) = 1`, `F.w = w`).

Open for later packages: `hflood` at the concrete parameters (`iidLaw χfl = floodLaw` and
`closeTo_floodLaw_add`), the box coverage of `realTrap` and of `simTrap` (`rowBnd_simTrap` +
`matBnd_simKey`), `Lemma8 S` (canonical), the game-level bridges (real experiment with C's
`keyGenLaw`/`encLaw` = `gameV` with `hyb0`; ideal experiment with the simulator machine = `gameV`
with `idealView`; the reduction's experiment with `redKeyLaw` agrees with `KGi` until `bad`), the
reduction as a machine (package G), the bridge of `circReal`/`circUnif` to package B's laws.

* **B done** (`t3/explut-b`): `SigabaNeoStd/Lattices/CircularRingLWE.lean` (`CircularRingLWE.decision`,
  `H p = RingLWE.H p.base`; `decision_problem_nil`: at `J = []` it is decision Ring-LWE) and
  `Estimator/Bound/CbdQ.lean` (CBD(16) bound at any `q ≥ 2^1024` given `log₂ q`, every sample count
  in a range). `ExpLUT/Params/Strength.lean`: at `q = 2^(2^16) − 1`, CBD(16), every `1 ≤ m ≤ 2^50`
  and every `J`, `τ`: `1155 ≤ H` at `N = 2^24` (`circularRingLWE_H_N24`), `495 ≤ H` at `N = 2^23`
  (`circularRingLWE_H_N23`); both are the largest targets the block-size checks allow.
* **E** (branch `t3/explut-e`): `Lib/Lattices/Algo/NegaG` (Horner in `X⁻¹` and `σ_k` by rotations
  over any commutative ring), `Lib/Lattices/Algo/MersenneWords` (`decM`, `decRM`, one's-complement
  words, gadget digits), `Lib/Lattices/ProgAlgo/Mersenne/{Residue,Ring,Mul,Aut,Bounds}`: programs
  `addMP subMP notP rotJP mulMB addRMP subRMP rnbK rhoJP scRMP rotBP mulRMP autMP` with `run_*`
  lemmas, decodings into `ℤ_{2^K−1}[X]/(X^N+1)` and per-tape time bounds (`MersenneT.boundsT_*`,
  `frameT_*`; ring product `22 N² K²` sweeps, `σ_k` `14 N K k` sweeps). Gadget digits: the existing
  `digitRWP`/`ginvP` with `decRM_digitRW`, `sum_pow_digitRW`.

### Package P (concrete parameters and concrete correctness) — done

Files: `Lib/Lattices/RingBoxes.lean` (boxes of families of ring elements: `famBig`, `famBall`,
`famAbort_le`, and the same with the boxes given by equations), `ExpLUT/Params/Conf.lean`,
`ExpLUT/Params/Noise.lean`, `ExpLUT/Params/Correct.lean`, `ExpLUT/BPBridge.lean`.

* **Configuration** (`Params/Conf`): `Rc = Negacyclic (ZMod qc) (2^24)`, `qc = 2^Kc − 1`,
  `Kc = 2^16` (opaque); `confS = canonSetting confE rfl h2c (binaryDigits (2^24) qc Kc hτc) …`
  with `confE = expRingOf (2^24) 22 (2^(Kc−22)) …` (`= expRingMersenne`, `confE_eq_mersenne`),
  `τ = Kc`, `W = 2^22`, `b = 22`, `D = 2τn ≤ 2^41`; `confN = cnormSpec …` (`confN_nrm`: `cnorm`).
  `helperJ : HelperMap confS (Fin 22 ⊕ Fin 21)` (`K ∪ K⁻¹`, `|J| = 43`). `Wbc = Fin mbar`,
  **`mbar = 3·(2^24·Kc) + 2·(140 + 64)`** (`mbar_lhl`: `|R|³ ≤ 2^{3nK}`; fewer than `2^57`
  programmed columns, `lhlCols_le`; per column `½√(|R|³/2^m̄) ≤ 2^{−205}`).
  Laws: `χT` (constants `0/1`, uniform), `χc = ringLaw cbdCoef` (CBD(16), `B_χ = 16`) for `χs` and
  `χ`, `χfl` (coefficients uniform below `2^eFl`, `eFl = 400`, `B_fl = 2^eFl`).
* **Key boxes**: `Pc = PIdx Wbc Jc confS.τ confS.E.W` (`|Pc| n ≤ 2^89`); `Big` (`Bk = 18750` bits
  per coefficient), `Small` (radius `2^{Bk−1} − 1 − coverBound`), `Inner` (radius
  `2^{Bk−1} − 1 − 2 coverBound`), all opaque (`irreducible_def`); `decc = gadDec`.
  **`coverBound = 2^eSh`, `eSh = 18500`**: every trapdoor `T` with
  `∀ y p, cnorm (T (decc y) p) ≤ coverBound` is covered (`covered_of_shift`) and gives abort
  probability `≤ 2^{−130}` (`abort_le_of_shift`). Real trapdoor: shift `≤ τn = 2^40`
  (`realShift_le`, `realTrap_covered`). **For package D**: Lemma 11's trapdoor shifts by at most
  `simShift B_R̂ = W τ n D^b (B_R̂ + 2)`, and `simShift_le : B ≤ 2^eRhat → simShift B ≤ coverBound`
  (`eRhat = 17400`); with `R* = Z* = 1` Lemma 9's recurrence gives `B_R̂ ≤ 2^17122`
  (`rhatBound_le`, `simShift_rhat_le`). So `keyLaw_eq_ideal`/`keyLaw_eq_of_good` apply with
  `Big Small hBig decc` for both trapdoors.
* **Noise** (`Params/Noise`): generic exponent chain (`gammaB_le_pow`, `deltaB_le_pow`,
  `stepBound_iterate_le_pow`, monotone in `T`); `evalBound_le : B_F ≤ 2^{17122+eFl}` for `T ≤ 16`;
  `corrBound_le : corrBound confS Wbc Jc T 16 2^eFl 2^{Bk−1} ≤ 16 + 2^36360`,
  `four_corrBound_lt : 4·corrBound + 2 < q`, `decode_ok` (messages `half * msgR M`,
  `half = ⌊q/2⌋`, `decodeBit`). Flooding budget `flood_budget`: `2^81` coefficients, shifts
  `≤ 2^70`, total `≤ 2^{eFl − 249}`.
* **Correctness** (`Params/Correct`): `correctExp F x M` (Setup, KeyGen, Enc, Dec at `confS`);
  `correct_fail_le : F.WF confS.E.W → F.T ≤ 16 → (∀ t, x t < F.nsym) → F.eval x = 0 →
  correctExp F x M false ≤ (2^128)⁻¹` (`correct_fail_le_130`: `2^{−130}`), `correct_ge`.
* **Bridge** (`BPBridge`): `toBP : Program w8 → BP (Fin w8.len)` (`T = 16`, `w = 2^14`,
  `|Σ| = 2^8`, `read8 i = i mod 16`, `step8`: transitions, last step `[out]`), `attrN`,
  `wf_toBP : (toBP F).WF (2^22)`, **`eval_toBP : (toBP F).eval (attrN x) = if F.output x then 1
  else 0`**, `eval_toBP_eq_zero_iff`, `correct_w8`, `correct_w8_ge`.
* Lean pitfalls met here: a hypothesis `h : v ∈ S` makes the elaborator `whnf` its type, which
  enumerates `S` if it unfolds to a box over `Fin (2^22) × …` — keep concrete boxes opaque and use
  the `…_of_eq` lemmas of `RingBoxes`; never re-synthesize the instances of `keyLaw` at concrete
  types (`keyLaw_none_le` is generic); compare powers of `2` through exponents only
  (`pow_le_pow'`, `pow_mul_le'`), never by `exact`/`rfl` on `2^big`. Builds of these files need a
  virtual-memory limit above 30 GB (`ulimit -v 60000000`; RSS about 4 GB).
### Package F (machines) — design (branch `t3/explut-f`)

**Formats** (`PE/Impl/ExpLUT/Prog/Words.lean`, namespace `AdvancedEncryption.ExpLUT.Prog`). Generic
dimensions `Dims` (`N = 2^e`, `q = 2^K − 1`, `W = 2^b`, `m̄ = mb`; `2W ∣ N`, `W < N`, `b ≤ K`,
`2 ≤ K`); `setting D` = `canonSetting (expRingMersenne …) (binaryDigits …)`, `τ = K`;
`Wb = Fin mb`, helpers `Jh = Fin b × Fin 2` (`(t,0)` = `g_t`, exponent `2^t`; `(t,1)` = `g_t⁻¹`,
exponent `W − 2^t`; `helperMap D`; `t = b−1` is present twice, harmless), `Pos = Fin 16`,
`wSt = 2^14`, `half = 2^{K−1}`, `msgR μ ∈ {0,1}`.

* ring element: `encRM N K` — `N` blocks of `K` bits, LSB first, **canonical** (`[0, 2^K − 1)`;
  the all-ones word is never output). `rEnc`, `vecE r`, `matE r s` = `FixedEnc.fun` in `Enum` order.
* `mpkEnc`: `B (Fin 2 × BCol) ++ H (Jh → Fin 2 × Col) ++ a (Pos → Col) ++ A₀ ++ A^in (Pos → Dig →
  Fin 2 × Col) ++ A^aut (Fin b → Dig → …) ++ d (Fin 2)`; `BCol = Fin mb ⊕ Fin K` (Ā columns first),
  `Col = Fin 2 × Fin K`, `Dig = Fin 2 × Col × Fin K`.
* `mskEnc = mpk ++ T (Wb × Fin K)`; `ctEnc = b (BCol) ++ h (Jh → Col) ++ c^aut (Fin b → Dig → Col)
  ++ C^in bottom rows (Pos → Col) ++ c^in (Pos → Dig → Col) ++ c₀ (Col) ++ c_m`;
  `skEnc = mpk ++ k_F (KCol = (Fin W × BCol) ⊕ (Fin W × Jh × Col) ⊕ Col)` (Dec gets no `mpk`).
* **predicate word** `predWord F` (`predLen = 211 · 2^22`): 15 transition tables then the output
  table, indexed by the LUT index `u = z + 2^14 a`; entry `(i, u)` = 14 bits LSB first at
  `14 (2^22 i + u)`; output bit `u` at `210 · 2^22 + u`. `progOf C` reads it
  (`progOf_predWord`). `bpOf F : BP Pos` (`T = 16`, `w = 2^14`, `|Σ| = 2^8`, step 15 = output as
  `0/1`), `wf_bpOf` (`2^22 ≤ W`), **`eval_bpOf`**: `eval (bpOf F) (attrN x) = if F.output x then 1
  else 0`. Valid predicates: `ValidC C := C.length = predLen`; KeyGen gives the zero key and Dec
  `[false]` outside (as RingBTVW).
* attribute: the universe's `encAttribute w8 x` (MSB first per symbol), `attrN x t = (x t).val`;
  message `[μ]`; Dec outputs `[decodeBit μ']` (coefficient 0 in `[2^{K−2}, 3·2^{K−2})`).

**Machine specifications** (targets for the machine agents, `Words.lean`): `SetupSpec χT`,
`EncSpec χs χ χfl`, `KeySpec kb L`, `DecSpec L`, with the laws `setupLawW`, `encLawW`,
`keyLawW kb` (`keyGenLaw` with `gadDec`, `Big = image of mB fair bits` (`KeyBoxes`), zero key on
abort or invalid `C`) and `decOutW`.

**Deviation (for D/G): no exact uniform law mod `2^K − 1`.** A bounded-clock fair-coin machine only
produces dyadic probabilities, and `2^K − 1` is odd. The public matrices are drawn from
`unifW D` (`N K` fair bits read by `decRM`: per coefficient `0` w.p. `2^{1−K}`, others `2^{−K}`),
`setupCoinsLawW D (unifW D) χT` (same order as `setupCoinsLaw`). Distance to `setupCoinsLaw` ≤
(number of public coefficients) · `2^{−K}` — a statistical hybrid step at H0 (or LHL statements
for this near-uniform seed). All other laws (`χT`, `χs`, `χ`, `χfl`, `Big`) must be dyadic
(binary, CBD, boxes of `2^w` values, `Big` = image of fair bits).

**Machine conventions.** Every algorithm is an `XProg k` compiled with `toMachineT`/`toMachineB`
(input tape: `encodeTuple (pw :: inputs)`, output tape: `encodeTuple outputs` via `frameApP`), with
per-tape clocks `timeBoundT` and `descLen` from `XProg.size`, as `RingBTVW/Prog`. Every ring word a
machine outputs is canonicalized (`canonRP`: an all-ones `K`-block → zeros), and every gadget
decomposition (`digitRWP`) is taken of a canonical word (`binaryDigits` uses `ZMod.val`).

**Planned decomposition.**
1. *Common* (`ExpLUT/Prog/Ring*`, generic → `Lib`): `canonRP`; samplers (uniform ring word =
   `N K` coins; coefficient samplers for dyadic laws, negatives by NOT); row × scalar, inner
   products (`mulRMP`, `addRMP`), `x·G` (`rotBP`), `G⁻¹` (`digitRWP`), `σ_{g^j}` (`autMP`, index
   `g^j mod 2N` in unary), `X^{w x_t}` (`rhoJP` with `2N − w x_t`).
2. *Setup*: sample `Ā`, `T`, `B⁽²⁾`, `H`, `a`, `A₀`, `A^in`, `A^aut`, `d` in that order; gadget
   columns `g_c − Σ_w Ā_w T_{w,c}`; assemble `mpk`, `msk = mpk ++ T`.
3. *Enc*: parse `mpk` by fixed offsets, `x`, `μ`; coins `s, e_b, e_h, e_aut, e_in, e_din, e₀, e_m`
   (order of `encCoinsLaw`); `b`; `s_k`, `h_k`; `C_{g_t} = gcAut`, its digits, `c^aut`; the bottom
   rows of `C^in_t`, the digits of `C^in_t = [a_t; ·]`, `c^in`; `c₀`; `c_m`.
4. *KeyGen* (other agents after this note): parse `msk`, `C`; `EvalPK` over `bpOf (progOf C)`
   (16 × (`mulPK`, coefficients `α`/`v` of `L_i`, `lutPK` = W sums of `b` `Aut` rounds)); one try of
   box rejection: `p ← Big`, `y = d₁δ₁ − pubShort p` (block structure of `M_F`), `z = gadDec y`,
   `x = p − realTrap T z`, test `x ∈ Small`; output `mpk ++ assemble x z` (zero key on abort).
5. *Dec*: `EvalCT` (with `EvalPK`), `y_F − κ_F`, inner product with `k_F`, `c_m − d₂ − …`,
   `decodeBit`.
6. *Eval*: `Machine.exists_of_almostConst` (not counted in the cost): `[true]` iff `|C| = predLen`,
   `|x| = 128` and `(progOf C).output x = false` (`Expressive` via `progOf_predWord`).

### Package F — status (branch `t3/explut-f`)

Done (axioms `[propext, Classical.choice, Quot.sound]`):
* `Prog/Words.lean` (formats, specs; see the design note above).
* `Prog/Eval.lean`: `evalMachineX` (almost-constant machine), `authorized_iff`
  (`Authorized ↔ C.length = predLen ∧ (progOf C).output x = false`), `expressive`.
* Lib `ProgAlgo/Mersenne/Canon` (`canonRP`, `canonW_eq`: canonical words are `encRM ∘ decRM`),
  `Mersenne/MatMul` (`matMulMP`, `decRM_sumLoopM`), `Mersenne/GadRow` (`gadRowP`: canonical
  `g_c − P_c`, `2^c` by doublings of `1`). Cost certificates checked (not yet committed as
  lemmas): `check 8 canonRP σRing σRing' [7, 44 N, 40 NK]`, `check 8 matMulMP σMat σMat' wMatM`
  (`wMat` with the `m n l` coefficients `48, 76 NK, 73 N, 71 N², 107 N²K, 22 N²K², 7 K`),
  `gadRowP`: `8 + 27 K + 63 NK + 11 K² + 89 NK² + 18 NK³` sweeps (output tape `≤ top`).
* `Prog/UnifCanon.lean`: `unifCanonP` (fair bits → canonical words), `appendLaw_unifCanonP`,
  word laws of i.i.d. families (`lawVec`, `lawMat`, `lawFunMat`, `lawFunFunMat`, `υW_eq`).
* `Prog/SetupGad.lean`, `Prog/SetupP.lean`: **`setupP X : XProg 128`, `law_setupP`,
  `setupSpec_setupMP`** — the `Setup` machine realizes `setupLawW D χT` exactly, for any explicit
  sampler `X : RingSampler D χT` (7-tape program appending the canonical word of a `χT` sample).

* `Prog/Samplers.lean`: `χbin D` (`0`/`1` with probability `1/2`), `binSampler D : RingSampler`.
* `Prog/SetupSize.lean`: `size_setupP_le`, **`descLen_setupMP_le`** (`≤ 6 B 3^128 (516 + B)`,
  `B = X.P.size + 34 (195 m + 36) + 2·10^6 + 4` when every field count `n` has `n N K < 2^m`;
  at `N = 2^24`, `K = 2^16`, `b = 22`, `m = 100`: `≈ 2^249`), `time_setupMP` (`totalTimeT`).

Remaining for F:
* closed clock of `setupMP` (per-tape, as `RingBTVW/Prog/TightSetup`: `vb_smp` for `repF`, `VB.natP`,
  `VB.checkMap` with the certificates above, `vb_appendTapeP`/`vb_frameApP`), its `descLen`, numerics;
* concrete `RingSampler`s (binary `χT`: one fair bit then zeros; CBD/box coefficient samplers with
  negatives as one's complement NOT);
* `Enc` (design below), then its clock/descLen.

**Enc plan** (all ring words canonical; `σ_{g^j}` as `j` iterations of `σ_g`, `g = 1 + 2N/W` in
unary — `autMP` with a template of length `g`; `X^{w x_t}` by `rhoJP` with `2N − w x_t`): parse the
input frames (`ufChunk`/`dropChunk` of `RingBTVW/Prog/EncP`), sample the coins in the order of
`encCoinsLaw` with `RingSampler`s, then one generic block
`encRow(s, A, z, e) = canon(s·A⁽⁰⁾ + A⁽¹⁾ − z·G + e)` (per column `(r, i)`: `z_r 2^i` by `rotBP`
doublings) used for `b` (`z = 0`), `h_k` (`z = (s_k, 1)`), `c^aut_{t,d}`
(`z = digit_d(C_t)·(σ_t s, 1)`), `C^in_t` bottom rows (`A = (−a_t ; 0)`-style, `z = −X^{w x_t}(s,1)`),
`c^in_{t,d}`, `c₀` (`z = (s, 1)`); `c_m = s d₁ + d₂ + e_m + 2^{K−1} μ`.

### Package F4 — the `Dec` machine (branch `t3/explut-f4`, in progress)

**Design.** `Dec` is written as code of a small verified register machine instead of raw tape
programs:
* `SigabaNeoStd/Lattices/ProgAlgo/Mersenne/VM.lean`: **`RingVM`** — 200 word registers, the ring
  instructions of `ℤ_{2^K−1}[X]/(X^N+1)` (`add sub mul canon neg`, and with a template register
  `digit rotB aut rhoJ`; operands cut to `N K` bits by `takeD`, so `exec` is total), the moves of
  `ValVM` (`mv cp drop clr tl`), `rep`/`seq`/`ifb`. `compile : Code → XProg 247` (every
  instruction framed on its own tapes); **`run_flat_compile`/`law_compile`**: the compiled program
  realizes `exec` exactly (from `enc N K w`, `0 < N`, `0 < K`). Cost: each instruction is framed, so
  its clock is that of its Mersenne program on its own tapes (to be summed along `exec`).
* `VMLib` (`wr`, `exec_not_mem`, `exec_rep_inv`, pop/push/shift of words), `VMRing`
  (`decRM_digitRW_canon`: digits of canonical words are `binaryDigit`; `digitRW_zero_rotBW`),
  `VMDot` (**`exec_ddotC`**: the digit dot product `Σ_{i<K} v_i d_i(m₀) + Σ_i v_{K+i} d_i(m₁)`, the
  kernel of Mul/SMul/Aut; constants `Consts`: reg 0 `[]`, 1 `[false]`, 2 zero word, 4 `K` bits).
* `ExpLUT/Prog/DecAlg.lean` (ring level, any `Setting`): `vecMul_ginv_apply`, `mulCT_eq`,
  `mulPK_eq`, `autPK_row`, `smulPK_row`, `autCT_eq` (everything is digit dot products);
  **`rounds_eq_bitRounds`**, `lutPK_eq`, `lutCT_eq` (LUT = one loop over `j < W`, the pair of `j`
  recomputed along the set bits of `j`); **`σ_idx_eq_bitAut`**, `σ_idx_succ`; **`decryptRaw_eq`**
  (`μ' = c_m − d₂ − (Σ_{i,c} σ_{g^i}(b − B⁽²⁾)_c k + Σ_{i,k,c} σ_{g^i}(h − H⁽²⁾ + G⁽²⁾) k +
  Σ_c (c_F − A_F⁽²⁾)_c k)`).
* `ExpLUT/Prog/DecFinal.lean`: the key sums on `RingVM` (registers 180–199): `dotC`, `autVecC`
  (`X := σ_κ(X)`), **`conjC`** (`Σ_{i<W} Σ_e σ_κ^i(x_e) k_{in+e}`), `subVecC`, `halvesC` (rows
  `H_k⁽²⁾`), `g1C` (`G⁽²⁾`), all with exact `exec` theorems.
* Register map: 0–19 constants/templates, 20–41 `κ_t = g^{2^t} mod 2N` (`σ_{g_t}`), 42–55
  `2N − 2^{b'}` (`X^{2^{b'}}`), 58–73 the parsed inputs, 80–89 ddot, 90–119 vector/G⁻¹ blocks,
  140–159 LUT coefficients, 180–199 final sums.
* Decoding: for canonical `v < 2^K`, `2^{K−2} ≤ v < 3·2^{K−2}` iff bit `K−1` ≠ bit `K−2`.
* **Duplication with F3** (branch `t3/explut-f3`, head 16b80df4): F3 built its own ring-word VM
  for KeyGen **under the same paths** (`Mersenne/VM.lean`, `VMRing.lean`, plus `VMMat.lean`,
  `ExpLUT/Prog/KeyVM.lean`) with a different instruction set. The two cannot both be merged as is:
  before merging both into `t3/pe-exp-lut`, rename one family (e.g. F4's to `Mersenne/DVM*.lean`,
  namespace `RingVM` → `DRingVM`, or F3's to `KVM*`), or port F3's routines (`mulPKC`,
  `ginvMulC`, `autPKC`) onto F4's `RingVM` (F4's `mulAccC`/`matGinvC`/`vecAutC` already cover
  EvalPK of Mul/Aut, see below).
* EvalPK is computed inside Dec alongside EvalCT (the same `bitRounds` loop carries the pair
  (public matrix, encoding)); F3 has no shared `EvalPK.lean` yet — a separate PK-only program for
  KeyGen can reuse `RingVM` and the blocks (`mulAcc`, `matGinv`, `bitRounds`) unchanged.

* `Mersenne/VMVec`, `VMGinv`, `VMFam` (Lib): `vecAddC`/`vecSubC`/`vecAutC`, **`vecGinvC`**
  (`v G⁻¹(M)`), **`matGinvC`**, `deintC` (rows of a matrix family), **`mulAccC`** (the Mul sum
  `Σ_{r,i'} ddot(F(r,j,i'), A(·,(r,i')))`), `ddotV_eq` (to `Σ_c v_c · binaryDigit`).
* `ExpLUT/Prog/DecCoef`, `DecCoefMath`: `coefC` (α_{g^j,L_i} resp. v_{g^j,L_15} from the table
  stream of `C`: `σ_{g^j}` along the bits of `j` with the templates `κ_t`, `X^{L(u)}` by the 14
  bits, `W⁻¹` by `rotB`), **`exec_coefC_alpha`/`exec_coefC_vcoef`** (`= alphaCoef`/`vCoef` of
  `bpOf (progOf C)` at `setting D`, `D.b = 22`), `gadC` (the words of `α • G`,
  `decRM_gadMatWords`), `incC` (`J := J + 1` in binary).
* `ExpLUT/Prog/DecFinal`: **`exec_finC`** — the whole end of decryption (the three key sums,
  `μ' = c_m − d₂ − …`, canonical word, decoded bit on register 179) from `c_F` (reg 176) and `A_F`
  (reg 177).

* `ExpLUT/Prog/DecFinalD`: **`exec_finC_D`** — register 179 = `[decodeBit D (decryptRaw …)]` under
  `FinD` (registers hold the word lists of `mpk`, `ct`, `k_F`; c_F, A_F⁽²⁾ words decode to
  `evalCiphertext`, `keyPK … 1`).
* `ExpLUT/Prog/Dec{Rep,Blocks,Calls,Round,RoundT,Rounds,Lut,Mul,Steps,Enc}`: **`exec_evalC_regs`**
  (`D.b = 22`, `C.length = predLen`, `DecRegs D mpk ct C w`): `devalC` leaves `A_F = keyPK` (reg 177)
  and `c_F = evalCiphertext` (reg 176), `RepM`/`RepV` entrywise; registers below 80 unchanged. One
  round = `roundC t` (`roundPK_eq`/`roundCT_eq`), rounds along the bits (`exec_roundsN` →
  `bitRounds`), the table loop `lutC`, Mul `mulC i`, the steps `stepsN` (`evalPKAt`/`evalCTAt`).
  `DecRegs` needs templates 76 = `4K` bits, 77 = `famMLen D`, 78 = `14·2^22` bits.
* `ExpLUT/Prog/DecSplit` (`splitSkC`/`splitCtC`: fields of `sk`/`ct` from registers 76/77),
  `DecFront` (`run_parseD`: input `encodeTuple [pw, sk, C, ct]` onto registers 76, 73, 77),
  `Mersenne/VMFront` (`tmplsP`: templates by `natP`), `Mersenne/VMWF` (`wf_compile`,
  `coinFree_compile`).
* **Cost** (`Mersenne/VMCert`, `VMCost`, `VMSize`): every instruction re-certified with scratch at
  the top size (`checkT_*`, `decide +kernel`); **`compile_time`**: for per-register bounds `B`
  closed under the code (`Closed`), `timeBoundT (compile c) (encB Mo N K B) ≤ vmTime … c` and the
  bounds are kept; per-instruction table `instrTime`; **`size_compile`**: exact state count
  `vmSize c` (per-op sizes: mulRMP 13341, autMP 5859, addRMP 4906, digitRWP 3751, …).
* **Description length warning**: `descLen_toMachineB` has the factor `3^k` (k tapes); RingVM has
  247 tapes (256 for the whole machine), so Dec's descLen is about `2^400+`, not `2^200–2^260`.
  The lever: shrink the register file (e.g. ≤ 81 registers → 128 tapes → `3^128 ≈ 2^203`).

**Remaining for F4**:
1. Register clash in the front end: `run_parseD`/`splitSkC`/`splitCtC` use 76/77 for the raw
   `sk`/`ct`, while `DecRegs` wants templates there (and 78). Fix without touching proofs: build
   the templates for 76–78 elsewhere (e.g. 175, 178, 199 — never written by `devalC` before use),
   and `cp` them into 76–78 after the split; the validity flag (`lenEqP predLen`) on another free
   register.
2. The template list of the prelude (`tmplsP`, plus `ONE` on 3, `[true]` on 75, the VM tapes
   40–43 incl. the all-ones word), and the bridge of `exec_evalC_regs` (`RepM`/`RepV`) and of the
   split fields to `FinD`/`DecRegs` (`cFs := cs`, `AF0s := as.take 2K`, `AF1s := as.drop 2K`).
3. The machine `(seq guard (ifBlank … (seq parse (seq templates (seq (frame vmE (compile decCode))
   output)))).toMachineB 255 0 nDec` and **`DecSpec`** (determinism from `coinFree_compile`;
   `[false]` for invalid `C`; output `[true, b, false]` on tape 0).
4. Clock: a per-register bound `B` for the Dec code, `Closed`, closed forms of the `w*`
   polynomials, then the concrete numbers at `Params/Conf`; descLen via `size_compile` (and
   possibly the register-file shrink above).
### Package F2 (clock of `Setup`, `Enc`) — status (branch `t3/explut-f2`)

Done (axioms `[propext, Classical.choice, Quot.sound]`; no change to the formats of `Words.lean`):

* **Clock of `Setup`** (`Prog/SetupTime.lean`): per-tape bound vectors (`VB`) through the whole
  program — the framed samplers on their own tapes (`vb_unifCanonP`: fair bits, two templates, the
  tail `ucTail` certified by `check_ucTail`, the append; `vb_ucF`, `vb_TF` for the sampler of `T`,
  fields tracked exactly, the sampler scratch at a common bound `S`), the templates at their exact
  lengths (`vb_tmplP`), the gadget columns (`vb_detCore`: `check_matMulMP` (scratch at the top),
  `check_gadRowP`, each sweep `2 M + 3`), the output (`vb_outP`, additive in `M`).
  **`time_setupMP_le : SetupBounds D X.B nI S M → nInS ≤ nI → (setupMP X).time ≤ setupTF D X.B nI S M`**
  (`SetupBounds`: `S` above every field's bits and `B.S₀`, `X.B.a ≤ N K`, `M` above the scratch, the
  input and the templates).
* **Concrete `Setup`** (`Prog/SetupConf.lean`, `Prog/EncSamplersConf.lean`): counts in closed form
  (`nB2_eq`, …, `nAaut_eq`; no enumeration is evaluated), `setupTFn`, `nInS ≤ 2^11`; for any `D`
  with `e = 24`, `K = 2^16`, `b = 22`, `m̄ = 3·2^40 + 408` and the binary sampler
  (`S = 2^97`, `M = 2^98`): **`time_setupMP_conf`: clock ≤ 2^242** (the closed form lies in
  `(2^241, 2^242]`; dominated by `Ā T`: `22 N² K² · m̄ K` sweeps of `2 M + 3` steps),
  **`descLen_setupMP_conf`: ≤ 2^249**; at `Dc`: `EncConf.time_setupMP_Dc`, `EncConf.descLen_setupMP_Dc`.
* **Samplers of `Enc`** (`Prog/EncSamplers.lean`): ring elements with i.i.d. coefficients
  (`ringLawD`; the word is the concatenation of the canonical coefficient words, `rEnc_ofCoeffs`,
  `ringLawD_enc`); flooding `floodR D e`, `floodP D e = repF N (entF K e)`, `law_floodP` (`e < K`);
  centered binomial `cbdR D η`, `cbdPM η L K` = RingBTVW's `cbdP` with one's-complement leaves
  (`mv v = v − [v < 0]`, `encM_eq_zmodEnc`), `law_cbdPM`, `cbdRP D η L = repF N (cbdPM …)`,
  `law_cbdRP`. **Interface for `Enc`**: `AppendLaw P 0 P5 (χ.map (rEnc D).enc)` (scratch `2 … 6`
  blank; `Setup`'s `RingSampler` has only `2 … 4`, so these are not `RingSampler`s; `n` elements
  are `repF (n N)` coefficient samples, `catPow_mul`). At `Dc` (`EncSamplersConf`): `χc = cbdR Dc 16`,
  `χfl = floodR Dc eFl` (`rfl`), `law_χcP` (`cbdRP Dc 16 6`), `law_χflP` (`floodP Dc eFl`).
* **The encoding row** (Lib `ProgAlgo/Mersenne/EncRow.lean`, `Prog/EncRow.lean`): `encRowP : Prog 56`
  (`0` output register of `L N K` bits, `1` `s`, streams `2` `A₀`, `3` `A₁`, `4` `Z`, `5` `E`,
  templates `6` `K`, `7` `N`, `8` `N K`, `9` `L`; scratch `10 … 55`), `run_encRowP` (`rowW`),
  `rowW_eq`, **`rowW_vecE`**: on the words of families over `α`, the word of
  `c ↦ s A₀ c + A₁ c − Z c + E c` (canonical). `check_encRowP`, **`time_encRowP`**:
  `(2M + 3)(200 + L (200 + 400 N + 400 N K + 100 N² + 200 N² K + 30 N² K² + 50 K))`.

* **The gadget stream** (Lib `ProgAlgo/Mersenne/GadStream.lean`): `gzP : Prog 36` (`0` output
  register of `2K · N K` bits, `1` `z₀`, `2` `z₁`, templates `3` `K`, `4` `N`, `5` `N K`, `6` `K − 1`;
  scratch `7 … 35`), `run_gzP`: `gzW z₀ ++ gzW z₁` (`z_r, 2 z_r, …, 2^{K−1} z_r`), `decRM_gIt`:
  entry `i` reads `2^i • z_r`; `check_gzP`, `time_gzP`
  (`(2M + 3)(100 + 400 K + 400 N K + 400 N K² + 100 N K³ + 100 K² + 100 N)`).

Remaining for `Enc` (design fixed; each block a `Prog` with a run lemma and a certificate, as
`encRowP`):
1. *gadget stream on the scheme's words*: entry `c = (r, i)` of `gzW z₀ ++ gzW z₁` reads
   `(z ᵥ* G) (r, i)` (`decRM_gIt`, `vecMul_G_apply`, `Enum.getElem_product`), and `rowW_vecE` with
   a general `Z` stream (only `decRM` of its blocks matters); `Z` of every encoding is such a stream (`b`: the zero word of `|BCol| N K` bits,
   a template), so every component is `encRowP` with `A₀`, `A₁` the two rows of the public matrix:
   `b` (`B`, `z = 0`), `h_k` (`H_k`, `z = (σ_{g^{je k}} s, 1)`), `c^aut_{t,d}` (`A^aut_{t,d}`, secret
   `s_t = σ_{kf t} s`, `z = digit_d(C_t) (s_t, 1)`), `c₀` (`A₀`, `z = (s, 1)`), `c^in_{t,d}`
   (`A^in_{t,d}`, `z = digit_d(C^in_t) (s, 1)`); the bottom rows of `C^in_t` with `A₀ = a_t`,
   `A₁ = 0`, the sign handled by `−(s a_t) + z G + e = (0 − s a_t) − (−z) G + e` (or a variant of the
   row with `subRMP` for the first term);
2. `σ_{g^j}(s)`: `j` rounds of `autMP` with the unary index `g = 1 + 2N/W` (template), `j = je k`
   or `2^t` by `natP` (`ExpRing.σ_comp`; `σ` is `2N`-periodic, so no index arithmetic);
3. `C_t = σ_{kf t}(H_{inv t}) − [0; σ_{kf t}(h_{inv t})]` (`autMP`, `subRMP`, `canonRP` per entry;
   `h_{inv t}` read back from the output word by its offset), then its digits (`digitRWP` of the
   canonical words — `binaryDigits` reads `ZMod.val`), streamed in `Dig` order;
4. `X^{w x_t}`: the template `2N − w x_t` from the 8 bits of `x_t` (most significant first: `dblP`
   doublings, then `14` more, `dropP` from a `2N` template), `rhoJP`;
5. parsing (`ufChunk` per field of `mpk`, as RingBTVW's `encParseP`), the coins in the order of
   `encCoinsLaw` (framed `cbdRP`/`floodP`, `law_seq_app` as `law_setupP`), `c_m` (`mulRMP`,
   `addRMP`, the word of `2^{K−1}` at coefficient `0` when `μ`), the frame of the output (`frameApP`);
6. the law (`EncSpec D (cbdR D 16) (cbdR D 16) (floodR D eFl)`, i.e. `χc χc χfl` at `Dc`) and the
   costs (`VB` chain as `SetupTime`; dominated by `c^aut`: `b · 4K² · 2K` rows of `2K` products,
   about `2^{56}` products of `22 N² K²` sweeps each, top `≈ 2^{98}`: clock `≈ 2^{240}`).

### Package G (attribute hiding of the implementation) — branch `t3/explut-g`

Files `PE/Impl/ExpLUT/AH/*` (namespace `AdvancedEncryption.ExpLUT.Prog`, in the aggregator) and
`PE/Impl/Game/OneSetup.lean`. Axioms `[propext, Classical.choice, Quot.sound]`.

**Main results.**
* `AH/Final.attributeHiding_Dc`: `AttributeHiding (univ w8) params impl` for every `impl` with
  `ImplSpec Dc kb L impl χc χc χfl` (`Setup` meets `SetupSpec Dc (χbin Dc)`, `Enc` meets
  `EncSpec Dc χc χc χfl`, `KeyGen` meets `KeySpec Dc kb L` **and `KeyLongSpec Dc L`** (empty word on
  predicate words longer than `L`, as RingBTVW's `key_long`), `Eval = evalMachineX`), from
  `CircularRingLWE.decision.HardAt (circParamsD Dc) kb'` with `64 · 2^256 · C ≤ 2^kb'`, given
  `KbCover kb 2^18500`, the flooding hypothesis `hflood` at some `ε_fl ≤ 2^{−148}`, and the
  reduction machines `RedMachine … C A Dm` (below). Simulator: `simMachine Dc` (`AH/Sim`: the
  encoding of `ctUW`, independent `unifW` entries; existence via `Machine.exists_finiteAlg'`, cost
  not bounded — it does not enter the definition).
* `attributeHiding_Dc_registry`: the same from `CircularRingLWE.decision.Holds`, with
  `strength_Dc : 1155 ≤ CircularRingLWE.decision.H (circParamsD Dc)` (`m = m_B + 1 + τ|J| ≤ 2^50`).
  **Required strength**: `kb' ≥ 262 + log₂ C`; `1155` bits cover `log₂ C ≤ 893`.
* Generic: `AH/Assembly.attributeHiding_of_reduction` (any `D`, `kb`, coverage, statistical
  hypotheses), `advantage_le` (`|adv| ≤ statW ε_fl + |rAcc − uAcc|`).

**Pieces.**
* `AH/Unif`: `unifW` is within `ε_U = N 2^{−K}` of uniform (`closeTo_unif_unifW`, every element has
  probability `≥ 2^{−NK}`, Bernoulli); `closeTo_setupLaw` (`epsSetup`), `ctUW` and `closeTo_ctU_ctUW`
  (`epsCT`), `mem_support_setupLawW`.
* `AH/Games`: `real_eq_gameV` (real experiment = `gameV` of `realVW`, keys `KGiW` = ideal key law
  on `Setup`'s support under `RealCovW`), `realVW_close` (to D's `hyb0`, `χbin = bitLaw`),
  `ideal_eq_gameV0` (unshifted challenge), `idealVW_close`, `gameV0_idealView_eq` (`ctU_shift`).
* `AH/RedGame`: the reduction's experiment `redGame` (secret `redSec`, view `view2`, keys `KGsim`
  = `redKeyLaw` with `T_sim`); `accept_red`: equal to the hybrid's for continuations rejecting
  `bad` (`KGsim_eq_KGiW` under `SimCovW`, `22 ≤ b`).
* `Game/OneSetup` + `AH/Chain1`: **a statistical change of the secret costs its distance once**
  (`closeTo_runWith_setup_one`; D's `chain` pays `|Attr| = 2^128` per step, which with P's
  `m̄ = 3NK + 408` would give only `2^{−20}`); `chain1`.
* `AH/Conf`: `Dc` (`setting Dc = confS` by `rfl`), coverage `realCovW_of`, `simCovW_of` from
  `KbCover kb coverBound`: real shift `≤ τn = 2^40`; `T_sim` shift `≤ W τ n D^b (B_R̂ + 2)` with
  `B_R̂ = (stepBound 1 1 1)^[16] 1` (`matBnd_simKey`, `progBnd_progOf`, `rowBnd_simTrap`,
  `vBound_iterate_le`, `simShift_rhat_le`). **The cover bound `2^18500` suffices.**
* `AH/Stat`: `delta1, delta5 ≤ 2^{−148}`, `deltaT ≤ 2^{−189}`, `epsSetup, epsCT ≤ 2^{−150}`,
  `statW Dc ε_fl ≤ 2^{−140}` for `ε_fl ≤ 2^{−148}`, `hstat_Dc`.

**Open (hypotheses of `attributeHiding_Dc`).**
1. ~~`hflood` at `χfl`~~ — **done in package G3** (`hflood_Dc`, `attributeHiding_Dc'`).
2. `KbCover kb 2^18500` for the KeyGen machine's `KeyBoxes` (P's `famBig`/`famBall` boxes over
   `PIdx (Wb Dc) (Jh Dc) …` have it by `add_mem_of_eq`; `Big` must be the image of fair bits).
3. **The reduction machine** (`RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm`): for every
   admissible `A` and distinguisher `Dm`, a machine `R` with
   `R.acceptProb (realLaw (circParamsD Dc)) = rAcc …`, `R.acceptProb (idealLaw …) = uAcc …` and
   `cost R ≤ C (cost A + cost Dm)²`. `rAcc`/`uAcc` = probability over `circReal`/`circUnif` that
   `redGame` followed by `DcB Dm` accepts. `R` must: decode the instance word (B's rows: plain rows
   = the columns of `B`, `d`, and the helper columns `(k, (1, i))`; key row `(i, j)` = helper
   `k = jhE j` column `(0, i)`, automorphism index `jList`; the law bridge is **done in package G3**:
   `realLaw_bind_decode`/`idealLaw_bind_decode`, so `R` only has to run `F ∘ decode D` on its input);
   draw `B̄⁽²⁾`, gadget columns of `B⁽²⁾`, `H⁽²⁾`, `d₂`, the flooding errors, `zr` (`redSec`); run
   `A` (`Lib/Machines/Inline`) answering select with `mpkEnc (view2 …).1`, key queries with
   `KGsim` (`EvalPK` over `bpOf (progOf C)` for `R̂_F` via `simKey` (Corollary 1 propagation),
   `simX`/`simTrap` (Lemma 11), one box try with `kb`, encoding `skEnc`), the challenge with
   `ctEnc (shiftCT ⌊q/2⌉ μ (view2 …).2)`; track `bad` (`authW`: `|C| = predLen ∧ output x = false`);
   output `Dm`'s verdict on `viewObs8` if not `bad`, `[false]` otherwise.

### Package G3 (flooding at `χfl`, circular law bridge) — branch `t3/explut-g3`

Files `SigabaNeoStd/Lattices/FloodRing.lean`, `SigabaNeoStd/Lattices/CircularRingLWEInst.lean`,
`PE/Impl/ExpLUT/FloodBound.lean`, `PE/Impl/ExpLUT/AH/Flood.lean`, `PE/Impl/ExpLUT/AH/CircBridge.lean`
(all in the aggregators). Axioms `[propext, Classical.choice, Quot.sound]`.

**Flooding (open hypothesis 1 of G, closed).**
* Library `FloodRing`: `floodRing N Q W` (one ring element, coefficients uniform below `W`; P's `χfl`
  is `floodRing (2^24) q (2^eFl)` by `rfl`, `χfl_eq`), `closeTo_floodRing_add` (`∑ⱼ |δⱼ|/W`),
  `closeTo_floodRing_add_le` (`N B / W` for `cnorm δ ≤ B`), `closeTo_pi_floodRing_add_le`
  (independent families: `#entries · N B / W`, via `Stat.closeTo_pi`). D's `floodLaw` is not
  rewritten as `Lattices.floodLaw` over a flattened index type: its four independent families are
  flooded one by one (`CloseTo.bind`), which needs no law equality.
* `FloodBound` (generic over `S : Setting (Negacyclic (ZMod Q) n)` with a `NormSpec` whose norm is
  `cnorm`): `closeTo_iidFam_floodRing_add`, `floodCount S Pos` (the flooded ring elements),
  `closeTo_floodLaw_add_le`, `cnorm_floodShift_le` (entries of `floodShift ē_b zr` are `±` sums of at
  most `|Wb|` entries of `ē_b`, possibly under `σ_{g_t}` (`nrm_σ`); norm `≤ |Wb| B_χ`, no factor `n`
  since `zr` is binary), **`hflood_floodRing`**: `hflood` at `ε = floodCount · n (|Wb| B_χ) / W`.
* `AH/Flood`: `εflDc = floodCount (setting Dc) Pos · 2^24 (m̄ · 16) / 2^eFl`,
  `floodCount_Dc_le : floodCount ≤ lhlCols`, **`εflDc_le : εflDc ≤ 2^{−249}`** (P's `flood_budget`,
  generic `natCast_mul_div_le_inv_pow`, `flood_budget_gen`), `εflDc_le_148`,
  **`hflood_Dc`** (exactly the hypothesis of `attributeHiding_Dc`), and
  **`attributeHiding_Dc'`** / **`attributeHiding_Dc_registry'`**: package G's results without
  `hflood` (remaining hypotheses: `ImplSpec`, `KbCover kb coverBound`, `RedMachine`, the
  constant `C`).

**Circular Ring-LWE law bridge.**
* Library `CircularRingLWEInst`: `CircularRingLWE.circRing p` (`σ ← polyOf χ_s`, uniform `aᵣ`,
  `eᵣ ← polyOf χ_e`, `(aᵣ, aᵣ σ + eᵣ − keyShiftRing p σ r)`), `realLaw_eq_circRing :
  realLaw p = (circRing p).map encodeRing`, `idealLaw_eq_uniform`; `pi_sum_bind`, `pi_unit_bind`,
  `pi_prod_bind`.
* `AH/Final`: `jList` now uses the explicit order **`jhE D : Fin (b·2) ≃ Jh D :=
  finProdFinEquiv.symm`** (was `Fintype.equivFin`, whose order is unspecified, so a machine could
  not know it), and `mCirc D = m̄ + K + 1 + K (b·2)` (same value). `strength_Dc` is unchanged
  (it holds for every `J`).
* `AH/CircBridge` (generic in `D : Dims`): row layout `ρ D : Fin (circParamsD D).rows ≃ Coord D`,
  `Coord D = BCol ⊕ Unit ⊕ (Jh × Col)`: plain rows (`plainE`) are, in order, the columns of `B`
  (`Fin (m̄+K) ≃ Wb ⊕ Fin K`, `bcolE`), `d`, then the plain helper samples `(k, (1, i))` at
  `m̄ + K + 1 + (i·2b + j)`, `k = jhE j`; key rows (`keyE`, the registry's `finProdFinEquiv`
  order) `m + (i·2b + j)` are the circular samples `(k, (0, i))`, `k = jhE j`, automorphism index
  `(jList D)[j]` (`get_jList`). `toPair`, **`enc D i = encodeRing (toPair D i)`** (the registry's
  word), `decode D` (choice on `encodeRing`; zero instance on other words), **`decode_enc`**.
  `keyShiftRing_eq` (the registry's key shifts are `σ_{g^{je k}}(s̄) G⁽¹⁾_{(0,i)}`, via
  `autσ_of_odd` and `G 0 (0, i) = 2^i`), `circRing_eq`, **`realLaw_circParamsD :
  realLaw (circParamsD D) = (circReal … (χcbd D) (χcbd D)).map (enc D)`** (`χcbd D` = CBD(16)
  coefficients, `χcbd_Dc : χcbd Dc = χc` by `rfl`), **`idealLaw_circParamsD :
  idealLaw (circParamsD D) = (circUnif …).map (enc D)`**, `realLaw_circParamsD_Dc` (with `circR Dc χc χc`),
  and for G2 **`realLaw_bind_decode` / `idealLaw_bind_decode`**: `(realLaw p).bind (F ∘ decode D) =
  (circReal …).bind F` (resp. `circUnif`). Hence a reduction machine whose output law on a word `w`
  is `F (decode D w)` with `F i = (redGame … i).bind (DcB Dm)` has acceptance `rAcc`/`uAcc`.
* Note for G2: `decode` is specified by choice; the machine parses `encodeSample`'s word
  (`encPair encBits (encList encNat)`: the public matrix, then the `rows · N` coefficients) and must
  be shown to agree with `decode` on encodings (`decode_enc`), e.g. by computing `toPair`'s inverse
  `ofPair` from the parsed coefficients (`ofPair_toPair`).

**Remaining for attribute hiding at `Dc`**: `KbCover kb 2^18500` for the KeyGen machine's boxes
(G's item 2), the reduction machine with its cost bound (G's item 3, package G2), the machines
meeting `ImplSpec` (package F).
### Package F3 (the `KeyGen` machine) — status (branch `t3/explut-f3`)

**Design: a register machine on ring words.** `KeyGen` is far too large for hand-plumbed tape
programs (nested loops five deep over `16` steps, `W = 2^22` coefficients, `b = 22` rounds,
`16K³` digit products per `Mul`), so it is written as code of a small VM whose semantics is a
pure function, and every routine is proved once at the level of lists of ring elements.

* `Lib/Lattices/ProgAlgo/Mersenne/VM.lean` — **`MVM.Code`**: `64` word registers;
  `op o d a b` for `o ∈ {add, sub, mul, neg, aut, rho, rot, dig}` (the Mersenne programs `addRMP`,
  `subRMP`, `mulRMP`, `notP`, `autMP` (`σ_{|b|}`), `rhoJP` (`X^{−|b|}`), `rotBP` (`2^{K−|b|}`),
  `digitRWP` (digit `|b|`)), each result **canonicalized** (`canonRP`); word moves `mv` (shift `|c|`
  bits), `mvR` (shift `N K` bits), `cp`, `drop`, `clr`, `tl`; `rep c body`, `seq`, `ifb`, `nop`.
  `compile : Code → XProg 105`, every instruction in a frame of its own tapes (operands loaded into
  work tapes cut to `N K` bits, so the semantics `exec N K` is **total and exact**).
  **`law_compile`**: the law of the compiled program on `enc N K w` is the point mass at
  `enc N K (exec N K c w)`; **`wf_compile`** (no `rep` body writes its counter, `Code.WFc`).
* `Mersenne/VMRing.lean` — reasoning tools: registers as **queues** `encL l` of canonical words
  (`mvR d s` moves the head of `s` to the tail of `d`); every `op` on canonical words is the ring
  operation (`canonW_add/sub/mul/neg/aut/rho/rot/dig`); `exec_writes` (footprints);
  `exec_rep_inv` (loops by invariants); one-instruction `exec_*` lemmas and the tactics `vm_step`
  (execute the head instruction of a `seq`) / `vm_simp`, which symbolically execute straight-line
  code (register names are `@[vmreg]` abbrevs, equalities decided by `Fin.reduceEq`). Routines clear
  their scratch registers so their effect is an exact update chain and composes by `rw`.
* `Mersenne/VMMat.lean` — **routines with exact specifications** (all on fixed registers
  `29 … 63`; callers use `0 … 28`):
  * `digAccC` (`exec_digAccC`): `acc += Σ_{i<K} e_i · digit_i(x)` over the next `K` stream elements;
  * **`mulPKC`** (`exec_mulPKC`): `EvalPK` of `Mul` with binary digits,
    `A'_{a,j} = Σ_{(r,i)} Σ_c Ad_{(r,j,i)}[a,c] · digit_{c.2}(A_{c.1,(r,i)})` (`mulPKm`), streaming
    the digit matrices once in the order of their word (`adL`), `(r, j, i, a, c)`; structure:
    `iBody` (four digit accumulations), the `ι` loop, the `j` loop (partial sums as a queue),
    the two `r` parts, a transposition (`tLoop`, `tOut`);
  * **`ginvMulC`** (`exec_ginvMulC`): `X · G⁻¹(Y)` (`ginvMulm`);
  * **`autMatC`** (`exec_autMatC`): `σ_k` on every entry, `k = |rKc|`;
  * **`autPKC`** (`exec_autPKC`): `EvalPK` of `Aut`: `H · G⁻¹(mulPK(σ_g^{m}(A), Aaut))`
    (`m = |rP|` applications of `σ_g`).
* `ExpLUT/Prog/KeyVM.lean` — the bridge to the scheme at the dimensions `D`: `matE_enc`,
  `digE_enc` (the words of `Words.lean` are the queues of the routines), `mulPK_eq_mulPKm`,
  `mul_ginv_eq`, `autMat_eq`, `aut_iterate` (`σ_g^{m} = σ_{g^m}`), **`autPK_eq`**;
  **`roundsPK_eq_bitChain`** (`A_j` after `t` rounds = `Aut_{g_s}` applied for the set bits `s` of `j`,
  increasing; the basis of item 1 below) and **`lutCoef_pow`** (`α_{k,L} = W⁻¹ Σ_u c_u μ^u`,
  `μ = σ_k(X^{2n−1})`; the basis of item 2).
  Axioms of all of these: `[propext, Classical.choice, Quot.sound]`.

**Done on `t3/explut-f3b`** (axioms `[propext, Classical.choice, Quot.sound]`):

* VM extension (`Mersenne/VM.lean`, `VMRing.lean`): `app d s` (`d := d ++ s`; `app d d` doubles)
  and `eqb f a b` (`f := [a = b]`); `law_compile` now via `coinFree_flat_compile` (the compiled
  code is coin free; `app`/`eq` lengthen words, so not `NoGrow`). `exec_app`, `exec_eqb` are in
  `vm_step`/`vm_simp`.
* `ExpLUT/Prog/KeyLut.lean` — the VM code of `EvalPK`, generic in `N`, `K` (caller registers
  `rAinS … rT15` = `0 … 28`; scratch `35 … 46` of the library between routine calls):
  `exec_matAddC` (`rAccL += rMOut`), `exec_agC` (`α G` as `gM α`), `exec_bitLoop`/`exec_coefAC`
  (`α = 2^{K−b}(Σ_{u<n} X^{−c_u} μ^u · X_c)`, `c_u` the complement of the `e` bits of entry `u`,
  `sumA`), `exec_coefVC` (`v = 2^{K−b} Σ_u [C_u] μ^u`, `sumV`), `exec_chainLoop`/`exec_chainC`
  (`A_j = chainM`: for `t < b`, digit `t` of the constant `j` (`hd_dig_natCast`) selects `autPKC`
  with `|rP| = 2^t` (doubled by `app`) and `H_{(t,0)}` from the `H` stream, or skips the block of
  `A^aut_t`), `exec_jLoopK` (`rAccL = accM = Σ_{j<n} A_j G⁻¹(α_j G)`, `μ_{j+1} = σ_g(μ_j)`,
  `j := j + 1` as a ring constant), `exec_stepK` (`mulPKC` with the `A^in` stream, then the
  table; `rCs` advanced by `|rTtab|`), **`exec_evalC`** (15 `α`-steps and the `v`-step:
  `rA = evalVM … 16`). Read-only register sets `roJ`, `roC`, `roS`; input structures `ChainIn`,
  `StepIn`, `CoefIn`.
* `ExpLUT/Prog/KeyEval.lean` — **`keyPK_eq_evalVM`** (`D.b = 22`): `(fun a c => keyPK (helperMap D)
  mpk (bpOf (progOf C)) a c) = evalVM (cvsK D C) (gD D) (HfK D mpk) (AaK D mpk) D.b X⁻¹ (2^b)
  (AinK D mpk) A₀ 16`, with `xInvG_mul_monoX`, `monoX_pow_two_n_sub_one`, `val_take_add_cmpl`
  (`L(u) + c_u = 2^{14} − 1`), `table_bpOf`/`table15_bpOf`, `coefs_eq`, `roundsPK_eq_chainM`,
  `lutPK_eq`, `evalPKAt_eq`.
* `ExpLUT/Prog/KeyBoxW.lean` — the key boxes: `kbOf D B hB r` (`Big` = image of
  `|PIdx| N B` coins, `kbOf_Big : Big = famBig B` whatever order a machine reads the coins;
  `Small = famBall r`), `kbCover_of`, `kbCover_of_eq`; **`kbDc`** (`Bk = 18750`,
  `r = 2^{Bk−1} − 1 − 2^{18500}`, opaque) and **`kbCover_Dc : KbCover kbDc coverBound`**.
  (Pitfall: `KbCover (kbOf Dc …)` makes the elaborator enumerate the ball — keep `kbDc` opaque.)
* `Lib/Lattices/BallTest.lean` — `zabs_le_iff_val` (`|x| ≤ r ⟺ val(x+r) < 2^B ∧ val(r−x) < 2^B`
  for `2r < 2^B`, `2^{B+1} ≤ q`), `cnorm_le_iff_digits` (digits `[B, K)` of `v + allC r`,
  `allC r − v` vanish), `sum_binaryDigit_eq_zero_iff` (fewer than `q` digits).
* `ExpLUT/Prog/KeyTryMath.lean` — `pubShort_apply` (row `i'` of `M_F(p, 0)`: the `Ā` columns, the
  `η_{i',k}`, `− Σ_{i,k} [i' = i·k] Σ_c G_{0,c} p_{i,k,c}`, `[i' = 0] Σ_c A_F[0,c] p_c`),
  `HelperMap.backRow`, `mulRow_eq_iff`, `sum_mulRow` (`Σ_i [i' = i·k] f_i = f_{backRow i' k}`).
* `ExpLUT/Prog/KeyTryVM.lean` — queue routines (registers `29 … 55`, free after `EvalPK`):
  `exec_ipC` (`rIa += Σ a_t b_t`), `exec_autQC` (`σ_k` on a queue), `exec_gadRecC`
  (`Σ_j 2^j a_j`), `exec_tstC` (`rFa += Σ_{m<n} (digit_{B+m}(x + R) + digit_{B+m}(R − x))`),
  `exec_decC` (one element from `N·B` coins: coefficient `j` = `val(chunk_j) − c₂`),
  `exec_decQC` (`n` elements, `decList`), `exec_digQC` (the digits `0 … n−1` of `rY` as a queue).
* `Lib/Lattices/CoinsUniform.lean` — `map_uniformList_eq_uniformOfFinset` (coins decoded
  injectively onto `S` have the law `uniformOfFinset S`; for `S = kbDc.Big = famBig` via
  `kbOf_Big`, with `c₂ = 2^{Bk−1}` so that `val(chunk) − c₂ = cenEmb chunk`).

**Remaining for `KeyGen`** (design fixed by the code above; the next agent should start with 3,
whose routines exist, then 1–2, 4, 5):

1. *Parsing (VM)*: from the `msk` word, by a stream and length templates: `B` (row 0: `m̄ + K`
   words, row 1), `H` word (`rHW`), `a`, `A₀` (`rA`), `A^in` (`rAinS`), `A^aut` (`rAautW`),
   `d`, `T`; bridge lemmas: `matE_enc`/`digE_enc` + `FixedEnc.fun` over `Jh`/`Pos`/`Fin b` as
   `hL`/`ainL`/`aautL` (with `HfK`/`HiK`/`AaK`/`AinK`).
2. *Constants (VM)*: `rOne` (`[true] ++ 0^{NK−1}`), `rMu0 = X⁻¹` (`rho` of `1` by `[false]`),
   `rXc = X^{2^{14}−1}` (`rho` of `1` by a template of `2N − 2^{14} + 1`), templates of the
   `StepIn`/`CoefIn`/`ChainIn`/`MulTmpl` structures (outer program, `natP`).
3. *Box try (VM)*, per row `i' < W` (math: `boxSample` with `p ← Big`):
   `y(i') = [i'=0](d₁ − Σ_c A_F[0,c] p_last,c) − Σ_w σ_{i'}(B_{0,w}) p_{i',w}
   − Σ_{k,c} σ_{i'}(H_k[0,c]) p_{i',k,c} + Σ_k Σ_j 2^j p_{(i'−je k) mod W, k, (0,j)}`
   (`pubShort`; the last term from `PE ++ PE` with the offset `(i' + W − je k)` rows, `je (t,0) = 2^t`
   by doubling, `je (t,1) = W − 2^t`); `z = digits of y(i')` (`dig`); `x_{i',w} = p_{i',w} +
   Σ_c σ_{i'}(T_{w,c}) z_c` (`realTrap`); `σ_{i'}` kept by one `σ_g` per row on the queues of
   `B₀`, `H_k[0,·]`, `T`. Coins: `p_last`, the `η` part, then the rows (`Bk` bits per
   coefficient, `val − 2^{Bk−1}` via `sub` of the constant with all coefficients `2^{Bk−1}`);
   their decoding is a bijection onto `famBig` (so the law is `uniformOfFinset Big` by
   `kbOf_Big`). Test `x ∈ famBall r`: `zabs c ≤ r ⟺ val(c + r) < 2^{Bk} ∧ val(r − c) < 2^{Bk}`
   (`2^{Bk+1} < q`), i.e. the digits `≥ Bk` of `x + R`, `R − x` vanish (`R` the element with all
   coefficients `r`); accumulate them in one register and test `= 0` with `eqb` (no wrap: fewer
   than `q` terms). Output `mpk ++ assemble x z` or `mpk ++ 0`; `|C| ≠ predLen` by two `drop`s and
   `eqb` with a blank register → `mpk ++ 0`.
4. *The machine*: an `XProg` (as `RingBTVW/Prog/KeyGenP.keyGenF`): `leP n` guard (`n` = length of
   the input with `|C| = L`; longer → `encodeTuple []`, **`KeyLongSpec`**), parse
   `encodeTuple [pw, msk, C]`, `natP`/`appendLaw_bits` templates, `coinsP` (`mB` coins), the VM
   code in a frame of `105` tapes (`MVM.law_compile`), output `frP`; **`KeySpec kbDc L`**.
5. *Costs*: a clock for compiled VM code (per instruction from `XProg.timeBoundT_frame` and the
   Mersenne `MersenneT` bounds; `rep` by `timeBoundT_loop_le_of_inv` with register-length
   invariants), `descLen` from `XProg.size`; estimate `≈ 2^214` steps at `Conf` (the `A^aut`
   stream passes of `autPKC`, `16 · 2^22 · 11` calls).

### Package G (attribute hiding of the implementation) — branch `t3/explut-g`

Files `PE/Impl/ExpLUT/AH/*` (namespace `AdvancedEncryption.ExpLUT.Prog`, in the aggregator) and
`PE/Impl/Game/OneSetup.lean`. Axioms `[propext, Classical.choice, Quot.sound]`.

**Main results.**
* `AH/Final.attributeHiding_Dc`: `AttributeHiding (univ w8) params impl` for every `impl` with
  `ImplSpec Dc kb L impl χc χc χfl` (`Setup` meets `SetupSpec Dc (χbin Dc)`, `Enc` meets
  `EncSpec Dc χc χc χfl`, `KeyGen` meets `KeySpec Dc kb L` **and `KeyLongSpec Dc L`** (empty word on
  predicate words longer than `L`, as RingBTVW's `key_long`), `Eval = evalMachineX`), from
  `CircularRingLWE.decision.HardAt (circParamsD Dc) kb'` with `64 · 2^256 · C ≤ 2^kb'`, given
  `KbCover kb 2^18500`, the flooding hypothesis `hflood` at some `ε_fl ≤ 2^{−148}`, and the
  reduction machines `RedMachine … C A Dm` (below). Simulator: `simMachine Dc` (`AH/Sim`: the
  encoding of `ctUW`, independent `unifW` entries; existence via `Machine.exists_finiteAlg'`, cost
  not bounded — it does not enter the definition).
* `attributeHiding_Dc_registry`: the same from `CircularRingLWE.decision.Holds`, with
  `strength_Dc : 1155 ≤ CircularRingLWE.decision.H (circParamsD Dc)` (`m = m_B + 1 + τ|J| ≤ 2^50`).
  **Required strength**: `kb' ≥ 262 + log₂ C`; `1155` bits cover `log₂ C ≤ 893`.
* Generic: `AH/Assembly.attributeHiding_of_reduction` (any `D`, `kb`, coverage, statistical
  hypotheses), `advantage_le` (`|adv| ≤ statW ε_fl + |rAcc − uAcc|`).

**Pieces.**
* `AH/Unif`: `unifW` is within `ε_U = N 2^{−K}` of uniform (`closeTo_unif_unifW`, every element has
  probability `≥ 2^{−NK}`, Bernoulli); `closeTo_setupLaw` (`epsSetup`), `ctUW` and `closeTo_ctU_ctUW`
  (`epsCT`), `mem_support_setupLawW`.
* `AH/Games`: `real_eq_gameV` (real experiment = `gameV` of `realVW`, keys `KGiW` = ideal key law
  on `Setup`'s support under `RealCovW`), `realVW_close` (to D's `hyb0`, `χbin = bitLaw`),
  `ideal_eq_gameV0` (unshifted challenge), `idealVW_close`, `gameV0_idealView_eq` (`ctU_shift`).
* `AH/RedGame`: the reduction's experiment `redGame` (secret `redSec`, view `view2`, keys `KGsim`
  = `redKeyLaw` with `T_sim`); `accept_red`: equal to the hybrid's for continuations rejecting
  `bad` (`KGsim_eq_KGiW` under `SimCovW`, `22 ≤ b`).
* `Game/OneSetup` + `AH/Chain1`: **a statistical change of the secret costs its distance once**
  (`closeTo_runWith_setup_one`; D's `chain` pays `|Attr| = 2^128` per step, which with P's
  `m̄ = 3NK + 408` would give only `2^{−20}`); `chain1`.
* `AH/Conf`: `Dc` (`setting Dc = confS` by `rfl`), coverage `realCovW_of`, `simCovW_of` from
  `KbCover kb coverBound`: real shift `≤ τn = 2^40`; `T_sim` shift `≤ W τ n D^b (B_R̂ + 2)` with
  `B_R̂ = (stepBound 1 1 1)^[16] 1` (`matBnd_simKey`, `progBnd_progOf`, `rowBnd_simTrap`,
  `vBound_iterate_le`, `simShift_rhat_le`). **The cover bound `2^18500` suffices.**
* `AH/Stat`: `delta1, delta5 ≤ 2^{−148}`, `deltaT ≤ 2^{−189}`, `epsSetup, epsCT ≤ 2^{−150}`,
  `statW Dc ε_fl ≤ 2^{−140}` for `ε_fl ≤ 2^{−148}`, `hstat_Dc`.

**Open (hypotheses of `attributeHiding_Dc`).**
1. ~~`hflood` at `χfl`~~ — **done in package G3** (`hflood_Dc`, `attributeHiding_Dc'`).
2. `KbCover kb 2^18500` for the KeyGen machine's `KeyBoxes` (P's `famBig`/`famBall` boxes over
   `PIdx (Wb Dc) (Jh Dc) …` have it by `add_mem_of_eq`; `Big` must be the image of fair bits).
3. **The reduction machine** (`RedMachine Dc kb L (circParamsD Dc) impl χc χc χfl C A Dm`): for every
   admissible `A` and distinguisher `Dm`, a machine `R` with
   `R.acceptProb (realLaw (circParamsD Dc)) = rAcc …`, `R.acceptProb (idealLaw …) = uAcc …` and
   `cost R ≤ C (cost A + cost Dm)²`. `rAcc`/`uAcc` = probability over `circReal`/`circUnif` that
   `redGame` followed by `DcB Dm` accepts. `R` must: decode the instance word (B's rows: plain rows
   = the columns of `B`, `d`, and the helper columns `(k, (1, i))`; key row `(i, j)` = helper
   `k = jhE j` column `(0, i)`, automorphism index `jList`; the law bridge is **done in package G3**:
   `realLaw_bind_decode`/`idealLaw_bind_decode`, so `R` only has to run `F ∘ decode D` on its input);
   draw `B̄⁽²⁾`, gadget columns of `B⁽²⁾`, `H⁽²⁾`, `d₂`, the flooding errors, `zr` (`redSec`); run
   `A` (`Lib/Machines/Inline`) answering select with `mpkEnc (view2 …).1`, key queries with
   `KGsim` (`EvalPK` over `bpOf (progOf C)` for `R̂_F` via `simKey` (Corollary 1 propagation),
   `simX`/`simTrap` (Lemma 11), one box try with `kb`, encoding `skEnc`), the challenge with
   `ctEnc (shiftCT ⌊q/2⌉ μ (view2 …).2)`; track `bad` (`authW`: `|C| = predLen ∧ output x = false`);
   output `Dm`'s verdict on `viewObs8` if not `bad`, `[false]` otherwise.

### Package G3 (flooding at `χfl`, circular law bridge) — branch `t3/explut-g3`

Files `SigabaNeoStd/Lattices/FloodRing.lean`, `SigabaNeoStd/Lattices/CircularRingLWEInst.lean`,
`PE/Impl/ExpLUT/FloodBound.lean`, `PE/Impl/ExpLUT/AH/Flood.lean`, `PE/Impl/ExpLUT/AH/CircBridge.lean`
(all in the aggregators). Axioms `[propext, Classical.choice, Quot.sound]`.

**Flooding (open hypothesis 1 of G, closed).**
* Library `FloodRing`: `floodRing N Q W` (one ring element, coefficients uniform below `W`; P's `χfl`
  is `floodRing (2^24) q (2^eFl)` by `rfl`, `χfl_eq`), `closeTo_floodRing_add` (`∑ⱼ |δⱼ|/W`),
  `closeTo_floodRing_add_le` (`N B / W` for `cnorm δ ≤ B`), `closeTo_pi_floodRing_add_le`
  (independent families: `#entries · N B / W`, via `Stat.closeTo_pi`). D's `floodLaw` is not
  rewritten as `Lattices.floodLaw` over a flattened index type: its four independent families are
  flooded one by one (`CloseTo.bind`), which needs no law equality.
* `FloodBound` (generic over `S : Setting (Negacyclic (ZMod Q) n)` with a `NormSpec` whose norm is
  `cnorm`): `closeTo_iidFam_floodRing_add`, `floodCount S Pos` (the flooded ring elements),
  `closeTo_floodLaw_add_le`, `cnorm_floodShift_le` (entries of `floodShift ē_b zr` are `±` sums of at
  most `|Wb|` entries of `ē_b`, possibly under `σ_{g_t}` (`nrm_σ`); norm `≤ |Wb| B_χ`, no factor `n`
  since `zr` is binary), **`hflood_floodRing`**: `hflood` at `ε = floodCount · n (|Wb| B_χ) / W`.
* `AH/Flood`: `εflDc = floodCount (setting Dc) Pos · 2^24 (m̄ · 16) / 2^eFl`,
  `floodCount_Dc_le : floodCount ≤ lhlCols`, **`εflDc_le : εflDc ≤ 2^{−249}`** (P's `flood_budget`,
  generic `natCast_mul_div_le_inv_pow`, `flood_budget_gen`), `εflDc_le_148`,
  **`hflood_Dc`** (exactly the hypothesis of `attributeHiding_Dc`), and
  **`attributeHiding_Dc'`** / **`attributeHiding_Dc_registry'`**: package G's results without
  `hflood` (remaining hypotheses: `ImplSpec`, `KbCover kb coverBound`, `RedMachine`, the
  constant `C`).

**Circular Ring-LWE law bridge.**
* Library `CircularRingLWEInst`: `CircularRingLWE.circRing p` (`σ ← polyOf χ_s`, uniform `aᵣ`,
  `eᵣ ← polyOf χ_e`, `(aᵣ, aᵣ σ + eᵣ − keyShiftRing p σ r)`), `realLaw_eq_circRing :
  realLaw p = (circRing p).map encodeRing`, `idealLaw_eq_uniform`; `pi_sum_bind`, `pi_unit_bind`,
  `pi_prod_bind`.
* `AH/Final`: `jList` now uses the explicit order **`jhE D : Fin (b·2) ≃ Jh D :=
  finProdFinEquiv.symm`** (was `Fintype.equivFin`, whose order is unspecified, so a machine could
  not know it), and `mCirc D = m̄ + K + 1 + K (b·2)` (same value). `strength_Dc` is unchanged
  (it holds for every `J`).
* `AH/CircBridge` (generic in `D : Dims`): row layout `ρ D : Fin (circParamsD D).rows ≃ Coord D`,
  `Coord D = BCol ⊕ Unit ⊕ (Jh × Col)`: plain rows (`plainE`) are, in order, the columns of `B`
  (`Fin (m̄+K) ≃ Wb ⊕ Fin K`, `bcolE`), `d`, then the plain helper samples `(k, (1, i))` at
  `m̄ + K + 1 + (i·2b + j)`, `k = jhE j`; key rows (`keyE`, the registry's `finProdFinEquiv`
  order) `m + (i·2b + j)` are the circular samples `(k, (0, i))`, `k = jhE j`, automorphism index
  `(jList D)[j]` (`get_jList`). `toPair`, **`enc D i = encodeRing (toPair D i)`** (the registry's
  word), `decode D` (choice on `encodeRing`; zero instance on other words), **`decode_enc`**.
  `keyShiftRing_eq` (the registry's key shifts are `σ_{g^{je k}}(s̄) G⁽¹⁾_{(0,i)}`, via
  `autσ_of_odd` and `G 0 (0, i) = 2^i`), `circRing_eq`, **`realLaw_circParamsD :
  realLaw (circParamsD D) = (circReal … (χcbd D) (χcbd D)).map (enc D)`** (`χcbd D` = CBD(16)
  coefficients, `χcbd_Dc : χcbd Dc = χc` by `rfl`), **`idealLaw_circParamsD :
  idealLaw (circParamsD D) = (circUnif …).map (enc D)`**, `realLaw_circParamsD_Dc` (with `circR Dc χc χc`),
  and for G2 **`realLaw_bind_decode` / `idealLaw_bind_decode`**: `(realLaw p).bind (F ∘ decode D) =
  (circReal …).bind F` (resp. `circUnif`). Hence a reduction machine whose output law on a word `w`
  is `F (decode D w)` with `F i = (redGame … i).bind (DcB Dm)` has acceptance `rAcc`/`uAcc`.
* Note for G2: `decode` is specified by choice; the machine parses `encodeSample`'s word
  (`encPair encBits (encList encNat)`: the public matrix, then the `rows · N` coefficients) and must
  be shown to agree with `decode` on encodings (`decode_enc`), e.g. by computing `toPair`'s inverse
  `ofPair` from the parsed coefficients (`ofPair_toPair`).

**Remaining for attribute hiding at `Dc`**: `KbCover kb 2^18500` for the KeyGen machine's boxes
(G's item 2), the reduction machine with its cost bound (G's item 3, package G2), the machines
meeting `ImplSpec` (package F).
### Package F3 (the `KeyGen` machine) — status (branch `t3/explut-f3`)

**Design: a register machine on ring words.** `KeyGen` is far too large for hand-plumbed tape
programs (nested loops five deep over `16` steps, `W = 2^22` coefficients, `b = 22` rounds,
`16K³` digit products per `Mul`), so it is written as code of a small VM whose semantics is a
pure function, and every routine is proved once at the level of lists of ring elements.

* `Lib/Lattices/ProgAlgo/Mersenne/VM.lean` — **`MVM.Code`**: `64` word registers;
  `op o d a b` for `o ∈ {add, sub, mul, neg, aut, rho, rot, dig}` (the Mersenne programs `addRMP`,
  `subRMP`, `mulRMP`, `notP`, `autMP` (`σ_{|b|}`), `rhoJP` (`X^{−|b|}`), `rotBP` (`2^{K−|b|}`),
  `digitRWP` (digit `|b|`)), each result **canonicalized** (`canonRP`); word moves `mv` (shift `|c|`
  bits), `mvR` (shift `N K` bits), `cp`, `drop`, `clr`, `tl`; `rep c body`, `seq`, `ifb`, `nop`.
  `compile : Code → XProg 105`, every instruction in a frame of its own tapes (operands loaded into
  work tapes cut to `N K` bits, so the semantics `exec N K` is **total and exact**).
  **`law_compile`**: the law of the compiled program on `enc N K w` is the point mass at
  `enc N K (exec N K c w)`; **`wf_compile`** (no `rep` body writes its counter, `Code.WFc`).
* `Mersenne/VMRing.lean` — reasoning tools: registers as **queues** `encL l` of canonical words
  (`mvR d s` moves the head of `s` to the tail of `d`); every `op` on canonical words is the ring
  operation (`canonW_add/sub/mul/neg/aut/rho/rot/dig`); `exec_writes` (footprints);
  `exec_rep_inv` (loops by invariants); one-instruction `exec_*` lemmas and the tactics `vm_step`
  (execute the head instruction of a `seq`) / `vm_simp`, which symbolically execute straight-line
  code (register names are `@[vmreg]` abbrevs, equalities decided by `Fin.reduceEq`). Routines clear
  their scratch registers so their effect is an exact update chain and composes by `rw`.
* `Mersenne/VMMat.lean` — **routines with exact specifications** (all on fixed registers
  `29 … 63`; callers use `0 … 28`):
  * `digAccC` (`exec_digAccC`): `acc += Σ_{i<K} e_i · digit_i(x)` over the next `K` stream elements;
  * **`mulPKC`** (`exec_mulPKC`): `EvalPK` of `Mul` with binary digits,
    `A'_{a,j} = Σ_{(r,i)} Σ_c Ad_{(r,j,i)}[a,c] · digit_{c.2}(A_{c.1,(r,i)})` (`mulPKm`), streaming
    the digit matrices once in the order of their word (`adL`), `(r, j, i, a, c)`; structure:
    `iBody` (four digit accumulations), the `ι` loop, the `j` loop (partial sums as a queue),
    the two `r` parts, a transposition (`tLoop`, `tOut`);
  * **`ginvMulC`** (`exec_ginvMulC`): `X · G⁻¹(Y)` (`ginvMulm`);
  * **`autMatC`** (`exec_autMatC`): `σ_k` on every entry, `k = |rKc|`;
  * **`autPKC`** (`exec_autPKC`): `EvalPK` of `Aut`: `H · G⁻¹(mulPK(σ_g^{m}(A), Aaut))`
    (`m = |rP|` applications of `σ_g`).
* `ExpLUT/Prog/KeyVM.lean` — the bridge to the scheme at the dimensions `D`: `matE_enc`,
  `digE_enc` (the words of `Words.lean` are the queues of the routines), `mulPK_eq_mulPKm`,
  `mul_ginv_eq`, `autMat_eq`, `aut_iterate` (`σ_g^{m} = σ_{g^m}`), **`autPK_eq`**;
  **`roundsPK_eq_bitChain`** (`A_j` after `t` rounds = `Aut_{g_s}` applied for the set bits `s` of `j`,
  increasing; the basis of item 1 below) and **`lutCoef_pow`** (`α_{k,L} = W⁻¹ Σ_u c_u μ^u`,
  `μ = σ_k(X^{2n−1})`; the basis of item 2).
  Axioms of all of these: `[propext, Classical.choice, Quot.sound]`.

**Plan for the rest of `KeyGen`** (not done):

1. *`A_j` without `W`-sized queues.* `roundsPK P A b j` applies `autPK_t` for the set bits `t` of `j`
   in increasing order (`roundsPK (t+1) j = autPK_t (roundsPK t (j − 2^t))` for `j ≥ 2^t`), so
   `lutPK = Σ_{j<W} smulPK(α_j, A_j)` is computed as one loop over `j` with a `b`-bit binary counter:
   for each `t` either `autPKC` (with `σ_{kf t} = σ_g^{2^t}`, `kf t = idx(2^t) = g^{2^t}`, `|rP| = 2^t`
   kept by doubling: `x := T; drop x p; drop x p; p := T; drop p x`), or skip the stream block
   `Aaut_t` (`drop` with a template of `16K³ N K` bits). Cost `≈ (b/2) W` `autPK` per step instead of
   `W`; no queue of `W` matrices. Needs the math lemma `roundsPK = ` the bit chain (pure algebra).
2. *Coefficients.* `α_j = W⁻¹ Σ_u X^{L(u)} μ_j^u`, `μ_j = σ_{g^j}(X^{−1}) = σ_g(μ_{j−1})`
   (`aut` with `|count| = g`), `X^{L(u)}` from the `14` bits of the table entry (LSB first, `ifb`/`tl`
   on the predicate word) times a queue of `X^{2^i}`; `W⁻¹ = 2^{K−b}` by `rot` with `|count| = b`;
   the last table gives `v_j` (`L(u) ∈ {0, 1}`). `smulPK(α, A) = A · G⁻¹(αG)` with `ginvMulC`
   (`αG` built by doublings `rot` with `|count| = K − 1`).
3. *Steps.* `16` steps: `mulPKC` with `A^in_i` (stream of `mpk`), then the `j` loop of 1–2;
   `15` `α`-steps and one `v`-step; result `keyPK`.
4. *Box try.* The coins `p ← Big` (a sampler parameter like `RingSampler`, giving the word of
   `kb.emb c` from `mB` fair bits), `y = d₁δ₁ − pubShort p` row by row (the blocks of `M_F`:
   `Σ_w σ_i(B_{0,w}) p_{i,w}`, `Σ_{k,c} σ_i(H_k[0,c]) p_{i,k,c}`, `− Σ_k Σ_j 2^j p_{i − je k, k, (0,j)}`,
   `A_F⁽¹⁾ · p_last` on row `0`), `z = gadDec y` (`dig`), `x = p − realTrap T z`
   (`σ_{idx i}(T_{w,c})`), the test `x ∈ Small` (a test-program parameter), the output
   `mpk ++ assemble x z` or the zero key.
5. *The machine.* An `XProg` around the VM phases: parse `encodeTuple [pw, msk, C]`, the length
   guard (**`KeyLongSpec`** of package G: `encodeTuple []` on predicate words longer than `L`),
   `|C| = predLen` else the zero key, the templates (`natP`), the coins, the framed output;
   **`KeySpec kb L`** for a `KeyBoxes Dc` value satisfying **`KbCover kb (2^18500)`** (package G;
   `famBig`/`famBall` boxes of `RingBoxes`).
6. *Costs.* Per-instruction clocks from the frames (`XProg.timeBoundT_frame` and the Mersenne
   `MersenneT` bounds), loops by `timeBoundT_loop_le`; estimate at `Conf`: the `Aaut_t` stream passes
   dominate, `16 · 2^22 · 11 · 2^184 ≈ 2^214` steps; `descLen` from `XProg.size` of the compiled code
   (a few thousand instructions, `105` tapes).

### Package G2 (the reduction machine) — status (branch `t3/explut-g2`)

**Correction of G's `RedMachine`.** A fair-coin machine with a bounded clock only produces dyadic
probabilities, and `2^K − 1` is odd, so no machine can draw `redSec`'s uniform `B̄⁽²⁾`, `H⁽²⁾`, `d₂`
exactly: `RedMachine` with `rAcc`/`uAcc` was not realizable. Now (`AH/RedGame`, `AH/Assembly`,
`AH/Stat`): `redSecW` (the same with independent `unifW` entries), `epsRed = (|BCol| + |Jh||Col| +
1) ε_U`, `closeTo_redGame` (the secret is drawn once: `closeTo_runWith_setup_one`), `rAccW`/`uAccW`
(acceptances of `redGameW`), **`RedMachine` asks for `rAccW`/`uAccW`**, `statW = statW0 + 2 epsRed`
(`advantage_le0` with `rAcc`, `advantage_le` with `rAccW`), `epsRed_le : epsRed Dc ≤ 2^{−150}`,
`statW_le` unchanged (`≤ 2^{−140}`). `attributeHiding_Dc'` keeps its statement.

**Plumbing (done, `AH/RedChain`, `AH/RedConst`).**
* `w8Codes` (codes of `univ w8`; `encAttribute_onto`), `redM8 = P ⨾ (inlined A ⨾ Post) ⨾guard Dm`,
  `acceptProb_redM8` (as `RingBTVW.acceptProb_reductionP`, with `postG`/`DcB`).
* The handlers' secret is **any finite type `Sig` with a map `f : Sig → RSec D`** (`RSec D` contains
  `Pos → ℕ`, so it has no fixed-length encoding) and a law `setupS i x` with
  `(setupS i x).map f = redSecW D χfl x i`; the handlers serve `spS = (specRedW …).comap f setupS`
  with `setupR D setupS instOf w = setupS (instOf w)` (`obs_oracleW_red`, via
  `Generic.runWith_comap`); `longKeys_red` (`predLen ≤ L`).
* **`RedComps D kb L impl χfl`**: `Sig`, `f`, `setupS`, `map_setupS`, `senc : FixedEnc Sig nS`,
  `IW`, `Ok`, `W`, `instOf`, the components `cs : Generic.Comps R (w8Codes senc) (spS …)
  (setupR …) IW Ok`, their bounds `cb : CompBoundsP cs L W`, the decoder `P` with
  `run_P : P.run (enc D i) = pure (dw (enc D i))`, `instOf_dw`, `iw`, the answer bound `La`
  (`≥` the lengths of `mpkEnc`, `skEnc`, `ctEnc`).
* **`redMachine_of_comps`**: `RedComps` ⟹ `RedMachine D kb L (circParamsD D) impl (χcbd D)
  (χcbd D) χfl C A Dm` for all `A`, `Dm`, `C ≥ rc.const` (`chainConst` of the chain).
* `RedComps.const_le`: `rc.const ≤ compBoundG 128 1 515 sP tP p R Sz2 L (11 Tc + 2^26 X²) t`
  (decoder states/time/tapes, components' sizes `Sz2`, components' time `Tc`, every length `≤ X`).
* **`attributeHiding_Dc_comps`**: `AttributeHiding (univ w8) params impl` from
  `CircularRingLWE.decision.Holds`, `ImplSpec Dc kb L impl χc χc χfl`, `KbCover kb coverBound`,
  `predLen ≤ L` and a `RedComps Dc kb L impl χfl` with `64 · 2^256 · const ≤ 2^1155`.

**Decoder (done, `Prog/RedDecode`).** The frame parser `decodeMX false K (2 · rows · N K) n` on the
registry's words modulo `2^K − 1` (generic `decodeW_encodeRingQ` for any `q ≤ 2^K`,
`coefW_eq_encRM`): `decR D n`, **`run_decR`** (`n ≥ encLen rows N K`), the state word
**`dwR_enc : dwR D (enc D i) = true :: wordsOf (toPair i).1 ++ wordsOf (toPair i).2`** (canonical
ring words, rows in the registry's order `ρ D`), `instR` (`decRM` of the blocks), **`instR_dwR`**,
`rowsD_eq : rows = mCirc D + K (2b)`, 14 tapes.

**Decoder and raw secret fixed (`AH/RedCompsR`).** `RawComps D kb L impl χfl` = the five component
programs on `R + 2` tapes for the raw secret (`rawEnc`, `rawSetup`, `rawF`), with state words
`IWR D` (= `dwR D (enc D i)`, `WR D = 1 + 2 rows N K` bits), and their bounds (`CompBoundsP cs L
(WR D)`); `RawComps.toRedComps` (decoder `decR D n`, `La = |mpk| + |sk| + |ct|`);
**`attributeHiding_Dc_raw`**: `AttributeHiding (univ w8) params impl` from
`CircularRingLWE.decision.Holds`, `ImplSpec Dc kb L impl χc χc χfl`, `KbCover kb coverBound`,
`predLen ≤ L`, `rc : RawComps Dc kb L impl χfl` and `64 · 2^256 · (rc.toRedComps nDc _).const ≤
2^1155`. **So what remains of G2 is exactly a `RawComps` at `Dc` (components `setupP`, `pubP`,
`keyP`, `chalP`; `authP := authWX`) and the numeric bound via `RedComps.const_le`.**

**Remaining for G2** (the components of `RedComps` at `Dc` and their bounds):
1. ~~`Sig`/`senc`/`setupS`~~ — **done** (`AH/RedSecret`): `RawSec D = Attribute w8 × CInst D × B̄⁽²⁾ ×
   H⁽²⁾ × d₂ × FloodV × zr`, `rawF` (= `attrN x`, `redPub`, `zr`, `redCore`, `fl`), `rawSetup`
   (`redSecW`'s draws), **`map_rawSetup`**, `rawEnc` (attribute bits ++ `instEnc` (canonical words of
   `toPair i`, the same words as the state word `dwR`) ++ coin words ++ `floodEnc` ++ `zrEnc`).
2. `setupP`: copy the instance words, sample with `unifCanonP` (package F), a `floodRing` sampler
   (`400` fair bits per coefficient, zero-padded: canonical), fair bits for `zr`.
3. ~~`authP`~~ — **done** (`Prog/AuthW`, `Prog/AuthWCost`, `Prog/AuthWX`): `authW8` (RingBTVW's
   `authBP` with the offset of `a ‖ z` and the entry bits prepended), `authAW_encAttr`,
   **`authWX hR : XProg (R + 2)`** (any `R ≥ 14`) with **`law_authWX`** (the bit `authW impl C x`
   when `Eval = evalMachineX`), `time_authWX` (`≤ 2^109` for `|C| ≤ 2^49`), `len_authWX` (one bit),
   `size_authWX` (`≤ 2^18`).
4. `pubP`, `chalP`: `mpkEnc`/`ctEnc` of `view2 …` (programming `a_t = B⁽¹⁾ Z_t + X^{w x_t} G`,
   `A₀`, `A^in`, `A^aut`, the shifted challenge) — VM code (`law_compile`) behind a front end.
5. `keyP` = `KGsim`: EvalPK over `bpOf (progOf C)` (F3b's routines), `simKey` (`R̂_F` by
   simulation-form propagation: `simMul`, `simAut`/`simPerm`, `simLut`), `simX`/`simTrap`
   (Lemma 11: `vRounds`, `ginvTop`), one box try with `kb` and the encoding `skEnc` — on the VM.
6. Bounds: times/lengths/sizes of all components (`CompBoundsP`, `compTimeP`), then
   `64 · 2^256 · compBoundG … ≤ 2^1155` (`RedComps.const_le`). The decoder at `Dc` is **done**
   (`Prog/RedDecode`): `nDc = encLen rows N K ≤ 2^120` (instance words), **`time_decR_Dc ≤ 2^270`**,
   **`states_decR_Dc ≤ 2^16`**, 14 tapes. Budget check (`compBoundG`): with `R ≤ 250` scratch tapes the
   factor `3^(14 + R + 30)` is `≤ 2^465`; states `2^{30}`-ish; slope `≤ 2^{t}` with `t` the log of the
   components' time (KeyGen-like `≈ 2^{215}`) — so `log₂ C ≈ 465 + 30 + 20 + 215 ≪ 893`.
   Kernel pitfall met: never state a bound on a closed term like `decT Dc` by unfolding at `Dc`
   (the kernel tries to evaluate `rowsD Dc` through `Nat.mul`); prove it for `D` and instantiate.

* **Orchestrator note (merge of F4):** Dec's VM is `SigabaNeo.Tape.RingVM` in `ProgAlgo/Mersenne/RingVM.lean`,
  `RingVMRing.lean` (renamed from `VM.lean`/`VMRing.lean`, which hold KeyGen's `MVM`). Dec lemmas that clashed with
  KeyGen/Setup/SimForm names got a `d` prefix: `devalC`, `dexec_evalC`, `dvecMul_ginv_apply`, `dxInvG_mul_monoX`,
  `duOf_toSt_toSym`, `dgetD_drop'`, `dmap_finRange_val`, `dlen_col`, `dlen_dig`.

### Automorphism rounds: executable template management (2026-11-24)

- Added `Prog/EncAutomorphisms.lean` and aggregate import.
- `autRoundP` installs both unary exponent templates, executes `autBlkP`, and clears the templates. `run_autRoundP` proves the complete store result, including consumption of all four input streams and restoration of template registers 7/8.
- `autBlocksP` defines consecutive rounds; WF and coin-freedom are proved for the entire program. Exact description size includes both literal templates: `36 + n * (autBlkP.size + 144 + 60 * 2^b)` when `j+n ≤ b`.
- Aggregate build passed, 9612 jobs (`/tmp/explut-aut-round-build.log`). Four exported theorems audited with only standard axioms (`/tmp/explut-aut-round-axioms.log`).
- Remaining next step: prove the complete `autBlocksP` stream invariant and identify output with `ct.caut`. The full Enc initialization/composition and clock, KeyGen/Dec/reduction machines and clocks, Submission and comparison remain unfinished.

### Full automorphism output and public-matrix row (2026-11-24)

- `EncAutomorphisms.run_autBlocksP` now proves the complete loop invariant for arbitrary consecutive blocks and four input suffixes, preserving output-register length and all other registers.
- `autBlocks_codec`, `autOutput_codec`, and `run_autBlocksP_ciphertext` identify the actual full phase with the scheme's encoded `caut` field and prove exhaustion of H/eh/Aaut/eaut streams. This closes the pending automorphism stream invariant above.
- Added `Prog/EncBPhase.lean`: `BPhaseOK` records machine templates; `run_bPhase_ciphertext` proves actual `mrowP` computes encoded `ct.b` and consumes B/eb streams. The zero gadget word and secret-word lengths are explicit hypotheses.
- Aggregate build passed (9614 jobs, `/tmp/explut-aut-b-build.log`); new loop, codec, full automorphism phase and b-phase theorems have only standard axioms (`/tmp/explut-aut-b-axioms.log`). No sorry, native_decide, or added axioms. `git diff --check` passed.
- Next: place these four verified phases (b, helper, automorphism, tail) in a common concrete store, build initialization from public/coin queues, and prove complete Enc execution and its clock. Existing `EncFront.program` is still conditional on an MVM core; it must be connected or replaced by the concrete Prog pipeline, not treated as a completed Enc implementation.
- The full goal remains open: Enc clock and sampler/front connection, KeyGen/Dec/reduction machines and clocks, Submission, RingBTVW comparison, final audit.

### Common-store encryption core (2026-11-24)

- Added `Prog/EncCore.lean`, imported by aggregate. `encCoreP D : Prog 321` runs the actual b/helper/automorphism/tail machines in ciphertext order.
- All phases share only tape 0. Private intervals: b 1..65, helpers 66..133, automorphisms 134..217, tail 218..320. `phaseSlot_inj` and `phaseSlot_separate` prove embeddings and separation without computational axioms.
- `phase_view_after` proves the exact later-phase view after executing an earlier machine: only output tape 0 changes. `run_encCoreP_output` proves the combined core output equals the four local executions, each receiving the previous output and its own preserved inputs/templates/scratch.
- WF, coin-freedom, and exact description-size formula of the combined concrete program are proved.
- Aggregate build passed (9616 jobs, `/tmp/explut-core-build.log`); five theorem axiom checks contain only standard axioms (`/tmp/explut-core-axioms.log`). `git diff --check` passed; no new sorry/native_decide/custom axiom.
- Important boundary: common-store execution is connected, but initialization from parsed public/coin words and the final `ctEnc` result theorem remain open, as does the clock. Existing front uses 105 tapes; the concrete core now uses 321, so the front must be generalized/embedded and its cleanup proved. Do not claim EncSpec completion from the core decomposition alone.
- Next implementation: construct initialization using fixed-size stream splitting and copies into these private intervals, literal templates (including zero output capacity), and connect each phase's existing scheme-output theorem to `run_encCoreP_output`. Then connect sampler/front law and clock. KeyGen/Dec/reduction, Submission and comparison remain open.

### Concrete input loader and initialized core (2026-11-24)

- Added `Prog/EncInit.lean`, imported by aggregate. Uses 326 tapes: core 0..320, coin stream 321, public/plaintext stream 322, loader template/scratch 323..325.
- `readFieldP` installs a literal length template, overwrites the destination with the next fixed-size field using `mvP`, consumes the source, and clears its template. `run_readFieldP` proves the complete store update; `run_readFieldP_encoded` proves exact encoded-field extraction. Loader scratch is preserved blank.
- `InitOp` has read/copy/literal instructions, compiled to actual Prog instructions; `run_initProgram` proves the entire instruction-list evaluator correspondence. WF, coin-freedom, clean-scratch preservation, and exact size are proved.
- `publicInitOps` consumes B,H,a,A0,Ain,Aaut,d,attribute,message in wire order and creates required copies. `coinInitOps` consumes s,eb,eh,eaut,ein,edin,e0,em in sampler order and creates copies. `templateInitOps` installs all four phases' templates, canonical ring-one constants, rotation templates and ciphertext-sized output register.
- `initializedCoreP` actually sequences this loader and the 321-tape core embedded in 326 tapes. Exact run, WF, coin-free, and description-size theorems proved.
- Aggregate build passed (9618 jobs, `/tmp/explut-init-build.log`); six exported theorem audits use only standard axioms (`/tmp/explut-init-axioms.log`). No new sorry/native_decide/axiom; diff check passed.
- Remaining immediate proof: starting with blank core/scratch and actual encoded coin/public streams, prove the resulting `initEval` state satisfies BPhaseOK, HelperOK, AutBlockOK, TailOK/TailInput and all phase data equalities. The existing generic loader theorem alone does not establish those specialized invariants or EncSpec.
- Useful next facts: `encRM_zero N K` (VMRing) identifies the loader's zero word with `wd D 0`; `τOf` reads local 6+i%8 and `tCb1` maps these to tail17..24, matching initializer. Indexed-codec lengths need explicit `e.length a` terms, not blanket backwards rewrites (dependent-motive failures). Front sampler still uses 105 tapes; generalize/frame it to this 326-tape initialized core and clear nonoutput tapes, then prove clocks and finish the remaining KeyGen/Dec/reduction/Submission/comparison obligations.

### Initialization from actual encoded scheme inputs (2026-11-24)

- Added `Prog/EncInitSpec.lean` and aggregate import.
- `publicWrites` and `coinWrites` specify the intended data placement using literal field words, independent of stream splitting. `eval_publicInitOps` and `eval_coinInitOps` prove complete store equalities from actual mpk/attribute/message and `encCoinWord` inputs, including all copies and exhaustion of source streams.
- Generic NoRead framing lemmas show literal/copy instruction lists preserve either input stream and commute with updates to it; these support exact composition of the two loaders.
- `loadedState` is declared data placement followed by constant templates. `run_encInitP_loaded` proves the executable initializer equals this state for actual input words.
- `encStart` places coin/public words on 321/322 with every other tape blank; `preparedState` is the fully initialized scheme state with initially blank core. `run_encInitP_start` proves the actual initializer reaches it, removing all source inputs.
- Build passed (9620 jobs, `/tmp/explut-init-spec-build.log`); four exported theorem audits use only standard axioms (`/tmp/explut-init-spec-axioms.log`). No warnings in the new module, no sorry/native_decide/custom axiom, diff check passed.
- Next: prove BPhaseOK/HelperOK/AutBlockOK/TailOK/TailInput and data facts for slices of `preparedState`, combine with existing phase theorems and `run_encCoreP_output` to get actual `ctEnc` output. The explicit write lists now eliminate all stream slicing from that remaining proof. Then connect front/sampling, cleanup and clock; other algorithms and Submission/comparison remain open.
- Proof notes: normalize `sourceTape` in input hypotheses with `simp [sourceTape]`, not `simp only` (Fin numerals otherwise block matching). Use fully instantiated `takeD_encoded_append`/`drop_encoded_append` lemmas for semireducible scheme matrix types. Disable `List.drop_drop` while proving individual reads. Do not unfold `takeD` globally, which expands 128 attribute bits before applying the attribute-length lemma. Final store equality uses `simp [Function.update_apply, hi]` to eliminate overwritten source entries.

### Complete deterministic Enc execution proved (2026-11-24)

- Added `EncReady.lean`: `readyCore = preparedState ∘ coreTape`; all four phase template/scratch invariants, b/helper/aut input data, and ciphertext-sized zero output are proved from the actual initializer's declared writes.
- Added `EncReadyTail.lean`: each tail data field and rotation template is proved separately, assembled into `ready_tailData : TailInput ...`. This avoids a giant kernel proof term.
- Added `EncOutputState.lean`: replacing output tape 0 preserves BPhaseOK/HelperOK/AutBlockOK/TailOK/TailInput. `τT_output` preserves all rotation templates.
- Added `EncRun.lean`: exact lengths for b/h/aut encoded blocks, and `run_ready_b`, `run_ready_helper`, `run_ready_aut` connect actual initialized phase states (with arbitrary output register) to shifted scheme ciphertext fields.
- Added `EncComplete.lean`: `run_ready_tail`, output-length/concatenation lemmas, `run_encCoreP_ciphertext`, and `run_initializedCoreP_ciphertext`. The last theorem executes the actual 326-tape initialized core from `encStart (encCoinWord r) (mpkEnc mpk ++ (encAttribute x ++ [μ]))` and proves output tape 0 is exactly `ctEnc (encrypt ... r)`. Hypotheses are `0 < b`, `2 ≤ N`, and `wSt * 128 ≤ 2*N`; no abstract core/run/spec premise remains in this deterministic theorem.
- `EncInit.rotationLength` now uses an explicit size comparison before subtraction, with `rotationLength_eq` proving equality to the original truncated subtraction. This is semantically identical for all D. It prevents kernel deep-recursion failures from reducing a symbolic natural minus a large numeral during template lookup proofs. `τT_tailSlot` also isolates the lookup from store-content reduction.
- Aggregate imports `EncComplete`. Full build passed (9630 jobs, `/tmp/explut-complete-enc-build.log`). Main end-to-end deterministic theorems, tail data and rotation-length equivalence audited with only standard axioms (`/tmp/explut-complete-enc-axioms.log`). Diff check passed, no new sorry/native_decide/custom axioms. No active build sessions remain.
- Next remaining Enc work: frame/generalize the existing 105-tape parser+sampler (`EncFront.prepare`, `law_prepare`) into the 326-tape core's input layout, clean all nonoutput tapes, and prove its distribution/EncSpec plus time bounds. The concrete deterministic output theorem is complete, but the randomized/full-machine/clock obligations are NOT yet complete. KeyGen/Dec/reduction machines+clocks, Submission, RingBTVW comparison and final overall audit remain open.
- Useful proof detail: `update_bView` is a generic opaque-store lemma avoiding expansion of all initialized data when proving a redundant output update. Apply generic lookup/equality lemmas with explicit types; Fin numeral coercions sometimes prevent `rw` matching, so first bind a typed equality (`have ht : ... := τT_tailSlot ...`). Do not return to full-store `rfl`/`change` reductions for those identities.

### Randomized Enc machine and concrete EncSpec completed (2026-11-24)

- Added `Prog/EncPipeline.lean`: generic concrete tape eraser and `eraseNonoutput` leave exactly `inputStore 0 ciphertext`; `cleanCoreP` sequences this after the actual initialized core. `relocateP` moves sampler outputs 0/1 to core input streams 321/322 and clears 0/1.
- `widePrepare` frames the existing 105-tape parser/sampler into 326 tapes. Restriction/embedding lemmas and `law_widePrepare` prove its exact distribution. `encryptionP` sequences parser/sampler, relocation and cleaned core; `law_encryptionP` proves the exact output store distribution with no abstract core argument. All WF obligations proved.
- Added `Prog/EncMachine.lean`: `frameCiphertextP` wraps the raw ciphertext in `encodeTuple [ctWord]` as EncSpec requires; its store law and WF are proved. `encProgram` sequences it with the full randomized encryption pipeline. `law_encProgram` is exactly `encLawW` mapped to framed output stores.
- `encInputLength` is the exact constant framed input length; `encMP D η L e = (encProgram ...).toMachineT 0 0 (encInputLength D)` is an actual finite-clock compiled machine. `encSpec_encMP` proves the generic EncSpec under sampler/dimension hypotheses. `time_encMP` exposes the exact compiler `totalTimeT` clock.
- Added `Prog/EncMachineConf.lean`: `EncConf.encMachine := EncW.encMP Dc 16 6 eFl`; `EncConf.encSpec_encMachine` proves `EncSpec Dc χc χc χfl encMachine` with all parameter hypotheses discharged. Aggregate imports this module.
- Aggregate build passed (9636 jobs, `/tmp/explut-enc-machine-build.log`). Randomized law, generic EncSpec, concrete EncSpec, and clock equality audited with only standard axioms (`/tmp/explut-enc-machine-axioms.log`). No new sorry/native_decide/axioms; diff check passed. No live sessions remain.
- Boundary: Enc's actual machine and law/specification are now complete. Its compiler clock is explicit and finite; a useful numerical time/description-length bound for comparison is still unproved. Remaining full goal: those Enc cost bounds, KeyGen/Dec/reduction machines and clocks, Submission and comparison against the dual-use `2^818` cost, and final audit. Do not confuse the explicit `totalTimeT` expression with the requested numerical cost result.
- Proof tips: avoid `simp [io2, Fin.ext_iff]` together (simp loop). Use separately proved val=0/1 iff index=0/1. For PMF bind/map compositions, `rw` can fail on semireducible scheme types; the working proof is `(congrArg (PMF.bind law) (funext hrun)).trans (PMF.bind_pure_comp _ _)`.

### Full Enc compiler clock and cost verified (2026-11-24)

- The actual production `encryptionP` now normalizes its relocated coin/public queues before the initialized core. `normalizeInputsP` truncates/pads to the exact schema lengths with carry/take operations and erases other tapes; `run_normalizeInputsP_start` proves valid encoded inputs are unchanged. The exact randomized law and concrete `encSpec_encMachine` were rebuilt for this changed production machine.
- Added `EncNormalize`, `EncNormalizeTime`, `EncPrepareTime`, `EncOutputTime`, and `EncTimeConf`. Parser bounds use four framed decoders; loose sampler bounds allow arbitrary initial tapes up to `2^104`. Normalization bridges the resulting bound to the core's `2^99` invariant. Output framing uses exactly the production program's sequence tree.
- `EncConf.descLen_encMachine` proves description length at most `2^744`; `time_encMachine` proves the actual compiled machine clock at most `2^817`; `cost_encMachine_lt` proves its total cost strictly below `2^818`. This is an Enc-only result, not the full PE/Submission comparison.
- Generic `XBound.seq/frame/total` and the generic machine cost bridge avoid kernel expansion of the enormous concrete program. Keep these abstractions when composing remaining machines. Exact sequence association matters for compiler time expressions.
- Aggregate build passed (9666 jobs, `/tmp/explut-enc-full-clock-build.log`). Exact concrete EncSpec, description bound, time bound, cost bound, and normalization identity were audited: only `propext`, `Classical.choice`, `Quot.sound` (`/tmp/explut-enc-final-axioms.log`). Source scan found no sorry/native_decide/custom axiom in Enc modules; `git diff --check` passed.
- Remaining: actual complete KeyGen and Dec machines with laws and numerical costs, safety reduction machines/costs, Submission, full RingBTVW comparison, final audit. KeyCoins already identifies the fair-coin decoding law with the uniform big box; KeyTryVM provides queue decoding, inner product, automorphism, gadget reconstruction, small-box test and digit routines. Their composition into a complete rejection-sampling KeyGen remains to be built. No live build sessions remain. All work remains uncommitted.

### KeyGen coin decoder execution/distribution bridge (2026-11-24)

- Added `Prog/KeyCoinVM.lean` and aggregate import. `coinDecodeStart` specifies the six initialized decoder input registers over an arbitrary ambient register state. It is a state specification, not an executable initializer.
- `exec_coinDecodeStart` proves the actual `decQC` execution consumes all supplied coins and emits the enumerated `coinDec` family. `map_uniformList_exec_coinDecodeStart` identifies its output queue distribution with the encoded uniform distribution on `(kbOf D B hB r).Big`.
- `wf_compile_decQC` proves the actual compiled decoder well formed; `law_compile_coinDecodeStart` proves the compiled tape program's output projection exactly equals the encoded decoded family, for each correctly sized coin word and initialized VM store.
- Aggregate build passed (9668 jobs, `/tmp/explut-key-coin-vm-build.log`). Four new theorems audited with only standard axioms (`/tmp/explut-key-coin-vm-axioms.log`); diff check passed. No live sessions remain.
- Boundary: this closes the connection between previously separate coin-distribution and decoder-execution results. Executable front initialization/sampling, key-map and trapdoor-shift composition, acceptance test, bounded retries, full KeyGenSpec and numerical clock remain. Dec/reduction/Submission/comparison remain open as before.

### Executable key candidate sampler and initialization (2026-11-24)

- Added `Prog/KeySample.lean`, imported by aggregate. `initP` copies the coin input from tape 0 to the VM coin register and installs every other VM tape using literal writers. `run_initP` proves it reaches the exact encoded `coinDecodeStart` state from any store. Initialization is now executable rather than a state premise.
- `decodeP` sequences this initializer with `compile decQC`. `candidateP` first runs a framed `coinsF` for `nPI D * D.N * B` fair bits, then runs `decodeP`. All stages are well formed.
- `law_candidateP` proves the full store distribution starting from a blank workspace; `law_candidateP_queue` proves its output register has exactly the encoded uniform big-box distribution. The module can be framed into a larger machine to preserve external public-key/trapdoor state. It is the pre-rejection candidate stage, not a full KeyGen machine.
- Aggregate build passed (9670 jobs, `/tmp/explut-key-sample-build.log`); initialization, WF, full-store law and queue law audited with only standard axioms (`/tmp/explut-key-sample-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: implement and connect the public-map/gadget/trapdoor-shift computation and exact small-box acceptance predicate, then retries and final key encoding. Existing `exec_tstC` only computes the sum of high binary digits; its equivalence to membership in the configured small box is not yet proved. Candidate sampler clock/size must charge literal initialization and sampling lengths. Dec/reduction/Submission/full comparison remain open.

### Exact small-box acceptance predicate (2026-11-24)

- Added `Prog/KeyBoxTest.lean`, imported by aggregate. Reuses the existing generic `SigabaNeoStd.Lattices.BallTest` lemmas rather than duplicating the centered-residue arithmetic.
- `sum_tstD_eq_zero_iff` proves the actual VM high-digit sum vanishes iff the tested ring element has coefficient norm at most `r`. Hypotheses explicitly include `2*r < 2^B`, `2^(B+1) ≤ q`, and `2*(K-B) < q`; the last excludes modular cancellation of test bits. The proof indexes both shifted digit streams by range × Bool and applies `sum_binaryDigit_eq_zero_iff`.
- `exec_tstC_eq_zero_iff` connects this predicate to the existing executable VM accumulator with zero initial accumulator. Added actual Boolean test `ballTestC := tstC; eqb rTx rFa rZ`, WF and `exec_ballTestC`, whose output is exactly `[decide (cnorm x ≤ r)]`.
- `small_iff_tstD` characterizes the family box by per-coordinate tests. `small_test_conditions_Dc` discharges separation/no-cancellation for concrete parameters and `kbDc_small_iff_tstD` specializes to the opaque configured box. Large numerical powers are compared via exponents, not expanded.
- Aggregate build passed (9674 jobs, `/tmp/explut-key-box-test-build.log`). Five key predicate/execution/WF/concrete-box theorems audited: only standard axioms (`/tmp/explut-key-box-test-axioms.log`). No new sorry/native_decide/custom axiom; diff check passed. No live jobs remain.
- Remaining immediate KeyGen work: sequence per-coordinate tests over the transformed short-family queue, compute the public map/gadget decomposition/trapdoor shift, construct the final accepted key and rejection/retry handling; full machine and numerical cost. The single-element Boolean test is implemented, but the complete family test loop and full KeyGen are not. Dec/reduction/Submission/full comparison remain open.

### Streaming whole-family rejection test (2026-11-24)

- Added `Prog/KeyBoxLoop.lean`, imported by aggregate. `BoxTestReady` records the radius/bit-count/zero templates. `boxLoadC` consumes one canonical ring word from rQa and resets the per-element accumulator. `boxBodyC` calls the verified `ballTestC`, retaining the rejection latch rDq on success and setting it to `[false]` on failure.
- `boxQueueC` clears the latch and runs the body for the length of rQc. `exec_boxQueueC` proves the queue is exhausted and the latch is blank iff all elements meet the coefficient-radius bound. The loop invariant tracks the remaining queue and acceptance of the processed prefix; all templates are preserved. Per-element accumulator reset means the existing `2*(K-B) < q` bound suffices independently of family length.
- `exec_boxQueueC_family` connects the enumerated queue to `(kbOf D B hB r).Small`. `boxFamilyC` converts the latch to a Boolean in rTx, and `exec_boxFamilyC` proves output exactly `[decide (p ∈ Small)]`. Full WF proved.
- Aggregate build passed (9676 jobs, `/tmp/explut-key-box-loop-build.log`); five loop/body/family/Boolean/WF audits use only standard axioms (`/tmp/explut-key-box-loop-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Important integration requirement: the test consumes rQa. Preserve the transformed candidate/key material elsewhere before testing. rDq is used as the rejection latch (the sampler's original output register must likewise be copied first). Input rQc must contain one zero per family entry; radius, bit counts, zero and `[false]` templates are explicit `BoxTestReady` prerequisites.
- Remaining: compute public map, gadget decomposition and trapdoor shift from sampled p; initialize/compose the family test with that transformed queue; final key encoding and rejection/retry semantics; KeyGen numerical clock/size. Dec/reduction/Submission/full comparison remain open.

### Real-trapdoor coordinate correction and single-try specification (2026-11-24)

- IMPORTANT CORRECTION to earlier continuation notes: `Prog/Words.keyLawW`, `KeyGen.keyGenLaw`, and `BoxSampler.boxSample` specify exactly ONE try of box rejection, returning a zero key on abort (and also on invalid predicate encoding). They do not specify retries. Do not implement retries, as that changes the required output distribution. Earlier mentions of retries in this plan are superseded by this source-backed requirement.
- Added `Prog/KeyShift.lean`, imported by aggregate. `autDotC` saves the count in register 56, runs `autQC`, restores the count, and runs `ipC`. `exec_autDotC` proves both row queues are consumed and the accumulator becomes `acc + sum (aut a_i * b_i)`. Restoring the counter is necessary because `autQC` consumes it.
- `corrected_inl` proves `p - realTrap T z` equals addition of the automorphic inner product on the trapdoor coordinates; `corrected_inr` proves other coordinates unchanged. `zip_aut_ofFn` connects ordered queues with the finite sum. `exec_autDotC_corrected` proves actual VM output equals the corrected coordinate, with all index/automorphism hypotheses discharged for Dims.
- Aggregate build passed (9678 jobs, `/tmp/explut-key-shift-build.log`); five WF/kernel/correction/execution audits use only standard axioms (`/tmp/explut-key-shift-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Integration: autDotC uses register 56 for saved length, consumes rQa/rQb/rQc, and accumulates into rIa. It requires an exponent-length template in rQk, a zero ring word in rZ, and the candidate coordinate preloaded in rIa. The full row/family loader/composition is not yet done.
- Remaining KeyGen: actual public map computation and gadget decomposition, full correction traversal, preserve/encode key material while testing, single-try accept/zero-key branch, input validation/front, numerical costs and KeySpec. Dec/reduction/Submission/full comparison remain open.

### Streaming target-minus-public-map gadget decomposition (2026-11-24)

- Added `Prog/KeyDecompose.lean`, imported by aggregate. `decomposeC` subtracts rIa (public-map row) from rQx (target row), then runs existing `digQC`. `exec_decomposeC_key` identifies the output with the corresponding row of `gadDec (keyTarget - pubShort p)`.
- `decRowLoadC` consumes one word from each input queue and reloads the digit counter from rQk; `decRowBodyC` appends that row's digits to rDq. `decRowsC` clears the output and repeats for the rQc row count. `exec_decRowsC` proves both streams are exhausted and output is exactly the concatenation of their row differences' digits.
- `rows_digits_gadDec` identifies this full queue ordering with row-major/digit-major gadget coordinates. WF proved for the single row and full traversal.
- Integration prerequisites: rQa target stream, rQb public-map stream, rQc one zero per row, rQk K zeros, rB1 `[false]`, rZ canonical zero. Output is rDq. The loader and digit core use rQx/rIa/rY/rZq/rU/rCK/rTd as scratch. The public-map values are still required input; this module does not compute `pubShort` itself.
- Aggregate build passed (9680 jobs, `/tmp/explut-key-decompose-build.log`); row specification/body/full loop/order/WF audits use only standard axioms (`/tmp/explut-key-decompose-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Remaining: public-map machine and its input layout, full trapdoor correction traversal, actual KeyGen front and single-try accepted/zero-key branch, KeySpec and numerical costs. No retries (see preceding specification correction). Dec/reduction/Submission/full comparison remain open.

### Sparse public-map row execution (2026-11-24)

- Added `Prog/KeyPublicRow.lean`, imported by aggregate. `pubShort_backRow` removes the redundant sum over all predecessor rows by `sum_mulRow`: each helper contributes only `M.backRow i k` to the negative gadget term.
- `signedDotC` computes a positive inner product, saves it in register 13, loads negative streams from 10/11 and count from 12, computes the negative product, and subtracts. WF and exact `exec_signedDotC` proved.
- `PublicPos` indices are `Wb ⊕ (J × Col τ) ⊕ Col τ`. Explicit `publicPosCoeff/Input` and `publicNegCoeff/Input` define the sparse streams; the AF coefficients are zero outside row0. `public_streams_eq` proves their signed enumerated inner products equal `pubShort`. `exec_signedDotC_public` connects the actual VM output to the public-map row for those explicit stream encodings.
- Register contract: positive rows rQa/rQb and count rQc; negative rows 10/11 and count12; rZ zero; output rIa; register13 saves the positive sum. Encoded public-key/candidate loading and automorphism generation of these stream words are still outstanding. Do not treat explicit stream input hypotheses as a completed end-to-end public-map machine.
- Aggregate build passed (9682 jobs, `/tmp/explut-key-public-row-build.log`); sparse identity, kernel execution/WF, stream identity and actual public-row output audited with only standard axioms (`/tmp/explut-key-public-row-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: executable stream generation and indexed extraction from public/candidate queues, full public-map traversal, full correction traversal, front and single-try accepted/zero-key branch, KeySpec/costs. Dec/reduction/Submission/full comparison remain open.

### Executable candidate-coordinate gathering (2026-11-24)

- Added `Prog/KeyGather.lean`, imported by aggregate. `fetchRingC N K j` preserves source register0, constructs bit offset `j*(N*K)` using `natC` binary doubling in register2, copies the source to register1, drops the prefix and reads the selected ring word into register3. Exact extraction and preservation/WF proved.
- `gatherAppendC/gatherC` append a static index list's entries into register4. `exec_gatherC_family` proves extraction from an explicitly enumerated encoded family equals the selected family coordinates, including arbitrary repeated/reordered selections.
- `positiveSelection/negativeSelection` implement the actual public-row candidate indices. `positiveGatherC/negativeGatherC` generate the `publicPosInput` and `publicNegInput` streams from the single encoded candidate vector; the latter uses `helperMap.backRow`. Both execution specifications and WF proved. The offsets depend only on dimensions/row indices, not on secret values.
- Register contract: source0 preserved; scratch1/2/3; output4; rB1 `[false]` and rZ canonical zero required and preserved. All registers outside1..4 are preserved by gathering (proved for append stage; clear4 is explicit). This enables copies into the signed-dot input registers without destroying candidate data.
- Aggregate build passed (9684 jobs, `/tmp/explut-key-gather-build.log`); fetch/family/positive/negative/WF audits use only standard axioms (`/tmp/explut-key-gather-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Remaining: public coefficient stream generation from encoded MPK/EvalPK (with automorphisms), composition with candidate gathers and signed dot for all rows, complete correction traversal and key assembly, single-try accept/zero-key branch, full KeySpec/costs. Gather time/size must charge source copies and offset construction; no numerical cost bound yet. Dec/reduction/Submission/full comparison remain open.

### Bounded row automorphisms and B/H coefficient gathering (2026-11-24)

- Added `Prog/KeyRowAut.lean`, imported by aggregate. Important cost correction: raw `g^i` unary templates in the earlier generic correction theorem are unsuitable for the numerical target. `rowExponent D i = g^i mod (2*N)` is positive, odd, less than `2*N`, and induces exactly the same scheme automorphism (`aut_rowExponent`). Keep the old theorem as a generic API, but use `exec_autDotC_corrected_bounded` for the production correction pipeline.
- `autGatheredC` loads the gathered queue and builds length/exponent counters via `natC`, applies `autQC`, and returns the transformed queue in register4. `gatherAutC` connects coordinate extraction and automorphism; exact family execution and WF proved. `gatherC_preserves` exports the full gather preservation result.
- `BHSource`, `bhSource`, `BHRow`, and `bhSelection` give explicit B/H field enumeration and row0 selections. `gatherBHC` generates the actual automorphic B/H coefficient stream, with `exec_gatherBHC` and WF. The source is the encoded enumerated B/H family; connecting it to the MPK wire codec remains necessary.
- Register contract: source0; gather scratch1..4; aut stage uses rQa/rQc/rQk/rQx/rQy, rB1 and rZ templates. Output4. Preserve candidate and other fields in registers outside those sets or in an external frame.
- Aggregate build passed (9686 jobs, `/tmp/explut-key-row-aut-build.log`). Six bounded-exponent/semantic/gather/correction/BH/WF audits use only standard axioms (`/tmp/explut-key-row-aut-axioms.log`). No new sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Remaining: B/H source codec bridge, AF first-row/zero coefficient stream and fixed negative gadget coefficients, compose all row inputs with signedDotC, all-row traversal, correction/key assembly/accept-or-zero front, KeySpec and numerical costs. Use reduced exponents throughout new production loaders; also review EvalPK input templates for the same issue. Dec/reduction/Submission/full comparison remain open.

### Public-key B/H codec and executable prefix bridge (2026-11-24)

- Added `Prog/KeyBHCodec.lean`, imported by aggregate. `matE_enc_product`, `hEnc_product`, and `bhSource_codec` prove that the source enumeration is exactly the B and H codec fields in wire order. `mpkEnc_bhPrefix` gives the actual MPK prefix decomposition.
- `prefixC` constructs the prefix length using binary doubling, extracts it with `takeC`, and stores it in register0. Exact execution, WF, and preservation outside0/2/3 proved. `bhPrefixLength` is data-independent.
- `mpkBHC` composes prefix extraction with `gatherBHC`; `exec_mpkBHC` starts from the actual `(mpkEnc D).enc mpk`, producing the automorphic B/H coefficient queue in register4. Requirements: rB1 false bit and rZ canonical zero. Source0 becomes the B/H prefix; preserve a separate full MPK for subsequent loaders.
- Lean proof detail: keep `(setting D).τ` in intermediate BHSource lists to avoid ill-typed rewriting under implicit transparency. The tuple-pattern `bhSource` must be simplified on inl/inr rather than replaced by `Sum.elim` via definitional equality.
- Aggregate build passed (9688 jobs, `/tmp/explut-key-bh-codec-build.log`). Five codec/prefix/execution/WF axiom audits use only propext, Classical.choice, Quot.sound (`/tmp/explut-key-bh-codec-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Remaining: AF first-row/zero coefficient stream, fixed negative gadget coefficients, compose full public-row inputs and signed dot, all-row traversal, correction/key assembly and single-try accept-or-zero front, KeySpec and numerical costs. Review EvalPK exponent templates for reduction modulo2N. Dec/reduction/Submission/full comparison remain open. Goal is not complete.

### Positive public-row coefficient completion (2026-11-24)

- Added `Prog/KeyCoefficients.lean`, imported by aggregate. `matL_row0_prefix` connects the actual evaluator matrix queue to its row0. `appendAFC` appends that row on the scheme's first row, or constructs an equally long zero word with binary doubling otherwise. Exact generic execution, WF, and `encL_zeros` proved.
- `publicPosCoeff_list` identifies the B/H plus conditional AF queue with the scheme's sparse positive coefficients, including its precise sum-type enumeration. `exec_appendAFC_public` specializes the actual append code to keyPK.
- `positiveCoeffC` composes `mpkBHC`, loading the evaluator matrix from register8, and the conditional append. `exec_positiveCoeffC` starts from actual encoded MPK on0 and encoded `matL (keyPK ...)` on8, and produces the complete positive coefficient queue on4. The saved evaluator matrix and rB1/rZ are preserved through the B/H generator (`mpkBHC_preserves_inputs`). The EvalPK execution front itself must still supply the register8 hypothesis.
- Register contract: inputs0 MPK and8 evaluator matrix, rB1 false-bit and rZ zero. Output4. Scratch includes prefix0/2/3, gather1..4, aut queue registers, and6 for zero construction. Register8 is preserved. The row equality is static in the generated program.
- Aggregate build passed (9690 jobs, `/tmp/explut-key-coefficients-build.log`); six execution/semantic/preservation/WF audits use only standard axioms (`/tmp/explut-key-coefficients-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: generate fixed negative gadget coefficients, compose positive/candidate/negative loaders with signedDotC, all-row traversal and correction/key assembly, actual EvalPK/KeyGen front, single-try accept-or-zero, KeySpec and numerical costs. Reduced exponents must be used in production EvalPK loaders. Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Executable negative gadget coefficient generation (2026-11-24)

- Added `Prog/KeyGadget.lean`, imported by aggregate. `powersC` appends consecutive ring powers of two using a counted doubling loop; exact loop invariant and WF proved. `negativeCoeffC` appends K ring zeros, saves the full row, and repeats it for each helper using `repAppC`.
- `gadget_row_list` proves G's row0 is the K powers followed by K zeros. `negativeCoeff_word` matches repetition to the helper/column product enumeration of `publicNegCoeff`. `exec_negativeCoeffC_public` connects the generated queue to the sparse signed-product semantics.
- `ringOneC` constructs the canonical word of one from the false-bit template using bitsC and natC. `negativeReadyC` includes that initializer, so the final `exec_negativeReadyC_public` requires only rB1=[false] and K>=2; no pre-encoded gadget or ring-one input. N positivity is supplied by Dims. Output4, scratch2/5/6/7; all other registers are untouched by construction.
- Aggregate build passed (9692 jobs, `/tmp/explut-key-gadget-build.log`). Six powers/codec/initialization/production/WF audits use only standard axioms (`/tmp/explut-key-gadget-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: compose positiveCoeffC, negativeReadyC and candidate gathers with signedDotC, preserving candidate (suggest register9), evaluator matrix8, and MPK outside scratch. Then all-row traversal/correction/key assembly and the actual EvalPK/KeyGen front; single-try accept-or-zero, KeySpec and numerical costs. Reduced EvalPK exponent templates, Dec/reduction/Submission/full comparison remain outstanding. Goal remains incomplete.

### Integrated public-map row machine and full traversal (2026-11-24)

- Added `Prog/KeyPublicMachine.lean`, imported by aggregate. `positiveCoeffC_frame` and `negativeReadyC_frame` give register footprints; `saveQueueC` packages generated queues into dedicated registers. `rowCountsC` constructs both signed-inner-product counts by binary doubling.
- `publicRowC` loads MPK from14, generates positive coefficients using AF on8 and saves them to rQa; generates negative coefficients to10; loads the candidate from9; gathers positive/negative candidate coordinates into rQb/11; installs counts rQc/12; runs signedDotC. `exec_publicRowC` proves exact pubShort output on rIa from the three encoded inputs plus bit/zero templates, requiring K>=2. This closes the explicit sparse-stream input hypotheses of the earlier row kernel.
- `publicRowC_frame` proves preservation of AF8, candidate9, MPK14, output accumulator15, rB1 and rZ. `publicRowsAppendC` statically traverses any prescribed row list and appends the computed ring words to15. `publicRowsC` clears15 and traverses Enum.list. Exact list semantics and WF proved; `exec_publicRowsC` yields the complete encoded public map in row enumeration order.
- Aggregate build passed (9694 jobs, `/tmp/explut-key-public-machine-build.log`). Six frame/row/full-traversal/WF audits use only standard axioms (`/tmp/explut-key-public-machine-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: generate `keyTarget` from the MPK's final d field (row0=d0, all other rows zero), connect publicRowsC and target stream to decRowsC; then full trapdoor correction/key assembly and one-try small-box acceptance/zero-key branch. The actual EvalPK/KeyGen input front must supply AF8, MPK14 and candidate9, and production EvalPK exponent templates must be bounded. KeySpec/numerical costs, Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Target generation and integrated gadget-coordinate computation (2026-11-24)

- Added `Prog/KeyTarget.lean`, imported by aggregate. `codecSize`/`mpkDOffset` recover the data-independent offset of the final d field. `mpkEnc_dSuffix` and `vecE_fin2` prove the actual codec split. `targetHeadC` copies MPK14, drops the preceding fields using a binary-built counter, and reads d0 into3. `targetC` emits d0 followed by W-1 zeros into rQa; `exec_targetC` matches `keyTarget` exactly.
- Added preservation lemmas for the full publicRowsC traversal and targetC. `keyDigitsC` runs publicRowsC (output15), targetC, copies15 to rQb, builds row/digit counters, and runs decRowsC. `exec_keyDigitsC` proves the output on rDq equals the actual enumerated `gadDec (keyTarget mpk - pubShort ... p)` coordinates. The generic `enum_map_ofFn`/`enum_gadget_order` bridge proves row-major then digit-major order.
- Production input contract remains MPK14, evaluator matrix8, candidate9, false-bit rB1 and canonical zero rZ; K>=2. The output gadget queue is rDq. Source/candidate and trapdoor retention must be checked when composing the correction traversal. Public-map output15 is preserved through target loading.
- Aggregate build passed (9696 jobs, `/tmp/explut-key-target-build.log`). Six codec/target/order/full-digit/WF audits use only standard axioms (`/tmp/explut-key-target-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: full trapdoor correction traversal (bounded row automorphisms), key assembly and single-try small-box accept/zero branch; connect actual EvalPK and sampler front to the input contract. Need production EvalPK exponent bounds, KeySpec and numerical costs. Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Full trapdoor correction traversal (2026-11-24)

- Added `Prog/KeyCorrection.lean`, imported by aggregate. `loadFamilyC` is a generic saved-source coordinate gather with exact execution/WF/frame lemmas. `correctionLoadC` loads a trapdoor row from the actual matrix codec on16 into rQa, a gadget row from17 into rQb, and the original candidate coordinate from9 into rIa.
- `correctionInlC` constructs the K count and bounded rowExponent template then invokes autDotC. `exec_correctionInlC` closes the explicit row-input hypotheses of the earlier correction kernel. `correctionCoordC` handles all PIdx coordinates, directly reading the non-trapdoor coordinates; exact corrected-coordinate semantics and register preservation proved.
- `correctionAppendC` traverses any prescribed coordinate list, appending to18. `correctionC` clears18 and traverses the full enumeration. `exec_correctionC` proves the exact encoded `p - realTrap T z` output, with no abstract correction-core assumption. The saved candidate9, T16, z17 and bit/zero templates are preserved by each coordinate computation.
- Input contract: T16 uses `(matE D (Wb D) (Fin D.K)).enc`, candidate9 and z17 use enum-family encodings, rB1 false-bit and rZ zero. Output18 is the corrected proposal. Sources8/14 are not used by this phase. Connect keyDigitsC output rDq to17 before invoking correctionC and establish T16/candidate9 retention through the digit phase.
- Aggregate build passed (9698 jobs, `/tmp/explut-key-correction-build.log`). Seven loader/coordinate/full-traversal/frame/WF audits use only standard axioms (`/tmp/explut-key-correction-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: compose digits and correction, assemble x/z in full key codec order, connect the single-try small-box test and accept/zero-key output. Actual EvalPK/sampler/KeyGen front and bounded EvalPK exponent templates still required. KeySpec/numerical costs, Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Integrated proposal and full key assembly (2026-11-24)

- Added `Prog/KeyProposal.lean`, imported by aggregate. Proved trapdoor16 preservation through public-map traversal and keyDigitsC; candidate9 and bit/zero templates also survive. `correctionC_frame` exports preservation of candidate9, trapdoor16, gadget17 and templates.
- `proposalC` runs keyDigitsC, copies its gadget queue from rDq to17, and runs correctionC. `exec_proposalC` proves the simultaneous exact z17 and x18 outputs, where z=gadDec(keyTarget-pubShort p) and x=p-realTrap T z.
- `AssemblySource`, `assemblySource` and `assemblySelection` reindex the concatenated x/z streams into actual KCol order (interleaving short and gadget coordinates per beta block). `assembleC` reads x18/z17 and gathers the full key word to19. `exec_assembleC` proves exact keyEnc encoding, not just a pair of component encodings.
- `proposalKeyC` composes proposal and assembly; `exec_proposalKeyC` proves the complete pre-acceptance proposal word from MPK14, evaluator matrix8, trapdoor16, candidate9, false-bit rB1 and zero rZ. Requires K>=2. The actual sampler/EvalPK front and acceptance test are not yet part of this theorem.
- Aggregate build passed (9700 jobs, `/tmp/explut-key-proposal-build.log`). Six frame/component/assembly/full-proposal/WF audits use only standard axioms (`/tmp/explut-key-proposal-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: connect the existing all-coordinate small-box test on corrected x18, with single-try accept19 or canonical zero-key output; install/check test templates without assuming they survive proposal scratch. Then actual EvalPK/sampler/KeyGen front, KeySpec and numerical costs. Bounded production EvalPK exponent templates, Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Single-try acceptance and zero-key branch (2026-11-24)

- Added `Prog/KeyAccept.lean`, imported by aggregate. Generic `emitBitsC` appends a fixed word from true5/false-rB1 templates. `radiusC` builds only the K-bit radius coefficient and repeats it N times; `exec_radiusC` proves the allC encoding. This avoids N*K literal-instruction embedding. WF and precise preservation proved.
- `acceptInitC` installs radius/low/high/count templates after proposal scratch is finished and copies corrected x18 to the test queue. Exact BoxTestReady/queue/count result proved. `acceptC` runs boxFamilyC, preserving proposal19, and branches once: keep19 if x is in kbOf.Small, otherwise natC builds the canonical full zero-key word on19. `exec_acceptC` proves both branches; no retry.
- `assembleC_frame` and `proposalKeyC_templates` establish retained x18 and bit/zero templates. `tryKeyC` composes proposalKeyC and acceptance. `exec_tryKeyC` proves the entire deterministic single-try output from encoded MPK14, AF8, trapdoor16, candidate9 and bit/zero templates, under the explicit box-test parameter inequalities. The result is keyEnc(assemble x z) on membership, keyEnc(0) otherwise.
- Lean typing note: in the final branch bridge use local `k : Keyt D` and `x' : PIdxD D -> Rg D` before invoking exec_acceptC. Implicit simplification cannot rewrite the conditional when assemble's inferred KCol(setting.tau,setting.W) is passed directly into the raw Keyt codec; typed locals and explicit branch proofs resolve this without altering semantics.
- Aggregate build passed (9702 jobs, `/tmp/explut-key-accept-build.log`). Six literal/radius/init/accept/full-try/WF audits use only standard axioms (`/tmp/explut-key-accept-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: concrete kbDc specialization and PMF law bridge to boxSample/keyGenLaw; actual sampler/EvalPK/KeyGen front (including invalid predicate -> zero and output MPK packaging), bounded production EvalPK exponent templates, KeySpec and numerical costs. Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Exact single-try output law and concrete box specialization (2026-11-24)

- Added `Prog/KeyTryLaw.lean`, imported by aggregate. `attemptOutput` expresses the exact boxSample option followed by keyOfOutput (abort maps to zero). `map_uniform_attemptOutput` proves its uniform-candidate law is keyGenLaw. `exec_tryKeyC_output` connects the actual VM output to this specification.
- `TryReady` explicitly packages the remaining front-end contract: MPK14, EvalPK matrix8, trapdoor16, candidate9, bit and zero templates. `map_uniform_exec_tryKeyC` proves exact output-law equality for arbitrary ready-state families. `map_coins_exec_tryKeyC` combines this with the existing fair-coin decoder law, without conditioning away rejects.
- `map_coins_exec_tryKeyC_Dc` specializes to Dc/Bk/rSmall/kbDc and discharges K>=2 and all separation/no-cancellation inequalities using existing concrete proofs. This remains conditional on TryReady states; it is not yet a theorem about the complete sampler/EvalPK machine.
- Local elaboration compatibility options `backward.isDefEq.respectTransparency` and `.types` are false in this module to allow concrete vs setting-indexed definitionally equal coordinate types at PMF boundaries. No axioms or computational proof bypasses were introduced; all final terms passed the kernel and standard-axiom audit.
- Aggregate build passed (9704 jobs, `/tmp/explut-key-try-law-build.log`). Five specification/VM/uniform/coins/concrete law audits use only standard axioms (`/tmp/explut-key-try-law-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: establish TryReady from actual MSK/predicate input and fair-coin sampling, including the EvalPK computation with bounded exponents; compile and package output with MPK, handle invalid predicate, prove full KeySpec and numerical costs. Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### EvalPK codec bridges and concrete semantics (2026-11-24)

- Added `Prog/KeyEvalCodec.lean`, imported by aggregate. `range_map_enum` and finite-index HfK/HiK/AaK/AinK identities bridge evaluator natural-index streams to public-key finite families. `helper_codec_hL`, `aaut_codec_aautL`, and `ain_codec_ainL` prove exact H/Aaut/Ain codec order. H contains forward then inverse for each helper bit; Ain contains all16 positions.
- `exec_evalC_keyPK` connects the existing actual evalC program to keyPK(bpOf(progOf C)), using the semantic keyPK_eq_evalVM theorem plus actual input-codec identities. Requirements remain StepIn, CoefIn, A0/Ain/C/15 templates, D.b=22 and 2^D.b<=q. Loader and template construction are the next obligations; no full EvalPK front claimed yet.
- Important correction to prior handoffs: inspected chainC/chBody/autStep and ChainIn. Existing production evalC uses the fixed g template (`rKc`) and iterates sigma_g `2^t` times (`rPw2`/rP); it does NOT construct unary g^(2^t) templates. Thus no bounded-exponent rewrite is needed for this existing evaluator. Charge the repeated automorphism work in cost proofs. The separate correction kernel already uses reduced rowExponent.
- Aggregate build passed (9706 jobs, `/tmp/explut-key-eval-codec-build.log`). Four codec/evaluator audits use only standard axioms (`/tmp/explut-key-eval-codec-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: actual MPK field reader and EvalPK template initializer, frame the evaluator to preserve MSK/predicate data for sampling/try, establish TryReady from real input, compile/package output and invalid-predicate zero branch. KeySpec/costs, Dec/reduction/Submission/full comparison remain open. Goal remains incomplete.

### Executable public-key field loading and EvalPK composition (2026-11-24)

- Added `Prog/KeyEvalRead.lean` and `Prog/KeyEvalFront.lean`, both imported by the aggregate. `readFieldC` uses scratch29/30 and the bit38 template to extract a fixed slice; `readBlockC` proves extraction from arbitrary flattened field lists. `publicFields_lengths` and `publicFields_flatten` identify the seven actual MPK codec fields.
- `evalFieldsC` loads H2, A04, Ain0 and Aaut1 from saved MPK17. Exact encodings and preservation outside 0/1/2/4/29/30 are proved. `exec_evalFieldsC` proves all four simultaneous outputs, with no preloaded stream assumptions.
- `EvalTemplates` isolates the remaining constant-initialization obligations, excluding public-key streams. `evalPublicC` composes the actual field loader and evalC. `exec_evalPublicC` proves the exact encoded keyPK matrix from MPK17, predicate3, bit38 and these constant templates. It constructs StepIn/CoefIn using preservation and the codec bridges. `wf_evalPublicC` proves loop-counter well-formedness, and `evalPublicC_saved` preserves MSK16/MPK17.
- Aggregate build passed (9710 jobs, `/tmp/explut-key-eval-front-build.log`; preceding loader build 9708 jobs). Eight loader/layout/front/WF/frame audits use only standard axioms (`/tmp/explut-key-eval-read-axioms.log`, `/tmp/explut-key-eval-front-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain.
- Next: construct EvalTemplates efficiently, including ring constants one/xInvG/xcK and repeated-zero multiplication templates; connect actual MSK/predicate input, preserve saved16/17 through EvalPK, restore bit38 as necessary before sampler/try. Then actual sampler/front/invalid-predicate handling/output packaging, full KeySpec/costs, Dec/reduction/Submission/full comparison. Goal remains incomplete. Changes remain uncommitted/unpushed.

### Actual initialized and sampled KeyGen core (2026-11-24)

- Added `Prog/KeyEvalInit.lean`, `KeyCandidate.lean`, `KeyInput.lean`, and `KeyCore.lean`, all aggregate imports. `TemplateWord`/`templateOpsC` provide verified constant stores: zero words use natC binary doubling; fixed ring words use emitBitsC. Three EvalPK ring constants are literal N*K-bit words (one, xInvG, xcK); their lengths must be charged in description/time bounds. Every other long zero template is constructed by doubling.
- `evalInitC_ready` constructs every EvalTemplates field from an arbitrary initial state, preserving predicate3/MSK16/MPK17. `evalReadyC` combines initialization and public evaluation with no template assumptions; exec_evalReadyC needs only MPK17 and predicate3. WF and saved16/17 are proved.
- `candidateC` initializes the decoder while preserving evaluated matrix8/public key14/trapdoor16, decodes fair bits from37, and copies the candidate to9. It also restores bit38 and zero63. `candidateC_ready` establishes the actual TryReady contract; `candidateTryC` connects directly to tryKeyC. `map_coins_candidateTryC` proves the exact keyGenLaw including abort-to-zero. The PMF bridge uses local respectTransparency/types=false options, as in KeyTryLaw, to reconcile raw vs setting-indexed coordinate types; the kernel audit is standard.
- `keyInputC` reads encoded MSK0 into MPK17/T16 using the exact concatenated mskEnc codec and preserves predicate3. `keyPrepareC` then runs initialized EvalPK and arranges MPK14/AF8/T16. `map_coins_keyCore` proves the exact deterministic-phase law from MSK0 and predicate3.
- `KeyCore.program D B r : XProg 105` now performs the complete compiled preparation, actual fresh coin generation, and compiled candidateTryC. coinFrame maps sampler output directly to tR rCoin (78) and uses only VM compiler scratch tapes0..5; sampleP clears the old coin register first. `law_sampleP` proves exact enc-state update. `law_program` proves the full-store law and `law_program_key` proves the output key on tR19 has the scheme's keyGenLaw. No arbitrary ready-state family or preinstalled template remains in this core theorem.
- This is still a core from `enc D.N D.K w`, with MSK on register0 and predicate on3. Remaining machine-interface work: parse encodeTuple[pw,msk,C], establish enc-state, branch on ValidC (length=predLen; invalid -> canonical zero key), retain/recover MPK for skEnc output, frame one-field tuple, clear workspace, and compile to bounded Machine / KeySpec. Candidate core consumes code scratch but preserves MPK14 in its apparent write footprint; a new proof of preservation through keyDigits/correction/acceptance would let output packaging read14. Existing correction frame lemmas only enumerate9/16/17/18/38/63, so add a separate14 lemma rather than changing those APIs. Alternatively retain MPK outside framed VM with explicit cost.
- Aggregate build passed (9718 jobs, `/tmp/explut-key-core-build.log`; init9712/candidate9714/input9716). Thirteen generic-init/readiness/core/input/PMF/WF audits use only propext/Classical.choice/Quot.sound (`/tmp/explut-key-eval-init-axioms.log`, `/tmp/explut-key-input-axioms.log`, `/tmp/explut-key-core-axioms.log`). No sorry/native_decide/custom axioms, no warnings in the new modules, diff check passed. No live jobs remain. All changes remain uncommitted/unpushed.
- Next: full KeyGen interface/KeySpec and numerical costs. Dec actual machine/spec/cost, reduction machines/costs, Submission/global comparison with 2^818 remain open. Goal remains active and incomplete.

### Full finite-clock KeyGen Machine and KeySpec (2026-11-24)

- Added `Prog/KeyOutput.lean`, `KeyBranch.lean`, `KeyFront.lean`, and `KeyMachine.lean`, imported by the aggregate. Proved MPK14 preservation through keyDigits/correction/acceptance/candidateTry using new separate lemmas; prior frame APIs unchanged. `packKeyC` emits MPK14 ++ key19 on0. `KeyCore.outputProgram` runs the probabilistic core, packs skEnc, and uses IO.post to erase all workspace. Its law is the complete unframed secret-key word distribution.
- `invalidKeyC` reads MPK from the MSK codec and builds the zero-key word using natC, then packs it. `KeyCore.run_pre_any` proves VM initialization from arbitrary parser workspace; `enterP` moves predicate input1 to register3. `validP`/`invalidP` have exact output laws from arbitrary tapes with MSK0/predicate1.
- `KeyCore.parse` decodes encodeTuple[pw,msk,C] into io2 msk C []. `checkP` maps the existing lenEqP to predicate1/result2/scratch3..6. `chooseP` branches on the resulting bit, and `law_chooseP` equals keyLawW for both ValidC and invalid C. The XProg ifBit condition is `(s i).head? = some true`, not MVM.hd; use a local law equality to expose the branch without unfolding its body.
- `KeyCore.keyProgram` parses, checks, runs the correct branch, and frames the output as encodeTuple[skEnc sk], clearing workspace. `keyInputBound D L` bounds the full framed input for every C.length<=L. `keyMP D B r L` is the actual toMachineT program with the compiler's finite clock. **`keySpec_keyMP` proves the complete primitive KeySpec**, and **`keySpec_keyMP_Dc L` discharges every concrete arithmetic condition for Dc/Bk/rSmall/kbDc**. These are no longer conditional on an arbitrary VM state family, oracle sampler, or unspecified machine.
- `time_keyMP` identifies the exact compiler totalTimeT expression. Numerical description/time bounds are not yet proved; do not claim KeyGen is below the global 2^818 comparison yet. Three literal ring constants in EvalInit are N*K bits each; candidate initialization has one more N*K-bit constant. Unary templates use doubling. Other existing code traverses very large finite index lists, whose instruction and loop costs must be bounded explicitly.
- Aggregate build passed (9726 jobs, `/tmp/explut-key-machine-build.log`; output9720/branch9722/front9724). Nine preservation/output/parser/branch/program/spec/WF audits use only propext/Classical.choice/Quot.sound (`/tmp/explut-key-machine-axioms.log`). No sorry/native_decide/custom axioms, new modules compile without warnings, diff check passed. No live jobs remain. All changes remain uncommitted/unpushed.
- Next: numeric KeyGen bounds for the actual keyProgram/keyMP, then Dec machine/spec/cost, reduction machines/costs, and Submission/global comparison with 2^818. KeyGen functional specification is now complete; overall goal remains active and incomplete.

### KeyGen syntax-size foundation (2026-11-24)

- Added `Prog/KeySizeBasic.lean`, imported by aggregate. `codeWeight` counts actual MVM syntax nodes. `size_compile_weight` proves the real 105-tape MVM compiler has at most 100000 states per counted instruction/control node, including each arithmetic operation, canonicalization and framing. Existing Mersenne/VMSize and VMCost concern RingVM (200 registers / 247 tapes), so do not use them directly for this MVM implementation.
- `weight_natC` gives a coarse 3*n+1 bound for doubling-generated unary constants; `weight_emitBitsC` is exactly word.length+1. TemplateWord/templateOps/readField bounds compose these for actual code. No hypothetical alternate implementation is used.
- `size_evalInitC_poly` removes codec terms symbolically before concrete specialization; `size_evalInitC_Dc` proves initialized EvalPK constant code uses <=2^112 states. This is deliberately coarse (linear natC bound) and is a state-count bound, not runtime or description length. `size_evalC` bounds the static evaluator code by2^37 states; loop iteration costs remain to be charged.
- Lean kernel pitfall: directly specializing size_evalInitC to Dc then simp/normalizing literal encRM lengths hit kernel deep recursion even at maxRecDepth100000. Resolve by proving the polynomial inequality for generic D first, then specialize the codec-free theorem. The final proof needs no increased recursion setting and builds in ~3 seconds.
- Aggregate build passed (9728 jobs, `/tmp/explut-key-size-basic-build.log`). Four size/doubling/concrete audits use only propext/Classical.choice/Quot.sound (`/tmp/explut-key-size-basic-axioms.log`). No sorry/native_decide/custom axioms; diff check passed. No live jobs remain, changes uncommitted/unpushed.
- Next: bound finite-list gather/public-row/correction/assembly syntax and the full KeyCore.keyProgram, then actual compiler runtime for MVM (may require new per-tape bounds because existing RingVM cost library does not apply). Full KeySpec is already proved. Dec/reduction/Submission/global2^818 comparison remain open.
- User asked ETA during this stage. Answer given candidly: at least hours, potentially days, no reliable completion time; actual numerical cost comparison is the largest uncertainty. Continue work without awaiting permission.

### Gather and assembly state bounds (2026-11-24)

- Added `Prog/KeyGatherSize.lean`, imported by aggregate. Proved weight_fetchRingC, weight_gatherAppendC/gatherC with bounded indices, and generic finite-family/loadFamilyC bounds. The bounds charge actual binary-doubling offset construction, copies/drops/moves, and each generated gather instruction.
- `weight_assembleC`/`size_assembleC` bound the actual full key assembly by source/output cardinalities. `assembly_lengths_Dc` bounds both finite enumerations by2^66. `size_assembleC_of_bounds` eliminates cardinality terms generically; `size_assembleC_Dc` proves <=2^192 compiled states. This remains a state bound, not time or description length.
- Important Lean elaboration detail: assembleC was elaborated with the PIdx DecidableEq from Classical.propDecidable, whereas newer imports provide FinEnum.decEq. This produces visually identical Enum.index expressions that are not definitionally equal. The size proof explicitly installs `let : DecidableEq (PIdx ... ) := Classical.decEq _`, then applies weight_gatherC directly to the existing target expression rather than rebuilding the index list. This preserves the actual code and its original instance. Generic theorem `Enum.index_lt` requires DecidableEq, not BEq/LawfulBEq. Avoid replacing code or theorem APIs to accommodate the elaborator.
- Concrete proof must instantiate a generic cardinality-bound theorem before evaluating numerals; direct arithmetic comparison involving concrete Enum.list lengths hits recursion depth even at100000. Final proof uses the generic size_assembleC_of_bounds and needs no elevated depth setting.
- Aggregate build passed (9730 jobs, `/tmp/explut-key-gather-size-build.log`), three gather/assembly/concrete audits standard axioms only (`/tmp/explut-key-gather-size-axioms.log`), diff check passed. No live jobs. Changes remain uncommitted/unpushed.
- Remaining: public-row/correction/acceptance and full KeyGen size bounds; actual MVM runtime certificates (existing RingVM VMCost does not apply); Dec/reduction/Submission/global2^818 comparison. Goal remains active and incomplete.

### Acceptance and correction size composition (2026-11-24)

- Added Prog/KeyAcceptSize.lean and KeyCorrectionSize.lean, aggregate imports. Acceptance bounds charge actual radius generation and the full zero-key branch. size_acceptC_Dc proves <=2^128 compiled states. keyCodecSize_eq exposes key word length before concrete specialization; direct change of concrete codecSize had caused huge unfolding.
- Correction bounds cover all three gathers, rowExponent (<2N), autDotC, both coordinate cases and the full traversal. size_correctionC D S proves <=100000*(S*(correctionCoordBudget D S+1)+2) when all source cardinalities are <=S. PIdx DecidableEq is explicitly Classical.decEq where required.
- correction_source_lengths gives symbolic T/Z/P cardinalities; correction_counts_Dc proves all three <=2^66. The proposed final size_correctionC_Dc <=2^212 specialization repeatedly took excessive checking time despite small scalar arithmetic. Runs were explicitly interrupted and that unverified specialization removed. Do NOT claim the concrete correction bound is proved. General bound and concrete cardinalities are independently proved. Next inspect the specialization boundary without redoing generic proofs. /tmp/key-correction-size-full.lean is a stale exploratory copy, not authoritative.
- Aggregate build passed (9734 jobs, /tmp/explut-key-correction-size-build.log). Three audits use only standard axioms (/tmp/explut-key-correction-size-axioms.log). Diff check passed. No live jobs; changes uncommitted/unpushed.
- Remaining: public-row/full KeyGen size and time bounds, actual MVM runtime certificates, Dec/reduction/Submission/global comparison. Goal active and incomplete.

### Public-row coefficient-builder size bounds (2026-11-24)

- Added Prog/KeyCoefficientSize.lean and aggregate import. Proved weight_prefixC, weight_appendAFC, weight_negativeCoeffC, weight_ringOneC, weight_negativeReadyC, weight_autGatheredC, weight_gatherAutC for the actual coefficient-stream code. These are ready to combine with BH/source cardinalities into publicRowC/publicRowsC and keyDigitsC bounds.
- Reinvestigated the pending concrete correction specialization. Isolated arithmetic /tmp/correction-arithmetic.lean with fully numerical dimensions eventually returned exit0 (norm_num). Attempts embedding the bound in the concrete declaration, including a separate private scalar lemma plus explicit dimension rewrites, continued for over a minute without completion and were deliberately interrupted. No missing process was restarted; sessions closed explicitly. Unverified final specialization and unused private scalar were removed; KeyCorrectionSize remains at the verified generic bound/cardinality results. Do not claim size_correctionC_Dc or <=2^212 yet. Temporary diagnostic files may be stale or modified.
- Aggregate build passed (9736 jobs, /tmp/explut-key-coefficient-size-build.log). Two coefficient/gather audits standard axioms only (/tmp/explut-key-coefficient-size-axioms.log); diff check passed. No live sessions/jobs. Changes remain uncommitted/unpushed.
- Next: combine coefficient builders and gather bounds into publicRowC/publicRowsC, keyDigitsC, and full keyProgram state bounds. Concrete correction specialization still open, as are KeyGen runtime, Dec/reduction/Submission/global comparison. Goal remains active.

### Public-row state-count composition (2026-11-24)

- Added Prog/KeyPublicSize.lean and aggregate import. PublicSizeInputs supplies six cardinality bounds; weight_publicRowC composes coefficient builders, candidate gathers, counters and signedDotC. size_publicRowsC bounds the actual compiled traversal by 100000*(2^b*(publicRowBudget D S+1)+2).
- Repaired positive coefficient proof by unfolding bhPrefixLength on both sides and normalizing multiplication association. Standalone Lean passed; aggregate build passed (9738 jobs, /tmp/explut-key-public-size-build.log). weight_publicRowC and size_publicRowsC axiom audit reports only propext, Classical.choice, Quot.sound; git diff --check passed.
- Next: concrete public cardinalities, keyDigitsC and full keyProgram size; KeyGen runtime, Dec, reduction, Submission and global comparison remain open. No live jobs. Changes uncommitted/unpushed; goal remains active.
- User requested ETA: reported at least hours, potentially days, with no reliable exact completion time; continue authorized goal work.

### Full deterministic attempt state-count composition (2026-11-24)

- Added symbolic public_input_lengths in KeyPublicSize, and new KeyDigitsSize/KeyTrySize aggregate imports. publicSizeInputs_Dc and trySizeInputs_Dc close all public, correction, assembly cardinalities at S=2^66 without evaluating enumerations.
- KeyDigitsSize proves target construction and full keyDigitsC weight/compiled-state bounds. KeyTrySize composes keyDigits, correction, assembly, rejection/acceptance, and candidate initialization/decoding into size_candidateTryC. Bounds are generic scalar expressions; they do not yet give a final numerical exponent for keyMP.
- Standalone checking caught only a noncomputable marker, conjunction proof, and unfolding alignment, all repaired. Aggregate build passed (9742 jobs, /tmp/explut-key-try-size-build.log). trySizeInputs_Dc, size_keyDigitsC, size_candidateTryC audit: only propext/Classical.choice/Quot.sound. No sorry/custom axiom/native_decide in the three new size files; git diff --check passed. No live jobs; changes uncommitted/unpushed.
- Next: bound remaining Eval/public-field/input initialization, compose XProg keyProgram including coins and framing, eliminate codec offsets symbolically and specialize scalar bounds. Full KeyGen time, Dec, reduction, Submission/global comparison still open. Goal active and incomplete.

### Complete keyProgram state-count composition (2026-11-24)

- Added KeyPrepareSize: generic take-sum/getD bound, publicFieldLengths_sum exact codec identity, bounds for four public-field reads, master-key reads, Eval templates/evaluator and keyPrepareC.
- Added KeyProgramSize: invalid branch, coin sampler, IO entry plus cleanup, parsing/check/framing, and full keyProgram bound. size_keyProgram_Dc specializes all cardinality premises and coin budget (keyCoinCount_Dc <2^106). This is the actual program with both branches and all IO; its upper bound is still the symbolic keyProgramBudget Dc (2^66) Bk 106, NOT a closed exponent or a runtime bound.
- Aggregate build passed (9746 jobs, /tmp/explut-key-program-size-build.log). Audited size_keyPrepareC and size_keyProgram_Dc: standard axioms only. No sorry/custom axiom/native_decide in new files; git diff --check passed. No live jobs, changes uncommitted/unpushed.
- Next: eliminate codecSize(mpkEnc), trap/key codecSize, mpkDOffset, evalInitOps weight sum, and nPI symbolically; prove closed scalar keyProgram size then keyMP descLen. KeyGen runtime remains entirely separate and unfinished. Dec/reduction/Submission/global comparison remain open; goal active.

### Closed KeyGen state-count and description bounds (2026-11-24)

- Added KeySizeConf and aggregate import. keyCodec_lengths eliminates public/trap codec sizes symbolically; keyCodec_bounds_Dc bounds public/trap/key words by 2^120. evalInitWeight_eq and evalInitWeight_Dc eliminate the template list. keyProgramBudget_numeric proves the scalar bound for abstract D under explicit projections/counts/codec bounds, avoiding giant concrete codec elaboration.
- size_keyProgram_Dc_pow: actual keyProgram Dc Bk rSmall state count +4 <=2^220. descLen_keyMP_Dc L: actual keyMP Dc Bk rSmall L description length <=2^620, for every input bound L. Includes both branches, coins, IO and framing; no numeric runtime claim.
- Scalar proof needed local maxRecDepth=100000 for kernel checking (completed in ~12 seconds). Early description identity incorrectly used 107 tapes; generic descLen_program105 exposed the mistake, corrected to actual 105 tapes. All final identities and bounds verified. Standard axioms only for both final theorems (/tmp/key-size-conf-audit.lean).
- Aggregate build passed 9748 jobs (/tmp/explut-key-size-conf-build.log), no new-file sorry/custom axiom/native_decide, git diff --check passed. No live jobs; changes uncommitted/unpushed.
- Next: KeyGen runtime certificate for MVM's actual 64-register/105-tape compiler (RingVM VMCost is 200/247 and cannot directly apply). Need register length invariants, primitive bounds, loop composition, then totalTimeT bound including arbitrary C.length<=L. Dec/reduction/Submission/global comparison remain open. Goal active, not complete.

### Growing-queue runtime certificates (2026-11-24)

- Added KeyTimeBasic and aggregate import. KeyTime.Cert states actual XProg lenBoundT/timeBoundT bounds; mono/seq/ifBit/frame composition proved. loop_family handles iteration-dependent output lengths, rep_family applies it to actual MVM.compile (.rep ...), with time R*(2*M+T+4)+2.
- This avoids the unusable fixed-invariant-only approach for MVM append queues (RingVM VMCost has different registers/tapes and lacks this append issue). Added appT_cert and actual MVM compile_app_cert/compile_app_self_cert with explicit frame/output/scratch bounds, including self-append used in natC binary doubling.
- Aggregate build passed 9750 jobs (/tmp/explut-key-time-basic-build.log). rep_family and both compiled append certificates audited: standard axioms only. git diff --check passed. No live jobs; changes uncommitted/unpushed.
- Next: primitive cp/clr/drop/mv/ring operation certificates, natC and field/gather output-length bounds, then stage-specific loop families and totalTimeT. These are proof tools, not a closed KeyGen runtime result. KeyGen desc<=2^620 already closed; time, Dec/reduction/Submission/global comparison remain open. Goal active.

### Actual MVM movement runtime bounds (2026-11-24)

- Added KeyTimeMoves and KeyTimeChecked with aggregate imports. Cert.ofVB/toVB bridges existing per-tape bounds; embedF_update_bound exposes exact global updates. compile_cp_cert (distinct registers), compile_clr_cert, compile_tl_cert prove actual output-vector updates and time <=2*(M+1)+3.
- Reused existing checked *primitive* proofs in RingVM VMCert via new generic frame_checked, without applying the incompatible RingVM compiler or register layout. compile_drop_cert uses actual fDr and blank tape39, time <=(2*M+3)*(20+10*counterLength), preserves length upper bounds. compile_mvR_cert uses actual fMv with NK counter37 and blank39/40, time <=(2*M+3)*(20+10*a37), preserves length bounds. VMCert dependency built locally successfully.
- Aggregate build passed 9756 jobs (/tmp/explut-key-time-moves-build.log). Five actual compiled movement certificates audited standard axioms only (/tmp/key-time-moves-audit.lean). git diff --check passed. All job handles terminal; changes uncommitted/unpushed.
- Next: counted mv, ring-operation loads/operation/canonicalization/output certificates using VMCert, initialization/natC and stage length invariants; then full KeyGen runtime. Existing append outputs use embedF local bounds; normalize to global scratch/register updates when composing. Numeric KeyGen time remains open, as do Dec/reduction/Submission/global comparison. Goal active.

### Ring-operation load/store runtime certificates (2026-11-24)

- Added KeyTimeLoad and aggregate import. checked_local converts checked primitive claims into Cert with explicit output bounds. inP_cert and load_cert cover actual operand load fLd (33 or34), set only destination operation tape bound to NK, preserve source and zero scratch32/39/40, time <=(2*M+3)*(30+10*NK).
- Inspected actual compiler output: it uses outQ (cp0 2;clr1;clr2;clr3), NOT ValVM.outP. Added check_outQ with exact local layout, outQ_cert and store_cert using fOut. Result bound on tape33 becomes destination register bound NK, and work tapes32/33/34 become blank, time <=(2*M+3)*20. No unused ValVM.outP certificate retained.
- Aggregate build passed 9758 jobs (/tmp/explut-key-time-load-build.log). load_cert/store_cert standard axioms only; check_outQ depends only on propext. No sorry/custom axiom/native_decide; diff check passed. All jobs terminal, changes uncommitted/unpushed.
- Next: ring-operation body fOp and canonicalization fCan certificates (operation scratch0..31 may have nonzero bounded lengths; work/tmpl tapes require separate bounds), compose with actual load/store sequence. Then initialization/natC, stage register invariants, KeyGen totalTimeT. Full numeric time and Dec/reduction/Submission/global comparison remain open. Goal active.

### Binary arithmetic and canonicalization runtime certificates (2026-11-24)

- Added KeyTimeRing and aggregate import. ringArea gives first-five structured bounds with all scratch bounded by M. New check_add37/check_sub37 verify actual Op.add/sub.prog after their Fin.castLE maps to37 tapes (check8/decide+kernel). ring37_cert handles full37 input with bounded nonblank scratch. Binary multiplication reuses VMCert.checkT_mulRMP, exactly its37-tape primitive.
- binaryOp_cert applies the actual fOp34 embedding for add/sub/mul, with cost (2M+3)*pEval[M,N,K](binaryPoly o). canon28_cert and canon_cert apply actual fCan with time (2M+3)*(7+44N+40NK). Output bounds remain explicit embedF/ringArea values; these are stage certificates, not yet a complete compiled op certificate.
- Aggregate build passed9760 jobs (/tmp/explut-key-time-ring-build.log). check_add37/check_sub37 only propext; binaryOp_cert/canon_cert standard axioms only (/tmp/key-time-ring-audit.lean). Diff check passed. No live jobs; changes uncommitted/unpushed.
- Next: compose load33/load34/binaryOp/canon/store into MVM.compile(.op o d a b), prove intermediate frame bounds/top/blank scratch properties; counted operations neg/aut/rho/rot/dig need analogous certificates. Then natC and stage invariants/KeyGen runtime. KeyGen desc<=2^620 remains closed; runtime, Dec/reduction/Submission/global comparison remain open. Goal active.

### Complete compiled binary operation runtime (2026-11-24)

- Added KeyTimeBinary and aggregate import. binaryAfter/canonicalAfter/binaryResult expose intermediate and final bound vectors; embed_bound/ringArea_bound and field lemmas discharge intermediate top/template/zero requirements.
- compile_binary_cert proves actual MVM.compile(.op o d s t) for add/sub/mul from bounded input with template35<=K,36<=N,37=NK,38<=NK and blank32/39/40. No restriction on d/s/t equality. Exact five-stage composition (two loads, operation, canonicalizer, store), cost binaryTime=(2M+3)*(2*(30+10NK)+pEval[M,N,K](binaryPoly o)+(7+44N+40NK)+20). Output binaryResult_words proves destination bound NK and work32/33/34 blank.
- Aggregate build passed9762 jobs (/tmp/explut-key-time-binary-build.log); compile_binary_cert and binaryResult_words audit standard axioms only (/tmp/key-time-binary-audit.lean). Diff check passed; no live jobs, changes uncommitted/unpushed.
- Next: normalize binaryResult for preserved registers/templates/39/40 and scratch bounds to facilitate repeated operations; analogous counted operation certificates neg/aut/rho/rot/dig; initialization/natC and KeyGen stage invariants/time. Full KeyGen runtime still open; Dec/reduction/Submission/global comparison pending. Goal active.

### Binary-operation invariant preservation (2026-11-24)

- Added KeyTimeInvariant and aggregate import. embed_outside, binaryFrame_lt, canonicalFrame_range and store_outside expose unaffected tapes. binaryResult_high preserves tapes>=39 except destination; binaryResult_other_register preserves every other register.
- binaryResult_templates gives35=K,36=N,37=input37,38=NK; binaryResult_bound preserves global bound M when N,K,NK<=M. Ready bundles exactly compile_binary_cert's top/template/blank requirements; binaryResult_ready proves all retained for next operation. Work33/34 blank also separately available via binaryResult_words.
- Aggregate build passed9764 jobs (/tmp/explut-key-time-invariant-build.log); other-register/templates/Ready audits standard axioms only (/tmp/key-time-invariant-audit.lean). Diff check passed. No live jobs, changes uncommitted/unpushed.
- Next: use Ready for sequences/loops (tail on register tapes preserves template/blank conditions). A uniform per-register bound vector with scratch0..31=M,32..34=0,35=K,36=N,37/38=NK,39/40=0 and registers=M can yield fixed invariant for binary-only loops. Growing append queues still need iteration families. Counted operations, initialization/natC, full KeyGen runtime, Dec/reduction/Submission/global comparison remain open. Goal active.

### All counted ring instructions: complete runtime certificates (2026-11-24)

- Added KeyTimeCounted and aggregate import. check_counted37 proves exact Op.prog checks for all five nonbinary operations (neg/aut/rho/rot/dig) on37 tapes after their real maps, using sigmaJ and scratch32 at topM. countedPoly selects actual sweep polynomial, including RingVM.wDigitM for arbitrary digit-counter length.
- counted37_cert/countedOp_cert use actual fOp(41+c.val), preserving its count bound; countedAfter_fields and countedArea_bound discharge canonicalization requirements. compile_counted_cert composes actual two loads, counted operation, canonicalization and store, with counter length a(tR c), arbitrary d/s/c aliasing. It charges the second load even though counted op reads the register directly, matching actual compiler.
- All eight MVM ring ops now have complete instruction-level runtime certificates (binary in KeyTimeBinary, counted here). This does NOT close KeyGen runtime: stage invariants, counters/natC, remaining simple moves/eqb, loop composition and totalTimeT remain.
- Aggregate build passed9766 jobs (/tmp/explut-key-time-counted-build.log). check_counted37 only propext; compile_counted_cert standard axioms only (/tmp/key-time-counted-audit.lean). No sorry/custom axiom/native_decide in new file; diff check passed. No live jobs; changes uncommitted/unpushed.
- Next: countedResult preservation/Ready analogous to binary; unified op certificates and explicit polynomial upper bounds, then initialization and stages. Dec/reduction/Submission/global comparison remain pending. Goal active.

### Uniform ring-instruction polynomial and conditional numeric bound (2026-11-25)

- Added KeyTimeArithmetic and aggregate import. operationBound=1000*(M+1)*(N+1)^2*(K+1)^2*(count+1). binaryTime_le (count0) and countedTime_le prove domination of actual full five-stage time expressions, all eight operations. Polynomial bounds kernel checked with simp/ring_nf/omega; no custom axioms.
- compile_op_cert unifies all actual MVM .op variants under Ready, with operationResult selecting binaryResult/countedResult. compile_op_concrete proves <=2^340 for N=2^24,K=2^16 under explicit Ready(2^120,N,K,a). This is CONDITIONAL on all length/template/blank premises. No claim that every KeyGen stage yet satisfies Ready or length<=2^120.
- Aggregate build passed9768 jobs (/tmp/explut-key-time-arithmetic-build.log). Both polynomial bounds and compile_op_concrete audited standard axioms only (/tmp/key-time-arithmetic-audit.lean). Diff check passed. No live jobs; changes uncommitted/unpushed.
- Next: countedResult Ready/register/template preservation to parallel binary, then initialization/natC and actual stage bounds. Remaining runtime-moving primitives include counted mv/eqb/nop/self-copy variants; append needs growing-queue families. Full KeyGen runtime, Dec/reduction/Submission/global comparison still open. Goal active.

### All ring operations preserve readiness (2026-11-25)

- Added KeyTimeOpInvariant and aggregate import. countedFrame_range separates low operation/scratch tapes from the direct counter register. countedAfter_high/countResult_high prove high-tape preservation with count=input counter length (including the counter itself unless overwritten by destination). countedResult_templates/words/bound establish actual output template/blank/global bounds; countedResult_ready closes Ready preservation.
- operationResult_ready now covers all eight ops, compile_op_ready pairs actual compile time/length certificate with readiness of the next bound vector. Source/counter/destination aliasing remains allowed. All results use actual output bounds, not semantic length alone.
- Aggregate build passed9770 jobs (/tmp/explut-key-time-op-invariant-build.log); countedResult_ready/compile_op_ready standard axiom audit (/tmp/key-time-op-invariant-audit.lean). Diff check passed. No live jobs; changes uncommitted/unpushed.
- Next: use actual Code sequential/loop composition with these certified transforms; initialization/natC/gather and growing queue invariants remain. Primitive counted mv/eqb/nop/self-copy edge cases still needed for complete code coverage. Full KeyGen time, Dec/reduction/Submission/global comparison remain open; goal active.

### Control and counted-move runtime coverage (2026-11-25)

- Added KeyTimeControl and aggregate import. nopX_cert and compile_nop preserve all bounds. compile_eqb_cert for distinct flag/inputs writes exact output bound1 and costs <=2*(M+1)+3. compile_mv_cert uses actual fMv(...41+c.val), checked mvPc, blank39/40, preserves all length upper bounds and costs <=(2M+3)*(20+10*a(tRc)).
- Added actual alias-branch proofs: compile_cp_any covers self copy, compile_drop_self, compile_mvR_self, compile_mv_overlap, compile_eqb_overlap (compiler selects nopX on illegal overlaps). Self branches required reduceDIte after simplification to True; all final proofs checked.
- Aggregate build passed9772 jobs (/tmp/explut-key-time-control-build.log); movement/eqb/copy/overlap audits standard axioms only (/tmp/key-time-control-audit.lean). Diff check passed. No live jobs; changes uncommitted/unpushed.
- Next: initialize counters and literals (natC/emitBitsC) using existing exact global copy/clear bounds plus append frame normalization; certify their output lengths/scratch states, then actual KeyGen phases and iteration families. Instruction primitive coverage now includes all Code constructors' leaves (op, mv, mvR, cp, drop, clr, tl, app, eqb, nop), but no closed full KeyGen runtime yet. Dec/reduction/Submission/global comparison pending. Goal active.

### Append bound normalization and nonblank-scratch loads (2026-11-25)

- Added KeyTimeAppend, KeyTimeLoadScratch and aggregate imports. compile_append covers distinct and self append, explicit appendResult = update destination(sum), scratch39=source length, scratch40=0. embed_update/embed_original normalize embedded updates.
- Important static-bound issue identified: appT's forN loop leaves a nonzero upper bound on counter scratch39 in lenBoundT, even though actual runtime counter is empty. Existing Ready blank39 cannot be assumed from semantics for totalTimeT composition. No compiler changes made. New check_inP_scratch accepts top-bound scratch32/39/40, proves load clears them; inP_scratch_cert/load_scratch_cert establish actual load without blank-scratch premises. Need use these to broaden compiled op certificates before composing append->op.
- Aggregate build passed9776 jobs (/tmp/explut-key-time-append-scratch-build.log). compile_append/load_scratch_cert standard axioms, check_inP_scratch only propext (/tmp/key-time-append-scratch-audit.lean). Diff check passed; all jobs terminal, changes uncommitted/unpushed.
- Next: natC runtime induction on n/2 with exact destination length n, source bit length1, global bound M>=n. Candidate convenient result upper bounds: dest=n, scratch39=max(input39,n), scratch40=input40 (actual scratch may clear); all other tapes unchanged. Then emitBitsC/templates. Broaden operation Ready via nonblank-scratch load proof. Full KeyGen runtime and Dec/reduction/Submission/global comparison remain open. Goal active.

### Unary and literal template runtime composition (2026-11-25)

- Added KeyTimeNat and KeyTimeTemplates, both imported by aggregate. natResult explicitly updates destination to n and scratch39/40 to M, preserving all other tape bounds. compile_natC proves actual binary-doubling MVM natC has this output bound and time <=(32*n+4)*(2*M+5), under input top<=M, n<=M, distinct source/destination and source length bound1. Strong induction uses n/2, real append certificates and actual nop branch; no semantic/static-bound substitution.
- compile_emitBitsC covers actual literal list append: output destination input length+bs.length, time <=(10*bs.length+1)*(2*M+5), with distinct true/false source registers and output<=M. compile_template combines zero and literal constructors with bound (32*value.length+6)*(2*M+5). compile_templateOps certifies the actual sequential template list via templateBounds and templateTimeWeight, without unfolding concrete encRM bit values.
- Aggregate build passed9780 jobs (/tmp/explut-key-time-templates-build.log). compile_natC, compile_emitBitsC, compile_template, compile_templateOps all standard axioms only (/tmp/key-time-templates-audit.lean); no sorry/custom axiom/native_decide. git diff --check passed. All jobs terminal; changes uncommitted/unpushed.
- Next: certify bitsC initialization and instantiate actual evalInitOps bounds to close evalInitC, then actual evaluation/gather/stage invariants. Broaden operation input readiness using load_scratch_cert (append/natResult carry scratch upper bounds M). Full KeyGen runtime remains open; Dec/reductions/Submission/global comparison remain pending. Goal active.

### Actual EvalPK constant initializer runtime (2026-11-25)

- Added KeyTimeInit and aggregate import. compile_bitsC certifies the actual two-clears/two-equality instruction sequence with output bit lengths1, time4*(2*M+5), distinct bit/aux registers and M>=1. compile_initBits includes the actual auxiliary-register clear, time5*(2*M+5). No semantic input equality is assumed for these static length certificates.
- template_length_le_weight and templateTimeWeight_le reuse existing symbolic size weights. evalInitOps_valid proves actual destinations avoid true/false sources and each template fits M whenever the sum of existing weightBound values fits M. compile_evalInitC composes the actual right-associated program, output templateBounds M (evalInitOps D) (initBitsResult a), time(5+templateTimeWeight)*(2*M+5). templateBounds_top/evalInitBounds_top preserve global input bound M.
- compile_evalInitC_Dc proves actual constant initializer time<=2^250 conditional on all input tape bounds<=2^120, using already verified evalInitWeight_Dc. This is an initializer certificate, not full KeyGen runtime. It deliberately permits scratch39/40 output static bounds M.
- Aggregate build passed9782 jobs (/tmp/explut-key-time-init-build.log). compile_bitsC/compile_evalInitC/evalInitBounds_top/compile_evalInitC_Dc all audited standard axioms only (/tmp/key-time-init-audit.lean). No sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: broaden full compiled ring-op certificates to nonblank work/scratch inputs via load_scratch_cert, preserving actual five-stage compile sequence; derive precise initialized register/template fields from templateBounds for evaluator loops. Then evaluation/public/gather/candidate stage families and full KeyGen time. Dec/reduction/Submission/global comparison remain open. Goal active.

### Nonblank scratch arithmetic and initializer bridge (2026-11-25)

- Added KeyTimeScratch and aggregate import. cleanWork clears bounds on32/39/40 only; load_scratch_normalized proves actual first fLd33 operand load has output update(cleanWork a)33(NK), retaining its original time bound. compile_binary_scratch/compile_counted_scratch compose the unchanged actual five-stage compiler from arbitrary bounded scratch inputs; no extra clear instructions or alternate compiler.
- RingInputs bundles global/template conditions without blank-work premises. compile_op_scratch/compile_op_scratch_ready cover all8 ops, preserve strong Ready after output, use operationResult(...cleanWork a), and retain operationBound(M,N,K,inputcounter). compile_op_scratch_concrete gives conditional <=2^340 at M2^120,N2^24,K2^16. operationResult_destination/other expose destination NK and all other register bounds unchanged, including counter aliases.
- update_register_low/natResult_low/templateBounds_low/initBitsResult_low prove low tapes<39 are preserved through actual initializers. RingInputs.evalInit and compile_evalInitC_ringInputs connect the complete real initializer output to ring-op input requirements, despite static scratch upper bounds M. Explicit template and input-top assumptions remain necessary; no full evaluator runtime claim.
- Aggregate build passed9784 jobs (/tmp/explut-key-time-scratch-build.log). First-load/full-op/Ready/numeric/register/init-bridge audits all standard axioms only (/tmp/key-time-scratch-audit.lean); no sorry/custom axiom/native_decide. git diff --check passed. All jobs terminal; changes uncommitted/unpushed.
- Next: precise template register fields and actual evaluation/public/gather loop length families; use RingInputs for intermediate bounds and strong Ready after ops. Moves/drop still have blank scratch requirements, so either establish actual prior clear bounds or generalize their primitive checks as needed. Close full KeyGen runtime, then Dec/reduction/Submission/global comparison. Goal active.

### Evaluator input loading and exact template bounds (2026-11-25)

- Added KeyTimeMoveScratch, KeyTimeRead, KeyTimeEvalInputs and aggregate imports. check_mvPc_scratch/check_dropPc_scratch accept pTop initial helpers, prove cleared helper outputs with the original wMv/wDr cost. compile_drop_scratch/compile_mvR_scratch/compile_mv_scratch preserve upper-bound vector a with no blank-helper premises; actual compiler/frame and alias exclusions unchanged.
- compile_takeC charges the real cp-destination-from-counter then counted move. compile_readFieldC covers the full actual saved-source copy, off initializer, drop, len initializer, take; explicit fieldResult has destination len, source-copy29=inputsource, counter30=len, scratch39/40=M. Cost <=(42*(off+len)+50)*(2*M+5), assuming off,len,input bounds<=M and bit source length1. Top, other-register, low-tape, and RingInputs preservation proved.
- compile_readPublicFieldC uses symbolic take-sum/getD bound and publicFieldLengths_sum, never evaluates concrete encodings. compile_evalFieldsC composes actual four fields (dst2/index1, dst4/index3, dst0/index4, dst1/index5), time4*(42*MPKsize+50)*(2*M+5). evalFieldsResult_outputs gives each exact field-length bound; evalFieldsResult_other preserves all registers except outputs0/1/2/4 and scratch29/30. RingInputs preserved. compile_evalFieldsC_Dc conditional input<=2^120, bit length1 gives <=2^250.
- EvalLengths records all19 exact initializer template lengths. evalInitBounds_lengths proves them from actual templateBounds; EvalLengths.evalFields preserves all through loader. evalInitBounds_bit preserves false-bit length1. compile_evalLoad_Dc certifies actual initializer+loader prefix <=2^251 for input<=2^120. evalLoad_invariants returns RingInputs and EvalLengths; this is the evaluator prefix, not evalC nor full KeyGen.
- Aggregate build passed9790 jobs (/tmp/explut-key-time-eval-load-build.log). Primitive check only propext; movement/read/loader/prefix/invariants audits standard axioms only (/tmp/key-time-eval-load-audit.lean). No sorry/custom axiom/native_decide, git diff --check passed. All jobs terminal; changes uncommitted/unpushed.
- Next: actual evalC loop families, using EvalLengths, precise fieldResult output bounds and scratch-tolerant arithmetic/movement. Then key input/preparation/candidate/public/gather/acceptance stage bounds and full KeyGen runtime. Dec/reductions/Submission/global comparison still open. Goal active.

### Final-table coefficient loop runtime (2026-11-25)

- Added KeyTimeLayout and KeyTimeCoefV, aggregate imports. layout M N K b assigns per-register caps b, exact physical templates35=K/36=N/37=38=NK, other physical scratch=M. layout_inputs/le_layout translate whole-tape invariants; layout_op preserves the layout when destination cap>=NK; layout_copy when source cap<=destination; layout_tail preserves it. rep_fixed specializes actual rep_family to a fixed length envelope, using tailB monotonicity; no change to program/counter semantics.
- evalInstructionTime=operationBound M N K M+(2*M+5) covers both arithmetic/control. compile_vBody certifies actual conditional-add/tail/multiply body within same layout, cost3*T+1. compile_coefVC includes all3 initialization copies, R iterations, final rotation, total4*T+R*(2*M+3*T+5)+2. Explicit requirements: Al/Pw caps>=NK, Z<=Al, One<=Pw, TW<=Cu, Cu<=R, and layout RingInputs. compile_cfV additionally charges actual predicate-stream copy (Cs<=Cp).
- evalInstructionTime_concrete<=2^341; compile_coefVC_concrete<=2^368 for M2^120,N2^24,K2^16,R2^22 with the above explicit register-cap conditions. This is a conditional actual coefficient-routine certificate, not evalC or full KeyGen. Numeric proof uses exponentiation.threshold1000 and calc/norm_num rather than omega's recursive evaluation of huge powers.
- Aggregate build passed9794 jobs (/tmp/explut-key-time-coef-v-full-build.log). layout_op/rep_fixed/coefVC/generic+numeric/cfV audits standard axioms only (/tmp/key-time-coef-v-audit.lean); no sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: extend layout primitives to exact register-cap transforms for growing queues (append) and generic initialized counter updates. Alpha coefficient bitBody doubles rCnt for14 rounds and needs a growing family (2^j); uBody/coefAC can then use a fixed outer envelope. Matrix routines agC/matAddC need linear queue families, followed by ginvMul/mulPK/autPK/chain/jBody/step/evalC composition with real input caps. Then full KeyGen stages; Dec/reductions/Submission/global comparison pending. Goal active.

### Growing bit counter and full alpha coefficient runtime (2026-11-25)

- Added KeyTimeGrowth, KeyTimeBitLoop, KeyTimeCoefA, aggregate imports. layout_update transports register-cap updates to physical tapes; layout_copy_update/clear_update preserve exact new caps. layout_append charges actual append and updates only destination cap, with source+destination<=M; helper39/40 fit layout scratch=M. RingInputs.update_layout preserves inputs for a cap<=M.
- compile_bitBody handles actual conditional rho, predicate tail, counter self-append. bitBodyTime=2*T+1+(4*M+6)*(2*M+5), T=evalInstructionTime. compile_bitLoop uses gamma j=layout(update b rCnt (2^j)), including iterSupT monotonicity, input counter cap1/output2^e, no fixed-envelope approximation for the doubling. Requires Cb<=e, 2^e<=M, E cap>=NK. Concrete14-bit loop<=2^348.
- compile_uBody charges actual E copy, counter reset from Bit1=1, bit-count copy, inner bit loop, add and multiply. Its output is widened back to the original layout only after using 2^e<=bCnt. alphaEntryTime=5*T+e*(2*M+bitBodyTime+4)+2, concrete<=2^349. compile_coefAC includes3 initialization copies, R entry iterations, finalmul/rot; time5*T+R*(2*M+alphaEntryTime+4)+2. compile_coefAC_concrete<=2^375 at e14,R2^22,M2^120,N2^24,K2^16 under explicit register-cap premises. compile_cfA includes actual predicate stream copy Cs<=Cp. Full evaluator callers still must establish these caps.
- Aggregate build passed9800 jobs (/tmp/explut-key-time-coef-a-full-build.log). Append/bitloop/generic+numeric/uBody/coefAC/cfA audits standard axioms only (/tmp/key-time-coef-a-audit.lean); no sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: actual matrix routines agC/matAddC with linear queue families using layout_append, then ginvMulC/mulPKC/autPKC and chain/jBody/step/evalC composition. Both actual coefficient routine families now have conditional runtime certificates. Full KeyGen, Dec/reduction/Submission/global comparison remain open. Goal active.

### Linear gadget and matrix-add output queues (2026-11-25)

- Added KeyTimeMatrixGrowth/KeyTimeMatAdd and aggregate imports. appendAllowance M=(4*M+6)*(2*M+5), layout_append_uniform; cap_update_le/cap_reset support exact cap transforms and safe widening. compile_agBody appends one NK word then doubles X0. compile_agLoop gamma j updates Ro0 to j*NK, starts0, endsR*NK. compile_agPost uses exact MA caps through copy, two zero-block appends, final segment append before widening.
- compile_agC certifies actual clear/copies, loop, and assembly. Requirements include X0cap=NK, Al<=X0, TK<=Ci<=R, R*NK<=Ro0cap, 2*Ro0cap+2*TKNKcap<=MAcap plus RingInputs. Actual code unchanged. Conditional concrete R2^16 cost<=2^362.
- moveAllowance M=(2*M+3)*(20+10*M); layout_moveR handles actual moves with nonblank scratch. compile_maBody covers two copies/two moves/add/append, preserving all caps except growing AccL. compile_maLoop gamma j updates AccL to j*NK. compile_matAddC includes stream copies, accumulator clear, counter copy, and loop. Requirements X0/X1caps=NK,Z<=NK,AccL<=Ro0,MOut<=Ro1,T4K<=Ci<=R,R*NK<=AccL. Conditional concrete R4*2^16 cost<=2^364.
- Integration caveat: these same-layout routine certificates expose scratch-cap requirements (e.g. Ci<=K for agC versus Ci>=4K for matAddC). Do NOT assume one common envelope satisfies incompatible requirements. Before full caller composition, derive asymmetric prefix/output cap transforms using actual initial overwrites (layout_copy_update/clear_update), so scratch caps shrink legitimately and output matrix caps remain precise. Loop/post certificates are reusable for that strengthening. No full evaluator/KeyGen claim.
- Aggregate build passed9804 jobs (/tmp/explut-key-time-matrix-growth-build.log). Loop/generic/numeric agC/matAddC audits standard axioms only (/tmp/key-time-matrix-growth-audit.lean); no sorry/custom axiom/native_decide, git diff --check passed. All jobs terminal; changes uncommitted/unpushed.
- Next: asymmetric initialized scratch/output caps for matrix routines, then ginvMulC/mulPKC/autPKC and chain/jBody/step/evalC composition; full KeyGen and Dec/reduction/Submission/global comparison remain open. Goal active.

### Asymmetric gadget bounds remove old scratch-cap restrictions (2026-11-25)

- Added KeyTimeGadget and aggregate import. layout_copy_cap permits exact copy followed by safe widening to a chosen cap. compile_agPre_exact certifies real clrRo0/cpX0Al/cpCiTK from arbitrary prior scratch caps, output update(gadgetBase)Ro0 0 where gadgetBase updates X0=NK,Ci=inputTK. Only Al<=NK is required in addition to RingInputs.
- compile_agPost_exact returns updateMA(2*Ro0+2*TKNK), independent of old MA cap; every intermediate copy/append output is retained precisely. compile_agC_exact composes prefix, existing linear loop, and exact assembly: output gadgetResult updates X0=NK,Ci=inputTK,Ro0=R*NK,MA=2*R*NK+2*inputTKNK. Requirements TK<=R and final matrix size<=M, not old scratch cap inequalities. gadgetResult_inputs/fields/other expose readiness, all four updated caps and preservation elsewhere.
- compile_agC_exact_concrete<=2^362 now requires only RingInputs M2^120,N2^24,K2^16,Al<=NK,TK<=K,TKNK<=K*NK. Old X0/Ci/Ro0/MA can have arbitrary bounds<=M. This closes the previously noted Ci-cap conflict for entering agC after a larger-counter routine, but other callers/routines still need analogous exact transforms.
- Aggregate build passed9806 jobs (/tmp/explut-key-time-gadget-build.log). Prefix/post/full/numeric/readiness/field audits standard axioms only (/tmp/key-time-gadget-audit.lean); fields only propext. No sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: strengthen matAddC similarly. Its maBody copies both X0/X1 from Z before use, so allow arbitrary old caps by tracking those copies to NK and widening the final X caps to max(old,NK). Important: rep uses iterSupT including iteration0, so a loop output cannot simply shrink an arbitrary initial X cap to NK; retain max unless an actual pre-loop overwrite exists. maPre must track exact Ro0=inputAccL,Ro1=inputMOut,Ci=inputT4K,AccL=0; final AccL=R*NK. Then ginvMul/mulPK/autPK and full evaluator/KeyGen composition. Dec/reduction/Submission/global comparison remain pending. Goal active.

### Asymmetric matrix-add bounds and safe operand suprema (2026-11-25)

- Added KeyTimeMatAddExact and aggregate import. compile_maBody_flexible permits X0/X1 caps>=NK, tracks actual Z copies to NK in intermediate layouts, performs both moves/add/append, then widens operand caps back. This allows initial larger caps without incorrectly charging append from those larger values. compile_maLoop_flexible uses the same linear AccL=j*NK family.
- matrixAddScratch updates X0/X1 to max(inputcap,NK), respecting iterSupT's inclusion of iteration0. matrixAddBase additionally sets Ro0=inputAccL,Ro1=inputMOut,Ci=inputT4K. compile_maPre_exact charges actual stream copies/clear/counter copy; initial input is safely widened only for X scratch. matrixAddResult sets final AccL=R*NK. compile_matAddC_exact now requires only RingInputs, Z<=NK,T4K<=R,R*NK<=M; no old operand/stream/counter/output-cap relationships.
- matrixAddScratch_inputs/base_inputs/result_inputs prove all layout bounds and templates preserved; matrixAddResult_fields/other expose all six changed caps and unchanged registers. compile_matAddC_exact_concrete retains <=2^364 at M2^120,N2^24,K2^16,R4*2^16 with only Z<=NK and T4K<=4K beyond RingInputs. This resolves matrix-adder scratch-cap integration restrictions noted earlier; full evaluator composition remains open.
- Aggregate build passed9808 jobs (/tmp/explut-key-time-mat-add-exact-build.log). Flexible body/loop/exact prefix/full/numeric/readiness/field audits standard axioms only (/tmp/key-time-mat-add-exact-audit.lean); fields only propext. No sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: ginvMulC/digAccC/mulPKC/autPKC actual nested matrix algorithms (SigabaNeoStd/Lattices/ProgAlgo/Mersenne/VMMat.lean and KeyVM.lean), using precise copied counters and linear output queues. Then chain/jBody/step/evalC, full KeyGen stages. Dec/reductions/Submission/global comparison still pending. Goal active.

### Actual digit accumulation runtime and cleanup (2026-11-25)

- Added KeyTimeDigitAcc and aggregate import. layout_drop preserves a layout using scratch-tolerant counted drop and moveAllowance. compile_digAccBody composes actual cpUpTK1/dropUpDn/mvRElDE/dig/mul/add; digitBodyTime=F+2*moveAllowance+3*T with F2*M+5,T=evalInstructionTime.
- Important namespace collision found and fixed: Prog.rDn (KeyTryVM) is34, but MVM.rDn used by VMMat.digAccBody/digAccC is54. All new counter references explicitly use MVM.rDn. Initial type mismatch exposed this; no alternate-code theorem was accepted. Explicit rw[digAccBody/digAccC] retained for clear matching; no transparency-option workaround remains.
- digitWide sets accumulator capNK and Up/Dg/Pr capsM (these are cleared later, M safely includes loop iteration0). Actual two-copy prefix sets Dn=inputTK and El=NK under DA<=NK,Z<=NK. compile_digAccC certifies real initialization, R rounds and all4 cleanup clears; time6*F+R*(2*M+digitBodyTime+4)+2. Requires TK<=R plus RingInputs, no old temporary/counter cap restrictions.
- digitResult restores Up/El/Dg/Pr bounds0, DA=NK,Dn=inputTK, all other register caps unchanged. Readiness/fields/other proofs included. compile_digAccC_concrete<=2^363 for M2^120,N2^24,K2^16,R2^16, with only DA<=NK,Z<=NK,TK<=K beyond RingInputs.
- Aggregate build passed9810 jobs (/tmp/explut-key-time-digit-acc-build.log). Body/prefix/full/numeric/readiness/field audits standard axioms only (/tmp/key-time-digit-acc-audit.lean), fields only propext. No sorry/custom axiom/native_decide, git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: VMMat iBody (four digAccC calls), jPre/jBody/rPart and gBody for ginvMul; tLoop/tOut for output; autMat/aStep/autPK and chain/jBodyK/step/evalC. Use exact copied/reset cap transforms and beware overlapping register names. Full KeyGen/Dec/reductions/Submission/global comparison remain open. Goal active.

### Inner kernel and matrix column bounds (2026-11-25)

- Added KeyTimeInner and KeyTimeColumns, both imported by the aggregate. InnerCaps records explicit cap hypotheses. compile_iBody composes all four actual digit accumulations, twelve copies and two moves, with conditional concrete time <=2^366.
- compile_jBody includes actual stream resets, repeated inner kernel, and both output moves; concrete bound <=2^388 permits Ci up to4*K. compile_gBody includes actual accumulator resets, GX copy, inner kernel and output moves, bound <=2^368. These are conditional same-layout certificates; callers still need to establish InnerCaps and the stream/counter inequalities using actual prefix transformations.
- Fixed the two newline-before-.mono parsing errors without changing statements. Aggregate build passed9814 jobs (/tmp/explut-key-time-columns-final-build.log). All three concrete compiled-code theorems audited with only propext, Classical.choice, Quot.sound (/tmp/key-time-columns-audit.lean). git diff --check passed before this documentation append. All build/audit sessions terminal. Changes remain uncommitted/unpushed.
- Next: actual rPart/mulPKC, ginvMulC prefixes and output transposition, autPKC, then evaluator and full KeyGen runtime. Dec/reductions/Submission/global comparison remain open. Goal active. User asked ETA: stated days-scale provisional estimate, not a measured deadline.

### Complete matrix and automorphism routine certificates (2026-11-25)

- Added KeyTimeMatrix and KeyTimeAutomorphism; both imported by aggregate. MatrixCaps extends InnerCaps with explicit stable prefix/stream/output/counter inequalities. layout_move handles actual counted moves with nonblank scratch.
- Certified actual tBody/tLoop/tOut, rPre/rPart, gPre, mulPKC and ginvMulC, including all setup, optional row drop, column loops, transposition and output moves. Concrete compiled mulPKC <=2^412 and ginvMulC <=2^390 for M2^120,N2^24,K2^16,Ci allowance4K,Cj allowance2K, assuming stated RingInputs/MatrixCaps and counter/stream inequalities.
- Certified actual aBody/autMatC/aStep/autPKC. autPKC includes the repeated entrywise automorphism, ordinary multiplication, saved digit stream, inverse product and stream restoration. Concrete step bound <=2^364 and full autPKC <=2^414 when P<=2^22 and explicit output/saved-stream conditions hold. No full caller claim: MatrixCaps and all extra inequalities still need to be established by actual caller prefixes or suitable asymmetric cap transforms.
- Initial numeric omega proofs hit recursion limits despite maxRecDepth10000; replaced by monotone calc/gcongr using existing column bounds and norm_num on the final closed arithmetic. No statement changes or axioms added.
- Aggregate build passed9818 jobs (/tmp/explut-key-time-automorphism-build.log). Audited rPart,tLoop,mulPKC_concrete,ginvMulC_concrete,autMatC,autPKC_concrete: only propext,Classical.choice,Quot.sound (/tmp/key-time-automorphism-audit.lean). New modules contain no sorry/native_decide/custom axiom; git diff --check passed. All sessions terminal. Changes uncommitted/unpushed.
- Next: chainC with Pw2=2^j loop invariant. Actual chPre copies Tb toS, tails/drops byCt, digS2, copies/movesGX fromHs, dropsHs; autStep copies MAdSs, PPw2, autPKC, MAMOut, SsMAd. chBody branches then doublesPw2; chainC copies SsAautW,HsHW,Pw2Bit1,CtTb then repeats. Need safe cap update/widening under Pw2 doubling, preserve MatrixCaps, boundP>=2^B and <=2^22. Then jBodyK/step/evalC with coefficient-scratch cap normalization; full KeyGen/Dec/reductions/Submission/global comparison remain open. Goal active.

### Actual exponent-doubling chain runtime (2026-11-25)

- Added KeyTimeChain and aggregate import. ChainCaps extends MatrixCaps with exact saved/source-stream equalities, template-copy and output bounds. ChainCaps.update_pw2 preserves every condition under arbitrary exponent-cap updates (register15).
- compile_chPre covers all real copies/tail/drop/digit/move operations. compile_chainAut covers the real four copies around autPKC. compile_chBody includes the conditional aut/drop branch and actual self-append; output updates only Pw2 to twice its prior cap.
- compile_chainLoop uses gamma j=layout(update b Pw2 (2^j)), rep_family, actual counter tails, and a monotone envelope; starts exponent1, returns2^B. Bounds require Ct<=B,2^B<=M,2^B<=Pcap, plus explicit chain and matrix hypotheses. compile_chainC includes all four real initialization copies and therefore accepts arbitrary previous Pw2 cap. No assumption that the loop shrinks an unmodified register was introduced.
- Numeric body<=2^416, fullchain<=2^422 for B22,Pcap2^22,Ci4K,Cj2K,M2^120,N2^24,K2^16. compile_chainC_concrete returns updatedPw2=2^22 and remains conditional on ChainCaps/counter bounds. No full evaluator claim yet.
- Aggregate passed9820 jobs (/tmp/explut-key-time-chain-build.log). Audits (/tmp/key-time-chain-audit.lean): ChainCaps.update_pw2 onlypropext; prefixes/body/loop/fullconcrete onlypropext,Classical.choice,Quot.sound. New module no sorry/native_decide/custom axiom. git diff --check passed. All sessions terminal; uncommitted/unpushed.
- Next bridge: coefficient code overlaps matrix scratch. Pw35=S (large matrix stream), Cu36=S2, E37=Ac0 (NK), Cnt38=Ac1 (NK), Cb39=Co0 (large), Cp40=Co1. Existing coefAC requires Pw<=E and Cb<=14, incompatible with this stable matrix envelope. Use actual coefPre copies to reset Pw toNK and Cu toTW before loop, then widen back to old caps afterward. For uBody, actual cpCbTe can shrink Cb internally before bitLoop; keep original larger Cb cap at outer-loop iteration0, restore it by widening after the inner loop. Keep Cnt2^14<=oldCnt and E>=NK. This should remove incompatible scratch hypotheses without changing actual code. Then connect coefficient+chain+agC+ginvMulC+matAddC in jBodyK and step/evalC. Full KeyGen runtime, Dec, reductions, Submission/global comparison remain open; goal active.

### Shared scratch normalization and complete evaluator envelope (2026-11-25)

- Added KeyTimeCoefFlexible and KeyTimeEval, imported by aggregate. compile_uBody_flexible tracks the actual cpCbTe before bitLoop; only Te<=e is needed, not oldCb<=e. The inner-loop result is widened back after the real reset. coefficientBase resets Pw=NK,Cu=inputTW; actual coefPre certified to this base, then restored to the larger caller envelope. Eliminates oldPw<=E and oldCu<=R restrictions. CoefficientCaps records remaining compatible inequalities. Full cfA/cfV (including predicate copy) bounds <=2^376/2^369.
- Added gadgetResult_le and matrixAddResult_le to widen exact initialized outputs into a stable shared envelope. EvaluatorCaps collects all caller obligations. compile_jBodyK_concrete composes the actual coefficient, chain, gadget, inverse product, matrix add and final ring updates (<=2^424). compile_stepPre_concrete<=2^414; compile_stepK_concrete<=2^452; compile_evalC_concrete covers actual15alpha iterations and finalvalue step<=2^458.
- Defined explicit evaluatorEnvelope with most streams2^120 and small caps on ring scratch/counters/templates; proved evaluatorEnvelope_top, RingInputs and all EvaluatorCaps fields. compile_evalC_envelope therefore certifies actual evalC on this explicit input/output length envelope without abstract cap hypotheses. This proves compatibility of the combined inequalities, NOT dominance of the actual loader output yet.
- Aggregate build passed9824 jobs (/tmp/explut-key-time-eval-build.log). Audit /tmp/key-time-eval-audit.lean covers flexible coefficient routines, jBody/step, envelope witness, complete evalC: standard axioms only. New modules no sorry/native_decide/custom axioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Critical remaining entry bridge: evalInitC initializes19templates but does not reset all small-cap scratch. evalFieldsC overwrites register30=MVM.rP with a field length, potentially larger than2^22. Thus do NOT assert evalLoad output<=evaluatorEnvelope from top bounds alone. Actual autStep overwritesP before using it, but current chain certificate starts with smallPcap. Other small scratch includesAl,X0/X1,Ac0/Ac1,DA,Ci,Cj,Cst,Cj2,Ct,Pw2. Need strengthen actual prefix/cold-entry certificates to track these overwrites, or add and prove a semantically harmless scratch-clearing prefix in the real evaluator path and update correctness/size/time proofs coherently. No algorithm edits made this stage. evalPublicC currently seq(evalFieldsC D)evalC in KeyEvalFront; evalReadyC seq(evalInitC D)(evalPublicC D). KeyEvalFront correctness uses field outputs/templates, so inspect exact dependencies before choosing a normalization approach.
- Full KeyGen runtime, Dec, reductions, Submission/global comparison remain open. Goal active.

### Real evaluator scratch normalization and complete entry bridge (2026-11-25)

- Changed the actual evalPublicC path in KeyEvalFront to evalFieldsC;evalScratchC;evalC. evalScratchC clears exactly13dead work registers: X0,X1,Ac0,Ac1,DA,Al,Ci,Cj,P,Pw2,Ct,Cst,Cj2. Preserves predicate, loaded public fields, all templates and saved master keys. wf_evalScratchC and evalScratchC_roS proved; exec_evalPublicC transports StepIn via of_roS and every CoefIn/input field through the clears. Existing external correctness theorem statements unchanged.
- Updated weight_keyPrepareC proof in KeyPrepareSize to use kernel-checked codeWeight(evalScratchC)+codeWeight(evalC)<=2^20. Existing prepare budget, state bound<=2^220 and description bound<=2^620 remain unchanged; no size claim weakened.
- Added KeyTimeEvalReady and aggregate import. scratchCaps tracks all13actual clear outputs. compile_evalScratchC certifies input/output layouts and13*(2M+5). scratchCaps_le_envelope checks all64registers from EvalLengths and inputtop; small template caps follow exact initialized lengths, dead scratch becomes0. compile_evalScratchC_Dc accepts arbitrary prior scratch under RingInputs and EvalLengths, costs<=2^130 and returns the explicit evaluatorEnvelope.
- compile_evalReadyC_Dc now covers the actual complete initializer, four public-field readers, scratch clears and evalC. Input only RingInputs M2^120,N2^24,K2^16; output explicit envelope, totaltime<=2^459. This closes the entry mismatch (including field-reader register30 versus exponentP), without assuming old scratch is small.
- Aggregate build passed9826 jobs (/tmp/explut-key-time-eval-ready-final-build.log). Axiom audit /tmp/key-time-eval-ready-audit.lean passed for exec_evalPublicC, KeyCore.keySpec_keyMP_Dc, KeyCore.descLen_keyMP_Dc, clear certificate, envelope dominance and complete evalReady certificate; only propext,Classical.choice,Quot.sound. First audit used incorrect unqualified namespaces for twoKeyCoretheorems, corrected and rerun successfully. No sorry/native_decide/custom axioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: keyEvalPrepareC adds cp8A/cp14savedMPK after evalReadyC; keyPrepareC includes keyInputC before this. Prove remaining input/prepare runtime with physical ring template initialization bounds and full result caps. Then actual proposal/acceptance/correction/front/output runtime and full keyMP cost. Dec/reductions/Submission/global comparison remain pending; goal active.

### Complete key preparation runtime (2026-11-25)

- Added KeyTimePrepare and aggregate import. RingInputs.initBits proves bit-constant setup preserves physical templates. keyInputResult tracks both actual fixed-field reads intoMPK17 and trapdoor16; keyInputResult_inputs preserves RingInputs. compile_keyInputC_Dc covers clear6,bitsC,and both unary-offset field readers, time<=2^250 from arbitrary inputtop2^120.
- preparedBounds is layout(M2^120,N2^24,K2^16) with everyVMregistercapM; physical ring templates retain their distinguished caps. compile_keyEvalPrepareC_Dc composes complete evalReadyC and actual cp8A/cp14savedMPK, time<=2^460. compile_keyPrepareC_Dc composes input loader and evaluation preparation, time<=2^461, outputpreparedBounds. Input remains RingInputs M2^120,N2^24,K2^16; actual machine enterP template setup still must be connected later. Actual production KeyCore.program uses compile(keyPrepareC D) as its first phase (KeyCore.lean:37).
- Aggregate build passed9828 jobs (/tmp/explut-key-time-prepare-build.log). Audit /tmp/key-time-prepare-audit.lean passed allfive new main/input/readiness theorems, onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/custom axioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next actual phase: KeyCore.sampleP writes nPI Dc*Dc.N*Bk fair bits to rCoin37, followed by candidateTryC. keyCoinCount_Dc already gives<2^106; nPI Dc<=2^66 fromcorrection_counts_Dc. candidateInitC has same clr6/bitsC/templateOps shape; candidateInitOps setsTBk=B,TKmB=K-B,TN=N,C2=encRM const,Dqn=nPI,Z=NK, preserving coins37 and saved8/14/16. Decoder decBody copiesDxTBk,moves coins byTBk,appendsDx thenTKmB toDw. decC clearsDw,copiesDnTN,repeatsdecBody,subDoDwC2. decQC clearsDq,repeatsDqn(decC;appendDqDo), candidateC copies9Dq. Need exact per-element outputNK (not stale large Do cap) and linear queue growth to bound these real loops. Runtime op-result API already gives exact destinationNK and unchanged otherregisters; can derive layout_op_update for reuse.
- KeyGen full runtime, Dec, reductions, Submission/global comparison remain open; goal active.

### Actual candidate decoder and linear output queue (2026-11-25)

- Added KeyTimeDecode and KeyTimeDecodeQueue, imported by aggregate. layout_op_update strengthens the general arithmetic API: actual compiled ring operation returns destinationcapNK and all other register caps unchanged, without requiring the old destination cap>=NK.
- compile_decBody tracks actual cpDxTBk, counted coin move, appendDx, appendTKmB. Copied Dx has exactTBk cap before append; outputDw grows by at mostK underTBk+TKmB<=K. compile_decLoop uses gammajDw=j*K. decodeBase safely widens Dx toM (includes iteration0), actual counter copy resets Prog.rDn34=TN. compile_decC covers real clear/copy/loop/sub and returns decodeResult with Do=NK,Dw=R*K,Dx=M,Dn=inputTN. Explicitly qualified Prog.rDn34 to avoid MVM.rDn54 collision. Concrete per-ring decoder time<=2^342.
- decodeResult_le permits safe recovery of a broad outer-loop scratch envelope after decoding. compile_decQBody uses exact Do=NK for appending before widening; outputDq grows byNK. decodeQueueBase widens four scratch registersDx/Dn/Dw/Do toM; compile_decQLoop uses gammajDq=j*NK and actual loopcounter. compile_decQC includes actual initial clearDq. AtR2^24,Q2^66, outputqueuecap2^106<=M2^120 and time<=2^412. Input still requires RingInputs and candidate-template boundsTBk+TKmB<=K,TN<=N,Dqn<=2^66; candidateInitC must establish them next.
- Aggregate build passed9832 jobs (/tmp/explut-key-time-decode-queue-build.log). Audit /tmp/key-time-decode-queue-audit.lean passed op-update/body/decoder/fields/queuebody/loop/fullconcrete; only standardpropext,Classical.choice,Quot.sound (fields onlypropext). No sorry/native_decide/customaxioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: certify candidateInitC's six template initializers with existing templateOps runtime API, establish actual candidate-template length bounds, apply decQC and final cp9Dq. candidateInitOps weight sum=3B+3(K-B)+3N+4NK+3nPI; nPI Dc<=2^66 via correction_counts_Dc. Bk<=K via Bk_lt_Kc.le. Coin sample has keyCoinCount_Dc<2^106 and must be connected to preparedBounds. Then tryKeyC/proposal/correction/acceptance, machinefront/output, fullKeyGen cost. Dec primitive and reductions/Submission/global comparison remain pending; goal active.

### Actual fair coins and complete candidate generation (2026-11-25)

- Added KeyTimeCandidate and KeyTimeCoins; both imported by aggregate. candidateInitResult tracks the actual bit setup and all six template writes. candidateInitOps_valid, candidateInitWeight and candidateInitResult_inputs/lengths establish actual initializedTBk=B,TKmB=K-B,TN=N,Dqn=nPI and preservation of physicalRingInputs. Exact initializer weight includes +7 (the previous handoff omitted fixed template overhead); kernel-checked arithmetic establishes <=2^120 atDc,Bk.
- compile_candidateInitC_Dc<=2^250; compile_candidateC_Dc composes actual initializer, decQC with its proven template bounds and finalcp9Dq, <=2^414, returningpreparedBounds from arbitrary inputRingInputs M2^120. Existing Bk=18750,K=65536 and nPI<=2^66 discharge the decoder requirements.
- cert_sampleP handles actual KeyCore.sampleP: physical clear ofcoinregister followed by framedcoinsF n. Uses existing atbb_coinsF/vb_smp with scratchS=M2^120 (no unjustified blank-length assumption), n<=2^106. Frame touches VMcoin78 and physicalscratch0..5; outputpreparedBounds preserved. Numeric time<=2^234. cert_sampleCandidate_Dc<=2^416 uses KeyCore.keyCoinCount_Dc; cert_prepareSampleCandidate_Dc<=2^463 composes preparation, real fair-bit generation, and candidate decoding.
- Aggregate build passed9836 jobs (/tmp/explut-key-time-coins-build.log). Audit /tmp/key-time-coins-audit.lean passed initializedlengths,initializer,candidate,sampler and both composedprefixes: standardpropext,Classical.choice,Quot.sound only (lengths propext andQuot.sound). No sorry/native_decide/customaxioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: actual candidateTryC = seq(candidateC D B)(tryKeyC D B r), so remaining tail is tryKeyC frompreparedBounds. Inspect actual proposalC, its initialization and correction/public multiplication/decomposition routines, then acceptance and zero-on-rejection. FullKeyCore.program composition needs associativity around compile(candidateTryC), followed by enter/parse/check/invalid/output framing and machineclock cost. Dec primitive/reductions/Submission/global comparison remain open; goal active.

### Actual proposal queue arithmetic kernels (2026-11-25)

- Added KeyTimeQueueArithmetic and aggregate import. QueueArithmeticCaps records ring scratch/zero-copy requirements. compile_ipBody/ipC certify actual two stream moves, multiplication, accumulator addition and counter loop. compile_grBody/gadRecC certify actual digit recomposition, including initialpowercopy and doubling by ring addition (not unbounded word concatenation).
- compile_signedDotC composes all six copies, both actual inner-product loops and final subtraction. Uses layout_op_update on final subtraction so outputIa cap is exactlyNK for later queue append; remaining register caps unchanged.
- Generic time functions retain arbitrary loop boundR. Conservative concrete preparedBounds certificates allow all register lengths/counter up toM2^120: ipC and gadRecC<=2^466, signedDotC<=2^468. These are real-code certificates frompreparedBounds, not yet full proposalC. Tighter caller-specific counts can reuse generic theorems if needed.
- Aggregate passed9838 jobs (/tmp/explut-key-time-queue-arithmetic-build.log). Audit /tmp/key-time-queue-arithmetic-audit.lean passed generic and concrete kernels: onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms; git diff --check passed. All sessions terminal; uncommitted/unpushed.
- Next loader bridge is KeyGather.lean (there is no KeyFetch.lean): fetchRingC N K j =natC2B1(j*NK);cp1src0;drop1by2;cp3Z;mvR3from1. gatherAppendC recursively fetches/appends4from3; gatherC clears4 first. Need exact fetched3 capNK and linear output4 cap length(js)*NK; indices bounded by existing Gather/PublicSizeInputs. loadFamilyC copies0fromsrc, gathers, copiesdstfrom4. This supplies exact source queue size for autQC.
- autQC rotates Qa using cpQxZ,mvRQxQa,autQyQxQk,appQaQy. Current move certificate does not shrink static Qa, so use conservative affine Qa bound S+j*NK with S+R*NK<=M and actual aut outputQy=NK beforeappend; do not claim a same-cap queue proof from the current move API. autDotC savesQc56,autQC,restoresQc,ipC. Remaining publicrows/gadgetdecomposition/correction/assembly/acceptance/front still open, as are Dec/reductions/Submission/global comparison. Goal active.

### Actual coordinate gathering and automorphic correction kernel (2026-11-25)

- Confirmed the previous gather aggregate build completed successfully (9840 jobs, /tmp/explut-key-time-gather-build.log); no live build remained. KeyTimeGather certifies actual nat offset/copy/drop/fetch, exact fetched word NK, recursive gather output length(js)*NK, and loadFamilyC including both copies. Concrete loadFamilyC bound <=2^316 under indices/list length <=2^66, bit/zero templates and RingInputs. familyResult preserves input readiness and records destination length. Cert.seq_assoc avoids expanding huge compiled programs just to reassociate sequences.
- Added KeyTimeShift and aggregate import. compile_autQBody certifies actual zero copy, stream move, automorphism and append, using exact operation output Qy=NK before append. compile_autQC tracks affine Qa cap bQa+j*NK, explicitly including iteration zero and requiring bQa+R*NK<=M; it does not assume the movement certificate shrinks source caps. compile_autDotC composes actual saveQc56, autQC, restoreQc, ipC, with output autDotResult preserving other caps. Concrete time <=2^414 for R2^66, initial Qa<=2^106, QueueArithmeticCaps and RingInputs M2^120. This is a conditional kernel bound, not yet a full correction/proposal or KeyGen runtime result.
- Direct Lean check passed; aggregate build passed 9842 jobs (/tmp/explut-key-time-shift-build.log). Audit /tmp/key-time-shift-audit.lean checked gather loader/readiness and all four new kernel certificates: only propext, Classical.choice, Quot.sound. No sorry/native_decide/custom axioms in either new module; git diff --check passed. Build and audit sessions terminal. Changes uncommitted/unpushed.
- Next: bridge correctionLoadC's three actual loads (16->Qa indexed trap row, 17->Qb indexed digit row, 9->Ia singleton candidate) to exact familyResult caps. correctionInlC then natQc K, natQk(rowExponent D i.val), autDotC. Existing correction_counts_Dc bounds source enum counts by2^66; rowExponent_lt bounds exponent<2*N. Need preserve bit/zero and scratch caps through loaders, prove output Ia cap NK (generic autDot preserves initial Ia, which singleton load supplies), then append correction coordinates to18 with linear growth. Existing correctionCoordC/AppendC/C handle all PIdx coordinates. Public rows/gadget decomposition/assembly/acceptance/front remain open, as do Dec/reductions/Submission/global comparison. Goal active.

### Actual three-source correction loader (2026-11-25)

- Added KeyTimeCorrectionLoad and aggregate import. compile_correctionLoadC composes the real three loadFamilyC calls in correctionLoadC: saved trapdoor16->Qa, digits17->Qb, candidate9->Ia. correctionLoadResult tracks their actual destination/scratch updates. correctionLoadResult_lengths proves Qa=K*NK,Qb=K*NK,Ia=NK; correctionLoadResult_inputs preserves RingInputs given K*NK<=M; correctionLoadResult_other preserves every register outside0..4,Qa,Qb,Ia. compile_correctionLoadC_Dc gives time<=2^318 using correction_counts_Dc, assuming caller bit/zero templates and RingInputs.
- Important proof issues resolved: correctionLoadC uses Classical DecidableEq whereas inferred finite instances can differ. index_classical proves Enum.index independent of DecidableEq by Subsingleton.elim, allowing the three-call certificate to match actual code. Explicit PIdx (Wb D) (Jh D) (setting D).tau (setting D).E.W syntax retained. A local classical PIdx DecidableEq is also declared. Generic lengths and readiness compile.
- Numeric proof must rewrite Dc.N=2^24 and Dc.K=2^16 first, then norm_num only time definitions. Params.Kc is irreducible; change to2^16 failed, and norm_num unfolding the full Dc/time expression produced kernel deep recursion after minutes. Rewriting dimensions first solves in seconds. correctionLoadTime_Dc is a separate arithmetic lemma. Current file has maxRecDepth100000; no custom axioms/sorry/native_decide.
- Aggregate build passed9844 jobs (/tmp/explut-key-time-correction-load-build.log). /tmp/key-time-correction-load-audit.lean passed generic loader, result lengths/readiness/frame and concrete loader: onlypropext,Classical.choice,Quot.sound. git diff --check passed. All check/build/audit sessions terminal. Uncommitted/unpushed.
- Next complete correctionInlC runtime: after correctionLoadC, actual natQc K and natQk(rowExponent D i.val), then autDotC. Use result lengths plus result_other to preserve B1,Z,Qx,Qy. Establish QueueArithmeticCaps with Ia=NK and caller x/y/zeroX/zeroY; after the two nat writes use update_layout. autDotC atR=K requires Qa+K*NK<=M (true atDc), and returns Ia unchanged=NK. Preserve unaffected registers for outer correctionAppendC, which appends Ia to18. Non-inl correctionCoordC is a singleton candidate load. Then linear traversal<=2^66 entries. Full proposal still needs public rows, decomposition, assembly, acceptance; fullKeyGen front/clock, Dec, reductions, Submission/global comparison remain open. Goal active.

### Complete per-coordinate correction runtime (2026-11-25)

- Added KeyTimeCorrectionCoord and aggregate import. correctionReady records actual natQc K and natQk(rowExponent); correctionInlResult records the complete autDot output. compile_correctionInlC composes actual correctionLoadC, both natural-number writers, and autDotC. Its assumptions are RingInputs, B1=1,Z<=NK,NK<=Qx/Qy, bounded source index counts,2*K*NK<=M and exponent<=M. No assumption that old Ia already has exact length: loader establishes Ia=NK. correctionInlTime_Dc and compile_correctionInlC_Dc give <=2^416.
- compile_correctionCoordC_Dc handles both branches of the actual correctionCoordC, including singleton candidate loading on inr. Uniform coordinate time<=2^416. correctionCoordResult_acc proves exact capIa=NK. correctionCoordResult_inputs preserves RingInputs (generic2*K*NK<=M,2N<=M). correctionCoordResult_other preserves all registers outside0..4,Qa,Qb,Ia,Qc,Qk,56; in particular18,B1,Z,Qx,Qy and saved9/16/17. These are the interfaces needed for the full append traversal.
- Used explicit local Classical DecidableEq for PIdx and index_classical normalization on the inr singleton to match actual code. A typed time inequality plus simp only avoids recursive expansion of huge concrete code during Cert.mono. Avoid broad simpa[js] on that certificate. Numeric bounds rewrite dimensions and use the prior2^414 autDot bound; no huge concrete code expansion.
- Aggregate passed9846 jobs (/tmp/explut-key-time-correction-coord-build.log). /tmp/key-time-correction-coord-audit.lean passed generic/concrete inl, both-branch coordinate certificate, exactacc/readiness/frame: onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms; git diff --check passed. All sessions terminal; changes uncommitted/unpushed.
- Next: full correctionAppendC traversal and correctionC initializer. Each coordinate returns exactIa=NK and preserves18, then actual app18Ia. To recover the caller envelope safely, widen scratch0..4,Qa,Qb,Ia,Qc,Qk,56 toM while retaining B1=1,Z<=NK,Qx/Qy>=NK and tracking18=j*NK. correctionCoordResult_inputs plus other permits this widening; after append, restoreIa broadM. Induct on list qs (<=2^66 fromcorrection_counts_Dc), preserve18linearcap<=2^106, time about2^484. correctionC clears18 first. Full proposal still needs publicrows/decomposition/assembly/acceptance and KeyGenfront/clock; Dec/reductions/Submission/global comparison pending. Goal active.

### Complete actual correction traversal runtime (2026-11-25)

- Added KeyTimeCorrection and aggregate import. correctionScratch identifies0..4,Qa,Qb,Ia,Qc,Qk,56; correctionBase safely widens only these caps toM, including iterationzero. correctionBase_inputs/le_correctionBase establish readiness and input domination. correctionCoordResult_le recovers the caller envelope when scratchcaps=M, using actual result readiness and frame theorem.
- compile_correctionStep combines actual coordinate code with app18Ia, uses exactIa=NK and preserved18, and restores scratch caps after the append; output18=b18+NK. compile_correctionAppendC inducts over the actual list recursion and gives output18=b18+len(qs)*NK, time len(qs)*(2^416+appendAllowance)+F. compile_correctionClear certifies actual clear18 plus this traversal for arbitraryqs. compile_correctionC_Dc specializes to full Enum.list, uses count<=2^66 and outputsize<=2^106, and gives time<=2^484. Caller requirements remain RingInputsM2^120,B1=1,Z<=NK,NK<=Qx/Qy; no assumption on old output18 or scratch lengths beyondRingInputs.
- Important: directly proving the clear+fullEnum traversal caused kernel deterministic timeout after minutes. Split the arbitrary-list clear theorem from its final specialization; both now check in seconds. Do not reintroduce proof-level simplification over the concrete huge Enum.list.
- Aggregate passed9848 jobs (/tmp/explut-key-time-correction-build.log). /tmp/key-time-correction-audit.lean checked output domination,step,append and fullcorrection: standardaxioms only. No sorry/native_decide/customaxioms; git diff --check passed. Build/audit sessions terminal; uncommitted/unpushed.
- Next missing proposal prefix is keyDigitsC: publicRowsC;targetC;cpQb15;natQcW;natQkK;decRowsC. publicRowC copies0from14, savespositiveCoeffC toQa, savesnegativeReadyC to10, copies0from9, savespositiveGatherC toQb, savesnegativeGatherC to11, rowCountsC then signedDotC. Existing KeyTimeGather, QueueArithmetic and correction traversal APIs can be reused. targetC=targetHeadC;cpQa3;nat2((W-1)*NK);appQa2. decRowsC=clearDq;repQc decRowBodyC. Need these prefixes, then copy17Dq and the now-proven correctionC, assembly/acceptance, fullKeyGenfront/clock. Dec primitive, reductions,Submission/global comparison remain open. Goal active.

### Complete actual gadget decomposition runtime (2026-11-25)

- Added KeyTimeDecompose and aggregate import. compile_digQBody uses exact ring digit outputTd=NK before appending, tracks Zq+=NK and U+=1 with B1=1, then restores oldTd cap. compile_digQLoop uses a two-register family digitQueueResult j (Zq=j*NK,U=j). compile_digQC includes actual clearZq,clearU,repCK. compile_decomposeC includes real subtractY Qx Ia before digit generation. Output length bounds, readiness and widening lemmas are provided.
- compile_decRowBodyC covers real decRowLoadC (two copies/moves and exact CK=Qk copy), decomposeC, appDqZq. Uses exact digit queue length R*NK before append, restores scratch to caller caps and gives outputDq+=R*NK. Caller conditions explicitly include Z<=Qx/Ia,NK<=Td/Y,Qk<=R,Qk<=CK,R<=U,R*NK<=Zq,B1=1 and output room. OldCK need not<=R: actual copy establishes small counter. compile_decRowsC includes actual clearDq and outerrepQc, linear output Q*R*NK. Generic all-rows certificate plus compile_decRowsC_concrete atM2^120,N2^24,K/R2^16,Q2^22 gives time<=2^386 and outputcap2^78. Single decomposeTime<=2^360. This is actual decRowsC under explicit caller caps, not yet full keyDigitsC.
- For digQC composition, simplify only digitQueueResult/zero_mul at the loop certificate before connecting the clear instructions; do not broadly simpa over the composed compiled code. Explicit time inequality avoids unresolved time metavariables.
- Aggregate passed9850 jobs (/tmp/explut-key-time-decompose-build.log). /tmp/key-time-decompose-audit.lean checked digitbody,digQC,decompose,rowbody,allrows,concrete: onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms; git diff --check passed. Build/audit terminal, uncommitted/unpushed.
- Next keyDigitsC prefix: publicRowsC and targetC, thencpQb15,natQcW,natQkK establish countercaps for now-proven decRowsC. Need preserve/widen its scratchcaps before the loop. publicRowC uses positiveCoeffC/negativeReadyC, positive/negativeGatherC, rowCountsC,signedDotC; inspect KeyCoefficients/KeyGadget/KeyPublicMachine/KeyTarget. Reuse KeyTimeGather/QueueArithmetic and current affine-loop patterns. CorrectionC alreadyproven<=2^484, so after keyDigitsC remains copy17Dq,correction,assembly/acceptance and fullKeyGenfront/clock. Dec primitive,reductions,Submission/global comparison remain open. Goal active.

### Actual target-vector generation runtime (2026-11-25)

- Added KeyTimeTarget and aggregate import. targetHeadResult tracks copy0from14, nat2mpkDOffset and fetched3=NK. compile_targetHeadC includes actual drop0by2 and streammove3from0, with arbitrary old scratch underRingInputs. compile_targetC composes head,copyQa3,nat2((W-1)*NK),appendQa2. targetResult gives exact outputcapQa=NK+tail=WNK; only0,2,3,Qa caps change. targetResult_inputs/other support downstream composition.
- compile_targetC_Dc time<=2^251, using mpkDOffset<=codecSizeMPK<=2^120 fromkeyCodec_bounds_Dc and W2^22,N2^24,K2^16. Generic targetTime_bound uses only offset/tail<=M2^120. targetTailLength is noncomputable because setting is. For concrete W, prove (settingDc).E.W=2^22 via change2^Dc.b=2^22 andnorm_num[Dc,Params.bc]; unfolding setting directly leaves canonSetting projections.
- Aggregate passed9852 jobs (/tmp/explut-key-time-target-build.log). /tmp/key-time-target-audit.lean checkedhead,target,length,readiness,frame,concrete: standardaxioms only. No sorry/native_decide/customaxioms; git diff --check passed. Build/auditterminal; changesuncommitted/unpushed.
- Next can close keyDigitsC tail afterpublicRowsC: targetC;cpQb15;natQcW;natQkK;decRowsC. Widen decomposition scratchQx,Ia,Td,Y,CK,U,Zq toM safely while preserving B1,Z,saved15 and targetQa. Existing decRows certificate requires Z<=Qx/Ia,NK<=Td/Y,Qk<=K,Qk<=CK,K<=U,K*NK<=Zq,Qc<=W; actualnat writes supply Qc/W and Qk/K. Compose to getDq<=2^78,time roughly2^388. Need publicRowsC runtime first for whole keyDigitsC (coefficient/gather/signedDot routines), then cp17Dq and correctionC<=2^484; assembly/acceptance/front/clock and Dec/reductions/Submission/global comparison stillopen. Goalactive.

### Complete keyDigits tail runtime and public-row bridge (2026-11-25)

- Added KeyTimeDigitsTail and aggregate import. digitsTailC is definitionally the existing keyDigitsC tail: targetC;cpQb15;natQcW;natQkK;decRowsC. decompositionBase safely widens Qx,Ia,Td,Y,CK,U,Zq toM, preserving all other caps. compile_digitsTailC composes actual target, copy, both counter writes and full decomposition, deriving the former counter/scratch premises from these actual writes and safe widening. compile_digitsTailC_Dc<=2^388 from arbitrary RingInputsM2^120,B1=1,Z<=NK. No old-counter or old-destination blankness premise.
- digitsTailResult_inputs preserves physical readiness; digitsTailResult_fields gives Dq=W*K*NK (2^78 atDc), B1/Z unchanged, Qx=M,Qyunchanged,candidate9/trapdoor16 unchanged. compile_keyDigitsC_of_publicRows connects a future publicRowsC certificate to this verified tail and the actual keyDigitsC syntax; it is conditional on that missing publicRowsC certificate and does not close fullkeyDigits runtime yet.
- Dependency pitfall: rewrite W first, thenN,K, otherwise rewritingN/K changes hidden ring instances in(settingDc).E.W and fails motive typechecking. Numeric digitsTailTime_Dc originally caused kernel deeprecursion when doing gcongr directly atDc; generic digitsTailTime_bound with opaque phase-bound hypotheses solved it. Concrete theorem now instantiates that scalar bound. No limits enlarged.
- Aggregate passed9854 jobs (/tmp/explut-key-time-digits-tail-build.log). /tmp/key-time-digits-tail-audit.lean checked generic/concrete tail,time,readiness,fields,conditionalkeyDigitsbridge: onlystandardpropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms; git diff --check passed. Build/audit terminal; uncommitted/unpushed.
- Next missing publicRowsC: positiveCoeffC gathers publicB/H prefix and applies row automorphism, appends evaluatorAF only atrow0; negativeReadyC generates repeated gadget powers/zeros; positiveGatherC/negativeGatherC use known indices; rowCountsC and signedDotC alreadyhave generic kernels. Need exact coefficientqueue lengths, then publicRowsAppendC linear accumulation15. After publicRows closes, tail ready; connect cp17Dq and correctionC<=2^484, then assembly/acceptance/fullKeyGenfront/clock. Dec primitive,reductions,Submission/global comparison remainopen. Goalactive.

### Actual negative coefficient generation runtime (2026-11-25)

- Added KeyTimePowers and aggregate import. compile_repAppC is a reusable actual repetition certificate for c!=d,s!=d, outputd=old_d+R*sourcecap; includes iterationzero, arbitrary prior output, and affine length growth. compile_powersBody/powersC certify actual append4from7 then ring-add doubling7, requiring7cap=NK; completepowersC clears4 and repeatscounter2, outputs4=R*NK.
- compile_negativeCoeffC composes actual nat2K,powersC,nat6KNK,append4from6,copy7from4,clear4,nat2H,repAppC2/4/7. negativeCoeffResult records2=H,6=KNK,7=2KNK,4=H*2KNK. Preserves all other caps, with readiness lemma. compile_negativeCoeffC_concrete<=2^364 forH<=2^6, RingInputsM2^120,B1=1,7=NK. This covers actual44helpers once initializerisconnected. The earlier draftnumericH2^66 was tightened to64 so its queue bound fitsM; no vacuous actualH2^66 specialization retained.
- Aggregate passed9856 jobs (/tmp/explut-key-time-powers-build.log). /tmp/key-time-powers-audit.lean checkedrepeatedappend,powers,negativecoeffgeneric/concrete,readiness/frame: standardaxioms only (framepropext only). No sorry/native_decide/customaxioms; git diff --check passed. Allsessions terminal; uncommitted/unpushed.
- Next ringOneC initializer: clr5;bitsC6/7/5;nat7B1(NK-1);app6from7;cp7from6. Need derive6=1,7=1 frombits then7=NK-1,6=NK,7=NK; preserveB1. Existing compile_bitsC yields low-level bitsResult, can lift tolayout similarly KeyTimeInit/KeyTimeCandidate. Connect negativeReadyC=ringOneC;negativeCoeffC. Actualhelpercount isD.b*2=44 (KeyPublicSize.public_source_lengths tuplelast), <=64. Then positiveCoeffC/gathers,rowCounts,signedDot,publicRows,fullkeyDigits. Proposalcorrection/tail alreadycertified; assembly/acceptance/front/clock and Dec/reductions/Submission/globalcomparison remainopen. Goalactive.

### Complete negativeReady initializer and generator (2026-11-25)

- Added KeyTimeNegativeReady and aggregate import. layout_bitsC lifts the actual bits initializer to VMregister layouts using layout_update; only t/f caps change to1. compile_ringOneC covers clr5,bits6/7/5,nat7(NK-1),app6from7,cp7from6. ringOneResult5=0,6=NK,7=NK with allotherspreserved, requiresNK>0,B1=1,RingInputs; no assumedblankoldregisters or old7=NK. ringOneTime<=2^246 atconcreteparameters.
- compile_negativeReadyC composes ringOne with negativeCoeffC; compile_negativeReadyC_concrete<=2^365 forH<=64 fromRingInputs/B1 alone. compile_negativeReadyC_Dc uses actualJh enumeration count: public_input_lengths Dc tuple.2.2.2.2 givesDc.b*2=44<=64. negativeReadyResult tracks exactoutput4=H*2KNK,7=2KNK,6=KNK,5=0,2=H; readiness and frameoutside2/4/5/6/7 supplied. This closes actualnegativeReadyC including initialization, stillnotpublicRowC asawhole.
- Aggregate passed9858 jobs (/tmp/explut-key-time-negative-ready-build.log). /tmp/key-time-negative-ready-audit.lean checkedringOne,negativeReadygeneric/Dc,readiness/frame: onlystandardaxioms (framepropextonly). No sorry/native_decide/customaxioms; git diff --check passed. Allsessionsterminal; uncommitted/unpushed.
- Next positiveCoeffC: inspectKeyCoefficients andKeyBHCodec. Need actualpublicB/Hprefix reader, indexgather, autGatheredC (natQcBHrowcount,natQkrowExponent,copyQa4,autQC,copy4Qa), appendAFC (row0prefixAF orzeroNKtail), preservingnegative/savedqueues. Then actualpublicRowC combines positiveCoeffsaveQa,negativeReadysave10,positiveGatherQb,negativeGather11,rowCounts,signedDot. Existingtimekernels nowcovernegativegenerator,allgathers,autQC,signedDot. FullpublicRows traversal and remainingproposal/acceptance/front plusDec/reductions/Submission/globalcomparison stillopen. Goalactive.

### Actual prefix extraction and evaluator coefficient suffix (2026-11-25)

- Added KeyTimePrefix and aggregate import. compile_prefixC certifies actual nat2n,takeC3/0/2,cp0from3. IMPORTANT takeC=cp3counter2;mv3/0/2 (counted move), notmvR. Result0/2/3=n, othercapsunchanged. prefixResult_inputs and prefixTime_concrete<=2^249 whenn<=M2^120.
- compile_appendAFC certifies both actual Bool branches: row0 prefix lengthL=2K*NK thenappend4from0; otherrows nat6L thenappend4from6. appendAFResult branches retainexactsourcecaps and commonoutput4=b4+L, readiness and frameoutside0/2/3/4/6. compile_appendAFC_concrete<=2^246 under outputroom,B1=1,RingInputs. These are parts ofpositiveCoeffC, not yet a fullpositive/publicrow certificate.
- Explicit simpa lists need MVM.compile and appendAFTime to equate compiledsequence syntax andtime; otherwise identical-looking types fail. All proofs check withoutlargerlimits.
- Aggregate passed9860 jobs (/tmp/explut-key-time-prefix-build.log). /tmp/key-time-prefix-audit.lean checkedprefix,appendAFgeneric/concrete,readiness/frame: standardaxiomsonly. No sorry/native_decide/customaxioms; git diff --check passed. Allsessions terminal; uncommitted/unpushed.
- NextautGatheredC n k=cpQa4;natQc n;natQk k;autQC;cp4Qa. Existingcompile_autQC outputQa conservativelyoldQa+nNK, so ifgather4exactnNK, result4cap2nNK (validconservative) unless tighterqueue-shrinkproofadded. Could use this doubledcap forpublicpositivequeue; outputcount remainsn actual, signedDot can consume fromlargercap. Need checktotalcapsfitM usingBHRow count. gatherBHC/mpkBHC andpositiveCoeffC connect prefixB/H,gather,autGathered,cp0from8,appendAF. ExistingKeyPublicSize PublicSizeInputs/public_input_lengths providecounts/indices/prefix bounds. ThenpublicRow/publicRows,fullkeyDigits; proposalassembly/acceptance/front andDec/reductions/Submission/globalcomparisonremainopen. Goalactive.

### Actual gather-plus-automorphism runtime (2026-11-25)

- Added KeyTimeGatherAut and aggregateimport. compile_autGatheredC covers cpQa4,natQc n,natQk k,autQC,cp4Qa; autGatheredResult gives Qa/4=b4+nNK,Qc=n,Qk=k. Counter/exponent premises derivedfromactualnatwrites. compile_gatherAutC composes actualgatherC andautGatheredC; output4cap=2*len(js)*NK (conservative length bound, notsemanticdoubling). Readiness and frameoutside1/2/3/4/Qa/Qc/Qk supplied.
- compile_gatherAutC_concrete gives time<=2^414 for indices/listlength<=2^66,exponent<=2^25,M2^120,N2^24,K2^16 and B1/Z/Qx/Qy callerconditions. Outputcap<=2^107 fitsM. autGathered alone bound<=2^412; gathered time<=2^316. Exact semantic correctness alreadyexists separately; these are realcompiledcode length/time certificates.
- Aggregate passed9862 jobs (/tmp/explut-key-time-gather-aut-build.log). /tmp/key-time-gather-aut-audit.lean checkedautGathered,gatherAutgeneric/concrete,length,readiness,frame: standardaxiomsonly (length/framepropextonly). No sorry/native_decide/customaxioms; git diff --check passed. Allsessions terminal; uncommitted/unpushed.
- Next specializegatherBHC D i=gatherAutC D.N D.K (rowExponent D i)(Enum.list.map(Enum.index∘bhSelection D)). PublicSizeInputs fields/source,row and publicSizeInputs_Dc give<=2^66; rowExponent_lt yields<=2^25. Compose mpkBHC=prefixC(bhPrefixLengthD);gatherBHC. Needprefix bound bhPrefixLength=BHSourcecount*NK (seeKeyBHCodec), so<=2^106. ThenpositiveCoeffC=mpkBHC;cp0from8;appendAFC (firstrow). Conservativegather output2*BHRowcount*NK +2K*NK fitsM. ActualBHEnum indices require index_classical normalization when matching code. NextpublicRow/publicRows; assembly/acceptance/front plusDec/reductions/Submission/globalcomparison remainopen. Goalactive.

### Complete positive coefficient generation (2026-11-25)

- Added KeyTimeBH and aggregate import. bhIndices uses the actual ClassicalEnum index composition withbhSelection, length/bound lemmas dischargeactualgatherindices viaPublicSizeInputs. compile_mpkBHC composes actualprefixC(bhPrefixLength) andgatherBHC; bhResult/time/readiness/frame. bh_bounds_Dc derivesprefix<=M2^120,rowcount<=2^66,rowExponent<=2^25,queuecap<=M; compile_mpkBHC_Dc<=2^415.
- compile_positiveCoeffC_Dc covers actualmpkBHC,cp0fromsavedAF8,appendAFC branch. Time<=2^416. positiveResult output4cap=2*BHRowCount*NK+2K*NK (conservative doubledBHcap fromautQC certificate), bothrow0/zero-tailbranches. positiveResult_inputs and frameoutside0/1/2/3/4/6/Qa/Qc/Qk supply latercomposition. RequiresRingInputsM2^120,B1=1,Z<=NK,Z<=Qx,NK<=Qy; savedinputs onlyneedtheirglobalcaps. NoteQx/Qy unchangedasbounds bypositiveResult despiteactualarithmetic, sincekernelswidenback. All semanticcorrectnesstheorems remainseparate/existing.
- Aggregate passed9864 jobs (/tmp/explut-key-time-bh-build.log); oneunusedsimp warning remains. /tmp/key-time-bh-audit.lean checkedactualMPKprefix,fullpositivecoeff,length,readiness,frame: standardaxiomsonly. No sorry/native_decide/customaxioms; git diff --check passed. Allsessions terminal; uncommitted/unpushed.
- NextpublicRowC composition: cp0from14;savepositiveCoeff Qa;save negativeReady10;cp0from9;savepositiveGatherQb;save negativeGather11;rowCountsC;signedDotC. Bothcoefficientgenerators nowhaveactualcertificates; allgatherscanusecompile_gatherC withPIdxindices<=2^66; publicSizeInputs_Dc. Need preservepositiveQa while negativeReadywrites2/4/5/6/7, saveexactqueuecaps for10/Qb/11, realrowCounts setsQc/12, and broaden arithmetic scratchIa/13 asneeded. signedDotC finaloutputIa=NK thenpublicRowsAppendC output15linearbyW. This closesmissingpublicRows toexistingkeyDigitsTail<=2^388. Proposalcopy17/correction,assembly/acceptance/front andDec/reductions/Submission/globalcomparison remainopen. Goalactive.

### Complete public rows, digits and correction proposal runtime (2026-11-25)

- Added KeyTimePublicKernels and KeyTimeProposal, with aggregate imports. PublicCaps keeps only publicScratch at M=2^120; saved 8/9/14/15/16/17 and B1/Z retain their caller bounds. Positive/negative generators and gathers recover this common envelope using actual output bounds and frame lemmas. compile_publicRowC covers all actual saves, rowCounts and signedDot, with exact final Ia=NK and time<=2^472.
- publicBase widens scratch only. compile_publicRowsAppendC tracks output15 linearly, compile_publicClear includes its actual clear; compile_publicRowsC_Dc covers all 2^22 rows with time<=2^496. publicRowsResult_inputs proves readiness for the tail. compile_keyDigitsC_Dc connects the existing actual digitsTail and has time<=2^497. keyDigitsResult_inputs/fields retain B1/Z, candidate9/trapdoor16, Qx/Qy=M and exact Dq=W*K*NK.
- KeyTimeProposal defines proposalReady (actual cp17Dq result) and proposalResult (actual correction result). compile_proposalC_Dc composes real keyDigitsC, cp17Dq and full correctionC, time<=2^498, under only RingInputsM120, B1=1 and Z<=NK. This is not yet proposalKeyC: assembly and acceptance remain open.
- Aggregate passed 9868 jobs: /tmp/explut-key-time-public-build.log. PublicKernels built4.2s, Proposal3.1s, aggregate3.0s. /tmp/key-time-public-audit.lean and .log audit publicRow/publicRows/keyDigits/readiness/fields/proposal; only propext, Classical.choice, Quot.sound. No sorry/native_decide/customaxioms in new modules; git diff --check passed. All tool sessions terminal. Uncommitted/unpushed.
- Proof-performance pitfall: simp [publicRowsResult, publicBase, publicScratch] in concrete caller premises/fields caused multi-minute elaboration. Replaced these by `change` for B1/Z and direct `exact digitsTailResult_fields ...`; same obligations then compile in seconds. Interrupted the slow build and temporary /tmp/public-debug.lean run intentionally before fixing, no duplicate live jobs.
- Next: proposalResult readiness/fields (correctionBase preserves17 and B1/Z), then actual assembleC=cp0from18;app0from17;gatherC of assemblySelection;cp19from4. Need source total cap <=M, indices bounded via assembly source Enum, destination key length. Existing KeyProposal/KeyProposalSize and KeyGatherSize supply dimensions/counts. Compose proposalKeyC, then acceptInitC/tryKeyC and complete machine front/framing/clock. Earlier candidate output coarse envelope still needs actual B1/Z caps recovered for whole machine composition. Dec, reductions, Submission/globalcomparison and finalaudit remain pending. Goal active.

### Assembled key-proposal runtime (2026-11-25)

- Extended KeyTimeProposal with proposalResult_inputs, proposalResult_fields (17=W*K*NK,18=PIdxCount*NK,B1/Z preserved), and proposalResult_source_bound proving18+17<=M120. Generic correctionSaved_fields avoids expensive definitional normalization of concrete PIdx enumeration when proving saved-register fields.
- Added KeyTimeAssembly and aggregate import. compile_assembleWords covers actual cp0from18, app0from17, gatherC and cp19from4 with arbitrary indices; compile_assembleC_Dc specializes to actual assemblySelection, using assembly_lengths_Dc bounds. Time<=2^318. assemblyResult gives exact4/19=len(indices)*NK, preserves18/B1/Z. compile_proposalKeyC_Dc composes actual proposalC and assembleC, time<=2^499. proposalKeyResult_inputs/fields provide acceptance-ready length conditions, including exact corrected queue18 and assembled queue19, B1/Z preservation. Premises remain RingInputsM120,B1=1,Z<=NK (full-machine initializer connection still pending).
- assemblyIndices is generic in D. assemblyIndices_length needs two simplification passes: first expand structural KCol/Enum lengths, then setting_tau/W. Simplifying setting fields first changes types but leaves original Enum instance arguments and makes apparently identical lengths fail. assembleC_eq uses simp only [assembleC,assemblyIndices,Function.comp_def,index_classical] to reconcile Classical decEq with structural instances. No maxRecDepth increase.
- Initial slow checks narrowed the issue to proposalResult_fields: direct `change keyDigitsResult ...` caused concrete enumeration reduction. Replaced with generic correctionSaved_fields and transitivity; compilation returns to seconds. Avoid rewriting full concrete result expressions: use congrArg2 for sums and equality.le.trans for bound propagation. All deliberately interrupted diagnostic/build sessions are terminal; no live checks.
- Aggregate passed9870 jobs (/tmp/explut-key-time-assembly-build.log); assembly targeted build9698 jobs (/tmp/explut-assembly-build.log). /tmp/key-time-assembly-audit.lean and .log checked source bound, actual assemble/proposalKey, readiness/fields: only propext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms, git diff --check clean. Changes uncommitted/unpushed.
- Next actual acceptance: KeyAccept.radiusC clears7,bits5/6/7,clearsRR,emitBitsRR(encM K r),cp7RR,clearRR,nat2N,repApp2/RR/7. compile_emitBitsC already exists (KeyTimeTemplates) on physical bounds; add layout wrapper using natResult_low/register and le_layout, then compose radius initializer and acceptInitC. KeyBoxLoop.boxBodyC=boxLoadC;ballTestC;ifbTx nop(cpDqB1), boxQueueC=clearDq;repQc body, boxFamilyC=boxQueue;clearQb;eqbTx Dq Qb. KeyTryVM contains ballTestC and per-digit subprograms; no KeyTimeBox certificate exists yet. Need acceptance/tryKey/fullmachine front+framing+clock, then Dec/reductions/Submission/global comparison. Goal active.

### Radius and complete acceptance initialization runtime (2026-11-25)

- Added KeyTimeRadius and KeyTimeAcceptInit, both aggregate-imported. layout_emitBitsC lifts existing physical compile_emitBitsC to layout bounds via natResult_low/register, with exact destination b[r]+literal.length and other registers preserved. compile_radiusC certifies actual clear7,bits5/6/7,clearRR,emitBitsRR(encM K r),cp7RR,clearRR,nat2N,repApp2/RR/7. radiusResult has5=6=1,7=K,2=N,RR=NK; fields/readiness preserveB1,Z,18,19. compile_radiusC_Dc<=2^270, anyr, requiresRingInputsM120,B1=1.
- compile_acceptInitC connects actualradius, natTBk B,natTKB(K-B),cpQa18,natQcPIdxcount. acceptInitResult givesRR=NK,TBk=B,TKB=K-B,Qa=b18,Qc=PIdxcount and preservesB1/Z/key19. compile_acceptInitC_Dc<=2^272 forB<=Dc.K,RingInputsM120,B1=1; generic result_inputs and fields supplied. All first-pass proofs compiled without extra recursion/heartbeat settings.
- Aggregate passed9874 jobs (/tmp/explut-key-time-accept-init-build.log), targetedradius9700 jobs andacceptinit9702 jobs. /tmp/key-time-accept-init-audit.lean/.log checked layoutemit,radius,acceptinit/readiness/fields: standardaxioms only. No sorry/native_decide/customaxioms; git diff --check clean. All sessions terminal. Changes uncommitted/unpushed.
- Next acceptance body: KeyTryVM tstBody=digTd Ta Di;addFa Fa Td;digTd Tnb Di;addFa Fa Td;appDi B1. tstC=addTa Tx RR;subTnb RR Tx;cpDi TBk;cpDc TKB;repDc tstBody. Need affine Di counter (initialB+j) rather than fixedM envelope because appDiB1 grows; use rep_family like KeyTimeDecompose/BitLoop, arithmetic capFa/Td>=NK. KeyBoxTest.ballTestC=tstC;eqbTx Fa Z (eqb layout wrapper using compile_eqb_cert likely needed). KeyBoxLoop.boxBody=boxLoad(Tx<-Z,mvRTxQa,Fa<-Z);ballTest;ifbTx nop(cpDqB1), boxQueue=clearDq;repQc body; boxFamily=boxQueue;clearQb;eqbTx Dq Qb. Initial PIdxcount<=2^66, B and K-B<=2^16. Keep outputkey19 andB1/Z preserved. Then acceptC actualreject branch nat19(keycodecsize);tryKeyC; recovercandidateB1/Z for completeKeyGen, machinefront/framing/clock. Dec/reductions/Submission/globalcomparison stillpending. Goalactive.

### Complete range test, acceptance and deterministic try runtime (2026-11-25)

- Added KeyTimeBoxDigits, KeyTimeBoxFamily, KeyTimeAccept and aggregate imports. compile_tstBody certifies four ring operations plus actual appDiB1; compile_tstLoop tracks Di=bDi+j with rep_family. compile_tstC includes add/sub and actual counter copies; returns original caps under sumTBk+TKB<=Di,TKB<=Dc and ring scratch caps. layout_eqb_update yields exact flag cap1. compile_ballTestC_Dc<=2^360 forTKB<=2^16.
- BoxCaps collects explicit caller caps. compile_boxBodyC_Dc includes boxLoadC,ballTestC and actual persistent rejection latch branch,<=2^362. compile_boxQueueC_Dc includes clearDq and entire repQc forQc<=2^66,<=2^430. compile_boxFamilyC_Dc includes finalclearQb/eqbTxDqQb,exactTxcap1,<=2^432.
- boxBase widens only Tx/Fa/Di/Dc/Ta/Tnb/Td/Dq/Qb/19. acceptResult=boxBase(acceptInitResult), readiness and B1/Z/Qc/19 fields supplied. compile_acceptC_Dc covers actualacceptInit,completeboxFamily,and bothaccept/reject branches,including nat19(keycodecsize) onrejection;time<=2^434 forRingInputsM120,B1=1,B<=K. Key19 cap is deliberatelyconservativeM120; semantics remain existingexec_acceptC. compile_tryKeyC_Dc composes actualproposalKey andaccept,<=2^500,requiresRingInputsM120,B1=1,Z<=NK,B<=K.
- Proofperformance: concrete finalaccept composition stalled while unfolding huge natC keycodec; generic compile_acceptC_of_parts establishes code composition with abstractD first. compile_rejectWord abstracts literal length fornumericbound<=2^250. Aftergenericcomposition aggregate rebuiltKeyTimeAccept1.9s. Several intentionalinterrupteddiagnostics areterminal; no livejobs. Directprefix diagnostic provedbase/readiness/fields quickly; fail-marker temporaryfile provedprefixbefore reject quickly. No diagnosticcode enteredrepository.
- Aggregate passed9880 jobs (/tmp/explut-key-time-accept-build.log). /tmp/key-time-accept-audit.lean/.log auditedloop,ballTest,boxFamily,accept,tryKey: onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms innewfiles;git diff --check clean. Allsessions terminal; changesuncommitted/unpushed.
- Next fullKeyGen: current compile_candidateC_Dc returnscoarse preparedBounds and loses B1/Z. Refine via new outputcertificate retaining actualcandidateInitResult B1/Z and decodeQueueBase protectedregisters; existing compile_candidateC_Dc proof shows exactintermediate decoder output then unnecessarilywidensbefore cp9Dq. Add precise candidateoutput and postinit B1/Z lengths; sampleP/preparationmay remaincoarse because candidateInit reinstallsB1/Z (check actualcandidateInitOps). Then compose prepare/sample/candidate/tryKey, with Params.Bk<=Dc.K, actual keyCore syntax. Add tryKeyResult readiness/fields ifneeded forpackKeyC/frame. Remainingenter/parse/check/invalid/pack/frame/clock and fullkeytime/Cost; thenDec/reductions/Submission/globalcomparison/finalaudit. Goalactive.

### Complete probabilistic KeyGen core runtime (2026-11-25)

- Added KeyTimeCore and aggregate import. candidateInitResult_constants proves actual initializer installs B1cap1 and ZcapNK. candidateDecoded retains decoder output caps; candidateResult copies exact decoder length into9 without widening allregisters. compile_candidateC_precise<=2^414 retains theseconstants; candidateResult_inputs/constants are unconditional givenRingInputs atinput (no externallyassumedB1/Z). Old compile_candidateC_Dc API unchanged.
- compile_candidateTryC_Dc composes actualcandidateC andtryKeyC,<=2^501. cert_keyCore_program_Dc covers actualKeyCore.program Dc Params.Bk r = compilekeyPrepare;sampleP(nPI*N*Bk);compilecandidateTry,<=2^502 foranyradiusr andRingInputsM120,N2^24,K2^16 oninput. Theactual configuredrSmall is included. candidateTryResult_inputs suppliesRingInputs atoutput forpackKey.
- Avoidedkerneldeeprecursion in candidateResult_inputs by defining candidateResult9 with known literalcap2^66*(2^24*2^16), ratherthan candidateDecoded a rDq. Theyareequal, but projecting through concreteinitializer duringdefeq causeda70s kernelrecursionfailure. Explicitcap gives2s aggregatebuild. Sameprinciple used in candidateDelivery_constants generichelper. No increasedrecursion/heartbeat limits.
- Aggregate passed9882 jobs (/tmp/explut-key-time-core-build.log). /tmp/key-time-core-audit.lean/.log checkedprecisecandidate,constants,candidateTry,fullprobabilisticcore,outputreadiness: onlypropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms; git diff --check clean. Allsessions terminal; uncommitted/unpushed.
- Nextmachineenvelope: KeyOutput.packKeyC=cp0from14;app0from19. Currentcorecaps14<=M120 and19=M120,so packingneedsM121 or tighterkey19cap. Prefer liftlayoutM120toM121 retainingphysicalringtemplates andregistercaps; packoutput0<=2^121. ThenKeyCore.outputProgram=program;compilepackKeyC;progMVM.IO.post, wherepost=cpphysical0from41;setList(empty)postTapes. VMIO.setList genericlistbounds canboundcleanups; KeyBranch.enterP=progIO.pre(N,K,zeroTemplates);compilecpCs1. Needcert forpre restoringRingInputs fromarbitraryparserworkspace. KeyFront.parse/check/chooseP, invalidP(keyInput;cp14from17;nat19codec;pack;post), KeyMachine.frameKeyP and fullkeyProgram/totalTimeT clock remain. ThenfullkeyCost<2^818,Dec/reductions/Submission/globalcomparison/finalaudit. Goalactive.

### Complete core output, packing and workspace cleanup runtime (2026-11-25)

- Added KeyTimeOutput and aggregate import. Cert.progSeq composes physical Prog certificates; cert_clearList certifies actual IO.setList(empty) on an arbitrary tape list with output clearedBounds and time(len+1)*(2M+5). cert_vmPost certifies actual physicalcp0from41 and completepostTapes cleanup; outputBounds(a41) keeps onlyphysical0, allothercaps0; time<=107*(2M+5).
- layout_lift and layout_lift_inputs safely enlarge globalscratch budget without losingringtemplates/registercaps. compile_packKeyC certifies actualcp0from14;app0from19 with exact0=b14+b19. cert_packPost_Dc liftsM120toM121 becausecore19cap=M120 and14<=M120, thenpacksandcleans; <=2^250,outputonlytape0. cert_outputProgram_Dc connects actualKeyCore.program throughpack/post; <=2^503 forRingInputsM120,N2^24,K2^16 input andanyradiusr. This still excludes enter/parse/check/invalid/frame/totalclock.
- Aggregatepassed9884jobs (/tmp/explut-key-time-output-build.log). /tmp/key-time-output-audit.lean/.log checkedclearing,post,pack,packPost,outputProgram: onlystandardpropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms;git diff --check clean. Oneharmless unusedFunction.update_apply simpwarning inclearListnil remains. Allsessions terminal;uncommitted/unpushed.
- NextenterP: IO.pre=physicalcp41from0;cp42from1;setList(enc N K (allVMregistersempty)) preTapes, preTapes excludes41/42. Need general literal putW/setList certificate (Lookup.lenBoundT_putW alreadyexists; putW nil=clear,cons=recursiveputW;consbit). Literals at35/36/37/38 mustestablishK/N/NK/NK; allotherclearedexceptinputs41/42. ComposecpCs1 topositionpredicate; getRingInputsM120 fromparserbounds. Existingcert_clearList handlesonlyempty literals; generalputW helpercanalso supportpre. TheninvalidKeyC viaexistingkeyInputC andnat19 pluspackPost; KeyFrontparse/check/chooseP andframeKeyP; wholekeyProgram/totalTimeT keyMPclock, Costcompare. Dec/reductions/Submission/globalcomparison/finalauditremain. Goalactive.

### VM entry and complete valid branch runtime (2026-11-25)

- Added KeyTimeLiteral and KeyTimeEnter with aggregate imports. cert_putW supports anyphysicaltapecount, exactliteraloutput,length-linearbound(len+1)*(2M+5). cert_setList uses literalBounds (selectedtapes overwrittenwithwordlengths) andliteralWeight=sum(length+1)+1, withweight<=len*(M+1)+1.
- blankVM=MVM.enc N K (allVMregistersempty); qualifyMVM.enc toavoidhigher-levelenc collision. preResult preservesinputlengthsa0/a1 onphysical41/42,otherwiseblankVMwordlengths. cert_vmPre coversactualphysicalcopiesandtemplateIO.setList; time<=(105*(M+1)+3)*(2M+5), exactpreResult. preResult_inputs establishesRingInputs fromarbitraryboundedphysicalworkspace (noinitialblanknessassumption).
- cert_enterP_Dc coversactualIO.pre pluscompilecpCs1, returnsverifiedpreparedBounds,<=2^250 foranyphysicalinputa withalltapes<=M120. cert_validP_Dc connectsactualenterP andoutputProgram; <=2^504, outputBounds(core14+core19), allotherphysicaltapeszero. Parser/check/invalidbranch/frame andcompilerclock stilloutsidecertificate.
- Aggregatepassed9888jobs (/tmp/explut-key-time-enter-build.log); /tmp/key-time-enter-audit.lean/.log auditedliteral,setList,pre,enter,valid: onlystandardpropext,Classical.choice,Quot.sound. No sorry/native_decide/customaxioms;gitdiffcheckclean. Allsessions terminal;uncommitted/unpushed.
- Nextinvalidbranch: compile_keyInputC_Dc and keyInputResult_inputs alreadyexist inKeyTimePrepare. Need keyInputResultB1=1 viafieldResult_other twice + initBits_sources. Widentophysicalringlayout withVMcapsallM120exceptrB1=1; preserveB1 fornat19. invalidKeyC=keyInputC;cp14from17;nat19(keycodecsize);packKeyC. cert_packPost_Dc handlesM121packingandpost butcodeassociation mayneedgenericcompositionhelper (orcertifyinvalidKeyC thenpost). invalidP=enterP;compileinvalidKeyC;progpost. Thenparse/check/chooseP inKeyFront,frameKeyP,fullkeyProgram/totalTimeTclock/keyCost;Dec/reductions/Submission/globalcomparison/finalaudit. Goalactive.

### Guarded KeyGen machine, correctness bridge, submission assembly (2026-11-25)

- `Prog/KeyTimeInvalid` (invalid branch certificate, `cert_invalidP_Dc` ≤ 2^254, `cert_validP_uniform` ≤ 2^504) and **`Prog/KeyTimeFront`**: `guardP n` (length guard on 105 tapes), `keyGuardP` (guard; valid input → `keyProgram`, overlong → empty output), `keyMB` via `toMachineB` (bounded loader). **`keyMachine := keyMB Dc Bk rSmall predLen`**: `keySpec_keyMachine : KeySpec Dc kbDc predLen`, **`keyLongSpec_keyMachine`** (the old `keyMP` could not satisfy `KeyLongSpec`), `time_keyMachine ≤ 2^508` (parser, length check via mapped `lenEqP` bounds, both branches, frame), `descLen_keyMachine ≤ 2^620`, `cost_keyMachine_lt < 2^818`. `codecSize_mskEnc_Dc ≤ 2^101`, `keyInputBound_Dc ≤ 2^103`.
- `AH/Correct` (delegate): **`correct_of_specs`**: `Correct (univ w8) params impl` from SetupSpec/EncSpec/KeySpec(kbDc)/DecSpec/eval, success ≥ 1 − 2^-130 (re-derived at Dc: 44 helpers, machine decodeBit).
- **`SubmissionCore`**: registry (`CircularRingLWE.decision`), `prem` (1155 bits at `circParamsD Dc`), `implE decM hdet` (setupMP binSampler, encMachine, keyMachine, decM, evalMachineX), `implSpec_implE`, `correct_implE`, `expressive_implE`, `attributeHiding_implE` (via `attributeHiding_Dc'` + `redMachine_of_comps`), `cost_implE_le` (≤ 2^242+2^508+2^817+T+2^249+2^620+2^744+S), **`spec_of_parts`** and `valid_submissionOf`. Remaining inputs: a deterministic Dec machine with `DecSpec Dc predLen` and time/descLen (delegate, files `Prog/DecMachine*`), and `RawComps Dc kbDc predLen (implE …) χfl` with const ≤ 2^893 (delegates: `Prog/RedSetupP*`, `Prog/RedPub*`/`RedChal*`, `Prog/RedKey*` + `RedKeyPLAN.md`; authP = `authWX`).
- Kernel pitfalls: state machine-level facts with `rw [implE_setup]` etc. (generic `cost_le_parts`) — unfolding `Machine.time` of concrete machines in the kernel recursed deeply; for Spec use generic `spec_of` + `submissionOf_impl` rewrites; abstract the input bound `n` before arithmetic on `keyInputBound Dc predLen`.
- Aggregate passed 9902 jobs. Axioms of KeyGen machine theorems: standard three.
- **`AH/RedConstDc`**: `compBoundG_le_Dc`, `const_le_of_bounds`, **`const_le_Dc`** (`const ≤ 2^821` for `rc : RawComps Dc kb predLen impl χfl` with `rc.R ≤ 300`, component sizes `2(|setupP|+|pubP|)+|keyP|+|authP|+|chalP| ≤ 2^240`, `compTimeP ≤ 2^500`, `Ssig, Lp, Lk, La, Lc ≤ 2^125`), **`hC_of_bounds`** (→ `64·2^256·const ≤ 2^1155`). Fixed sizes: `rawEnc_size_Dc ≤ 2^110`, `ctEnc_size_Dc ≤ 2^110`, `WR_Dc_le ≤ 2^125`. Final assembly will be `spec_of_parts decM hdet N hD rc (hC_of_bounds rc (const_le_Dc rc …)) (cost_implE_le …)`. Aggregate 9904 jobs.
- setupP (delegate): `Prog/RedSetupPUC`, `RedSetupP`, `RedSetupPDc` (`setupRX D hR e : XProg (R+2)`, R ≥ 38, law/WF/ok (Ok := True), time ≤ 2^205, Ssig = 2^101 at Dc); `Prog/RedSetupPSize`: `size_setupRX_Dc ≤ 2^20`.
- keyP (delegate, partial): `Prog/RedKeyPLAN.md` + `RedKeyMath`, `RedKeyMatVec`, `RedKeyURow`, `RedKeyU`, `RedKeyTry` (single simulated-trapdoor try, `map_coins_exec_simTryKeyC_uC_Dc`, needs register 16 = rows of simX). Aggregated (9922 jobs). Continuation delegate on modules 5 (simX) and 6 (simKey); modules 7–9 (view2 regs, front end/machine, time) remain.
- pub/chal (delegate, partial): `Prog/RedPubFront` (`ringIO`/`ringIO1` RingVM handler, R = 245, law/wf/bounds), `RedChalVM` (hash kernels), `RedChalMath`, `RedChalPhases` (c0/cin/caut words). Continuations: chalP, pubP.
- Dec (delegate): `Prog/DecMachineCode` (`decCode`, `exec_decCode`; renamed its `len_col` → `dmlen_col` to avoid clash with SetupConf), `DecMachineProg` (`DecM.decMP`, `decSpec_decMP`), `DecMachineConf` (**`decSpec_decMachine : DecSpec Dc predLen decMachine`**), `DecDescConf` (`descLen_decMachine ≤ 2^465`), `DecTimeVM` (`absRun` abstract clock, `absRun_sound`). Clock `time_decMachine` pending (continuation delegate, files `Prog/DecTime*`).
- **`SubmissionDec`**: `implX`, `Ncost = 2^818`, `cost_implX_le` (from Dec time ≤ 2^816), **`spec_of_comps`**: final `Spec` from Dec time bound + `RawComps` with coarse bounds. Remaining: `time_decMachine`, pubP, chalP, keyP (+ authWX lift into common R = 245, setupRX R ≥ 38).
- Dec clock (delegate): `Prog/DecTimeUni`, `Prog/DecTimeConf` — **`time_decMachine ≤ 2^727`**. `SubmissionDec.spec_of_rawComps`: final Spec from `RawComps` with coarse bounds only. Remaining: pubP, chalP, keyP.
- chalP (delegate): `Prog/RedChal{Code,Parse,B,H,Aut,Cb,Rows,Blocks,HWords,Tail,Law,Time,Bound,Dc}` — **complete**: `law_chal_spS`, `wf_chalP`, `bounds_chalP_Dc` (Lc ≤ 2^110, time ≤ 2^450), `size_chalP_Dc ≤ 2^200`, `chalP_Dc_spec`. 247 tapes (R = 245).
- pubP (delegate): `Prog/RedPubP*` (20 modules) — **complete**: `law_pub_spS`, `wf_pubP_Dc`, `len_pubP_Dc` (Lp ≤ 2^102), `time_pubP_Dc ≤ 2^450`, `size_pubP_Dc ≤ 2^200`, `pubP_Dc_spec`. Remaining: keyP only (then RawComps assembly).
- **`SubmissionAssembly`**: `KeyComp` (keyP on 247 tapes: WF, law_key vs spS, Lk ≤ 2^125, time ≤ 2^450, size ≤ 2^200), `compsOf`/`boundsOf`/`rawCompsOf` (setupRX, pubP, keyP, authWX, chalP, R = 245), **`spec_of_keyComp : KeyComp → Spec … (submissionOf decMachine _ 2^818)`**. The only remaining input is a `KeyComp`.
- **Law side complete**: `RedKeyPkt*` (packet code, `rkMidOk_pkt : RkMidOk (mid (pkOf pkt))`). **`SubmissionKey.spec_of_costs`**: final Spec from `RkMidBound midK a`, `RkTailCert a Lt Tt` (Lt ≤ 2^125, Tt ≤ 2^449), `midK.size ≤ 2^190`, `(rkTailP Dc Bk rSmall).size ≤ 2^195`. Remaining: these cost certificates (delegates: tail `RedKeyT*`, mid `RedKeyC*`).
- Tail certificate (delegate): `RedKeyT{In,Size,K,Acc,Cand,Mv,Pub,Dig,Uc,UD,Num,Tail,Main,SpecG,Spec}` — `rkTailCert_of` (Lt = 2^102+2^120, Tt = 2^436), `size_rkTailP_Dc ≤ 2^195`, **`spec_of_mid`**. Only remaining: mid cost (`∃ a, RkTailIn a ∧ RkMidBound midK a`, `midK.size ≤ 2^190`).

### Submission complete (2026-11-25)

- `RedKeyC3M*` (M3 certificate, `m3_h3`, time ≤ 2^303), `RedKeyCW`/`RedKeyCWPk` (code weights `cw_pkOf`, `cw_m4`), `RedKeyC.c3_spec_closed`.
- **`ExpLUT/Submission.lean`**: `submission := submissionOf decMachine _ (2^818)`; **`spec_submission : Spec (BranchingProgram.primitive w8) registry submission`** (unconditional) and **`valid_submission`** (1155 ≤ H(circParamsD Dc)). `#print axioms`: propext, Classical.choice, Quot.sound only. Aggregate builds (10190 jobs).

### Tight Enc clock (2026-11-25)

- **`EncConf.time_encMachine_tight : encMachine.time ≤ 2^253`** (was `time_encMachine ≤ 2^817`, kept). Files
  `Prog/EncTight{Base,Init,Cert,Core,Prep,Front}`, `Prog/EncTimeTight`:
  * `EncTightBase`: `TB p ρ σ σ' T` (the `Sym.Sound` summary of `AbsBound` evaluated at one value `ρ` of the
    variables: placed by any injective `u`, per-tape bounds, clock `T`), `TB.of_check`, **`checkAt`/`TB.of_checkAt`**
    (abstract run checked *numerically* at `ρ`; claims capped by the top), `TB.seq/mono/putW/clr/cpSelf`, and the
    generic sequencing equations `timeBoundT_seqL/R`, `xtime_seqL`, … (rewrite with these, never `show`/`change` a
    `timeBoundT`/`lenBoundT` of a concrete program: a non-syntactic match unfolds the structural recursion into the
    whole program, 25+ GB).
  * `EncTightCert`: `checkAt` certificates (`decide +kernel`) of the four phases at `ρE = [2^99, 2^24, 2^16, 9, 2^22, 2^42]`
    (`top, N, K, g, W, C`), streams/output/scratch at the top: `mrowP` (b row) ≤ 2^228, `hBlkP` ≤ 2^203,
    `autBlkP` ≤ 2^236, `tailP` ≤ 2^240 (the last two need `maxHeartbeats 0`).
  * `EncTightCore`: rounds (`tb_round`: templates of ≤ W bits, block restores its inputs), `core_tight` (disjoint slots).
  * `EncTightInit`: loader per-tape bounds (`initB_spec`, `mvP` charged its counter via `check_mvP_enc`), `initB_le`.
  * `EncTimeTight`: core box `Bstar`, `opOK_encInit` (82 loader ops; only `decide +kernel` on closed numerals),
    `cleanCore_tight`, **`suffix_tight` ≤ 2^242**.
  * `EncTightPrep`/`EncTightFront`: per-tape parser bounds (`lenBoundT_unfr_le`, `lenBoundT_parse_le`), sampler at
    `T(2^100, 2^102) ≤ 2^252` (was `T(2^104,2^104) ≤ 2^300`), **`total_encProgram_tight`**, `time_encMachine_tight`.
- Cost chain: `Sub.cost_implE_le` uses 2^253 for Enc; `Sub.Ncost = 2^745` (`cost_implX_le` from `time_decMachine ≤ 2^727`);
  total is dominated by the Enc description `2^744`.

### Promotion to SigabaNeoStd (2026-11-25)

Application-independent modules (import closure in Std only) moved to `SigabaNeoStd`, with `SigabaNeo.*` namespaces: `Params/Strength/Generic` → `Lattices/Estimator/CircularMersenne`; `Prog/DecTimeVM` → `Lattices/ProgAlgo/Mersenne/VMFlowClock` (`SigabaNeo.Tape.RingVM.Flow`); `Prog/RedChalVM` → `…/VMHash` (`RingVM.Hash`); `Prog/RedPubPKit` → `…/VMBuf` (`RingVM.Buf`); `Prog/RedPubFront` → `…/VMHandler` and `Prog/RedKeyMidRing` → `…/VMHandlerStash` (`RingVM.Handler`); `RingBTVW/Prog/DecodeWord` → `Lattices/RingLWEWord`; `Prog/RedKeyC1Un` → `Machines/Prog/AvoidTapes` (`SigabaNeo.Tape.XProg.Avoid`). Older notes above refer to the old paths.
