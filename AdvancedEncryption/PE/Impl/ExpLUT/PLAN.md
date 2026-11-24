# PE from lookup tables over exponents (ePrint 2026/2539 §5), for the 128-bit BP universe

Goal: a second `Submission` for `PE.BranchingProgram.primitive` (the same universe as
`PE/Impl/DualUse/Submission.lean`: 16 symbols of 8 bits, 32-bit states, `T = 16`), implementing
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
Classical.choice, Quot.sound]` only. Generic lattice math goes in `SigabaNeo/Lib/Lattices`,
generic machine code in `SigabaNeo/Lib/Machines`, the scheme in `AdvancedEncryption/PE/Impl/ExpLUT`.
Mirror the structure and reuse the infrastructure of `PE/Impl/DualUse` (read its `DESIGN.md`,
`COST_PLAN.md`, `AdvancedEncryption/BP_PLAN.md`) wherever possible.

## Design decisions (deviations from the paper, all as in `DualUse`)

1. **Odd modulus `q = 2^K − 1`.** The sieve divides by `W` (`α_{k,L} = W⁻¹ Σ_j …`), so `q` must be
   odd; the dual-use `q = 2^K` cannot work (the scaled gadget `W^T G` is no trapdoor). With
   `q = 2^K − 1` a residue is a `K`-bit word read modulo `q` (two words for `0`), negation is
   bitwise NOT, addition is addition with end-around carry, multiplication by `2^i` is a rotation and
   `W⁻¹ = 2^{K−40}`. Binary gadget `g = (1, 2, …, 2^{K−1})`, `τ = K`; `G⁻¹` = the bits of any `K`-bit
   representative. `⌊q/2⌉ = 2^{K−1}`. Nothing needs primality: the LHL used is
   `SigabaNeo.Lattices.isTwoUniversal_binaryHash` (any finite commutative ring).
2. **Binary / box laws instead of Gaussians.** Programming matrices `R`, `Z_t` and the TrapGen
   trapdoor `T` are binary (entries `0/1 ∈ R`); errors are the centered-binomial/box laws of
   `DualUse`; noise flooding by boxes (`closeTo_floodLaw_add`); keys by one try of box rejection
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
  must be an explicit machine with a cost bound, as `DualUse/ReductionMachine` + `Prog/KeyCostV`).
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
| B | `Lib/Lattices/CircularRingLWE.lean` (Assumption 1 as a `SigabaNeo.Assumption`, `H := RingLWE.H` of the base parameters) + certified strength at the concrete parameters (as `DualUse/Params/Strength`) | – |
| C | `ExpLUT/Ops`, `ExpLUT/Eval`, `ExpLUT/Scheme`, `ExpLUT/Correctness`: the operations of §4 over an abstract ring with automorphisms, exact identities and noise bounds, Lemma 9, the scheme of §5.1 with the box/binary laws, Theorem 1 | A's interface (abstract) |
| D | `ExpLUT/SimForm`, `ExpLUT/SimTrap`, `ExpLUT/Hybrid*`, `ExpLUT/Security`: Lemma 10, Corollary 1, Lemma 11, the hybrids, the reduction to circular Ring-LWE (math level) | C |
| E | Machine arithmetic modulo `2^K − 1` on ring words (add, neg, sub, mul, rotations, `σ_k`, gadget digits), as `Lib/Lattices/ProgAlgo/RingProgs` | – |
| F | Machines `Setup`, `Enc`, `KeyGen`, `Dec`, `Eval` realizing C's laws exactly; time and descLen bounds | C, E |
| G | Reduction machine of H4 with a cost bound; `HardAt` assembly (`AHConcrete` analogue) | D, F |
| X (optional, low priority) | Exact (`=`) step lemmas for the data-independent parts of the machine library (`Lib/Machines`, `ProgAlgo`), next to the existing `≤` bounds; the costs stay tight upper bounds | – |
| H | `ExpLUT/Submission.lean`: registry (circular Ring-LWE), `spec_submission`, `valid_submission`, cost comparison write-up | all |

## Status

(updated as packages land)

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

* **B done** (`t3/explut-b`): `SigabaNeo/Lib/Lattices/CircularRingLWE.lean` (`CircularRingLWE.decision`,
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
  `[false]` outside (as DualUse).
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
per-tape clocks `timeBoundT` and `descLen` from `XProg.size`, as `DualUse/Prog`. Every ring word a
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
* closed clock of `setupMP` (per-tape, as `DualUse/Prog/TightSetup`: `vb_smp` for `repF`, `VB.natP`,
  `VB.checkMap` with the certificates above, `vb_appendTapeP`/`vb_frameApP`), its `descLen`, numerics;
* concrete `RingSampler`s (binary `χT`: one fair bit then zeros; CBD/box coefficient samplers with
  negatives as one's complement NOT);
* `Enc` (design below), then its clock/descLen.

**Enc plan** (all ring words canonical; `σ_{g^j}` as `j` iterations of `σ_g`, `g = 1 + 2N/W` in
unary — `autMP` with a template of length `g`; `X^{w x_t}` by `rhoJP` with `2N − w x_t`): parse the
input frames (`ufChunk`/`dropChunk` of `DualUse/Prog/EncP`), sample the coins in the order of
`encCoinsLaw` with `RingSampler`s, then one generic block
`encRow(s, A, z, e) = canon(s·A⁽⁰⁾ + A⁽¹⁾ − z·G + e)` (per column `(r, i)`: `z_r 2^i` by `rotBP`
doublings) used for `b` (`z = 0`), `h_k` (`z = (s_k, 1)`), `c^aut_{t,d}`
(`z = digit_d(C_t)·(σ_t s, 1)`), `C^in_t` bottom rows (`A = (−a_t ; 0)`-style, `z = −X^{w x_t}(s,1)`),
`c^in_{t,d}`, `c₀` (`z = (s, 1)`); `c_m = s d₁ + d₂ + e_m + 2^{K−1} μ`.

### Package F4 — the `Dec` machine (branch `t3/explut-f4`, in progress)

**Design.** `Dec` is written as code of a small verified register machine instead of raw tape
programs:
* `SigabaNeo/Lib/Lattices/ProgAlgo/Mersenne/VM.lean`: **`RingVM`** — 200 word registers, the ring
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
  centered binomial `cbdR D η`, `cbdPM η L K` = DualUse's `cbdP` with one's-complement leaves
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
5. parsing (`ufChunk` per field of `mpk`, as DualUse's `encParseP`), the coins in the order of
   `encCoinsLaw` (framed `cbdRP`/`floodP`, `law_seq_app` as `law_setupP`), `c_m` (`mulRMP`,
   `addRMP`, the word of `2^{K−1}` at coefficient `0` when `μ`), the frame of the output (`frameApP`);
6. the law (`EncSpec D (cbdR D 16) (cbdR D 16) (floodR D eFl)`, i.e. `χc χc χfl` at `Dc`) and the
   costs (`VB` chain as `SetupTime`; dominated by `c^aut`: `b · 4K² · 2K` rows of `2K` products,
   about `2^{56}` products of `22 N² K²` sweeps each, top `≈ 2^{98}`: clock `≈ 2^{240}`).
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
4. *The machine*: an `XProg` (as `DualUse/Prog/KeyGenP.keyGenF`): `leP n` guard (`n` = length of
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
  predicate words longer than `L`, as DualUse's `key_long`), `Eval = evalMachineX`), from
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

Files `SigabaNeo/Lib/Lattices/FloodRing.lean`, `SigabaNeo/Lib/Lattices/CircularRingLWEInst.lean`,
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
  `acceptProb_redM8` (as `DualUse.acceptProb_reductionP`, with `postG`/`DcB`).
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
3. ~~`authP`~~ — **done** (`Prog/AuthW`, `Prog/AuthWCost`, `Prog/AuthWX`): `authW8` (DualUse's
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
