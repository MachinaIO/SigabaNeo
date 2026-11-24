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
