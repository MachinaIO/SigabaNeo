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
