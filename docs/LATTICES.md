# The lattice library (`SigabaNeo/Lib/Lattices`)

Definitions and proofs shared by claims and solutions, in the namespace `SigabaNeo.Lattices`.
`import SigabaNeo.Lib.Lattices` imports all of it; a definitions file should import only the
modules it needs.
The library is part of the core and is pinned with it. Its definitions are part of the meaning of
any claim that imports them, as cslib-frontier's are, so a submitter reads them as they read their
own. Its proofs are checked by Lean when the core is built.

| Module | Contents |
| --- | --- |
| `Basic` | `embed` (`Z^m ⊂ R^m`), `kernel B`, `perp B = Λ^⊥(B)`, `toInt`; `sampleList`, `sampleMat`, `sampleFun`, `sampleOptList`; `sampleFun_support` |
| `Gaussian` | `gaussZ s` (`D_{Z,s}`) and `cosetGauss B u τ` (`D_{Λ^⊥(B)+x₀,τ}`), cslib-frontier's `ZLattice.discreteGaussian`; `cosetGauss_mem_coset`, `cosetGauss_isSome_iff` |
| `Gaussian/Sum`, `Smooth`, `Tail`, `Bounds`, `Z`, `Facts` | Gaussian sums; smoothing of `Λ^⊥(B)`; tails (`gauss_tail_gen`, `cosetGauss_tail`, `gaussZ_tail`); point masses of `D_{Z,σ}` |
| `Encoding` | `matVals`, `encEntries`, `bitsOf`, `intMod` |
| `Gadget` | `gadget n b q = I_n ⊗ (1, 2, …, 2^{b−1})`, `gadgetInv` (binary decomposition), `gadget_mulVec_gadgetInv` for `q ≤ 2^b` |
| `ModuleLWE` | concrete: `ModuleLWE.Params`, `ModuleLWE.decision`, `ModuleLWE.search` (`Assumption`s with `H`, [ASSUMPTIONS.md](ASSUMPTIONS.md)); asymptotic: `ModuleLWE.Decision m d n q secret error` (cslib-frontier's `DecisionModuleLWEWith`), `DecisionGauss`, `DecisionGaussSecret`, `gaussVec` |
| `RingLWE` | Module-LWE of rank 1: `RingLWE.decision`, `RingLWE.search`, `RingLWE.Decision` |
| `LWE` | Module-LWE at ring degree 1: `LWE.decision`, `LWE.search`, `LWE.Decision`; `LWE.DecisionPub`: with the modulus public in the sample (`encodePub`) |
| `Estimator/` | the lattice estimator's attack cost models and `estimatorBits` ([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)) |
| `Hardness` | the earlier conservative bound `securityBits` ([LWE_HARDNESS.md](LWE_HARDNESS.md)) |
| `Trapdoor` | `Trapdoor.preimage`, `Trapdoor.ideal`, `Trapdoor.Sampler`, `Trapdoor.Exists` |
| `Trapdoor/Family` | `Trapdoor.Family.exists_sampler`, for one parameter family |
| `Prob`, `Stat` | expectations (`ev`, `ind`) and statistical distance (`CloseTo`) lemmas |
| `Homomorphic/Gadget` | `GadgetDigits`, `GadgetMatrix` (`G · G⁻¹(A) = A`), `gadgetOf`, the Ring-GSW gadget `gswGadget` and its top row `topRowGadget` |
| `Homomorphic/BinaryDigits` | `binaryDigits`: the gadget digits of `ℤ_q[X]/(X^N + 1)` (cslib-frontier's `Cslib.Negacyclic`): binary digits of the coefficients, `∑ᵢ 2^i dᵢ(a) = a`; `coeffBits`: a matrix as the bits of the coefficients of its entries (`MatrixBits`) |
| `Homomorphic/Circuit` | NAND circuits `Circuit ι`, evaluated in a ring (`eval`) and on bits (`evalBool`, `eval_bits`); every Boolean function is a circuit (`ofFun`, `evalBool_ofFun`) |
| `Homomorphic/GTrapdoor` | the gadget trapdoor over a ring: `gTrapdoorMatrix` (`B = [A₀ \| g − A₀ T]`), `gTrapdoorSolve`, `gTrapdoorMatrix_mul_solve` (exact preimages; not the Gaussian sampler) |
| `Homomorphic/RingGauss` | `rowRot` (coefficient matrix of `z ↦ ∑_c L_c z_c`, `rowRot_mulVec`), `gaussPreimage` (the discrete Gaussian on the solutions over `ℤ_q[X]/(X^N + 1)`), `gaussPreimage_mem`, `gaussPreimage_isSome`, `gaussPreimage_tail` (coefficients at most `K ≥ τ√m` except with probability `3 · 2^{−m}`) |
| `Homomorphic/Norm` | `zabs` (centered absolute value in `ℤ_q`), `cnorm` (coefficient norm of `ℤ_q[X]/(X^N + 1)`): `cnorm_add_le`, `cnorm_neg`, `cnorm_sum_le`, `cnorm_mul_le` (`≤ N · cnorm a · cnorm b`) |
| `Homomorphic/NoiseBound` | `rnorm` (norm of a row), `rnorm_mul_le`, `errBound`, `rnorm_evalErr_le` (the noise of BGG+ / Ring-GSW evaluation on `0/1` inputs), `cnorm_gadgetOf_binary_ginv_le` (binary decompositions have norm `1`) |
| `Homomorphic/SLP`, `Homomorphic/SLPEval` | straight-line programs of NAND gates (`SLP`, `valueOf`, `valueOf_invariant`, `valueOf_map`); their homomorphic evaluation: `slpPK`, `slpEnc`, `slp_enc_key_relation`, `slp_gsw_invariant`, `slp_enc_noise` |
| `Homomorphic/Depth` | the depth of a program (`SLP.depth`); the noise bound is at most `(WN + 1)^depth · E` (`slpBound_le_depth`) |
| `Homomorphic/NoiseGadgets` | the noise bound through the Boolean gadgets: `nb_xorW_le`, `nb_fullAdd` (the carry grows additively), `nb_rippleAdd`, `nb_andL`, `nb_muxL`, `nb_modAdd`, `nb_modSub` (factor `modFactor WN w`) |
| `Homomorphic/GSWNoise` | the noise of evaluating `f̂` homomorphically: a NAND block multiplies by `gswFactor WN N k = modFactor^(treeHeight+1) · (WN+1)` (`nb_nandBlock`); `nb_fhatSLP`: within `gswFactor^n · E` for `n` gates |
| `Homomorphic/SLPCircuit` | `SLP.circuit`: the circuit of a wire (the unfolding, for the analysis), with `evalBool_circuit`, `eval_circuit`, `evalMat_circuit` |
| `Homomorphic/BoolBuild`, `Homomorphic/BoolArith` | building Boolean programs (`Ext`, `addNand`, logic gates) and arithmetic on wires: `rippleAdd`, `constL`, `muxL`, `andL`, `modAdd`, `modSub`, with their values |
| `Homomorphic/BoolCompare` | comparisons of wires with constants, most significant bit first (`geConst`, `leConst`, `msbVal`), and Boolean combinations of them compiled into programs (`BExp`, `compile`, `compile_spec`) |
| `Homomorphic/GSWCircuit` | the Ring-GSW NAND on the bits of the coefficients (`coeff_gswNand`, `nandBlock_spec`) and the compilation of a circuit (`compileGSW`, `fhatProgram`, `fhatProgram_spec`): polynomial size `O(|f| · (kN)² · k)`; of a straight-line program gate by gate (`compileSLP`, `fhatSLP`, `fhatSLP_spec`): one NAND block per gate |
| `Homomorphic/Eval` | `evalMat` (BGG+ `EvalF` and Ring-GSW `Eval`), `evalEnc`, `evalErr`, `evalSim`; `bgg_key_relation`, `gsw_invariant`, `sim_relation` (`Aᵢ = B Wᵢ + xᵢ G` ⇒ `A_f = B W_f + f(x) G`), `matrix_key_relation`, `matrix_key_relation_bits` (matrix-valued functions, with a bit decomposition `MatrixBits`) |
| `LeftoverHash` | the leftover hash lemma for binary inputs hashed by a uniform matrix over any finite commutative ring (`ℤ_q`, `ℤ_q[X]/(X^N + 1)`, also `q = 2^K`): `isTwoUniversal_binaryHash` (two-universal: distinct binary inputs differ by the unit `±1`), `closeTo_binaryHash` (`(A, A·x)` is within `√(|R|^r · 2^{−m}) / 2` of `(A, u)`), from cslib-frontier's general `IsTwoUniversal.leftover_hash` |
| `BoxSampler` | one try of preimage sampling by box rejection (Lyubashevsky–Wichs, uniform boxes): `boxSample_some` (every target output has probability `1/|Big|`), `boxSample_eq` (the law does not depend on the trapdoor), `PMF.ext_option` |
| `Boxes` | centered boxes in `ℤ_Q`: `cenEmb` (bits as centered residues), `ballZ`/`ball` and `card_ball` (`(2r+1)^n`), `bigBox`/`card_bigBox`, `ball_subset_bigBox`, `pow_sub_pow_le` (`a^n − (a−c)^n ≤ n c a^{n−1}`) |
| `Flood` | noise flooding over `ℤ_q[X]/(X^N + 1)`: `floodLaw` (independent coefficients uniform in `{0, …, W−1}`), `closeTo_floodLaw_add` (adding `δ` costs `∑ |δᵢⱼ| / W`); in `Stat`, `dist_shift_pi` for any finite index set |
| `RingLWEInst` | the registry's Ring-LWE (Module-LWE of rank 1) as laws over `ℤ_q[X]/(X^N + 1)`: `ringReal` (`(aᵢ, aᵢ σ + eᵢ)`), `ringLWE_realLaw_eq`, `ringLWE_idealLaw_eq` (through `encodeRing`); `sampleMat_eq_pi`, `pi_comp_equiv`, `pi_curry` |
| `Decode` | `encodeBit`, `decodeZMod`, `decodeBit`: threshold decoding of `M · ⌊q/2⌋ + e` in `ℤ_q` and at the constant coefficient of `ℤ_q[X]/(X^N + 1)`, exact when `4|e| + 2 < q` |

## Trapdoors and preimage sampling

**The ideal distribution.** `Trapdoor.preimage B P τ` draws each column `K_j` of `K` from the
discrete Gaussian of width `τ` on the coset `{x ∈ Z^m : B·x = P_j (mod q)}`, or is `none` if a coset
is empty. `Trapdoor.ideal P τ` draws a uniform `B ∈ Z_q^{n×m}` first.

**A trapdoor sampler** (`Trapdoor.Sampler n m k q τ`) is:

* `gen` (`GenTrap`): on `(κ, q)`, with `κ` unary and `q` binary, it outputs `B` (as `matVals B`) and
  a trapdoor of any type with any encoding;
* `pre` (`SamplePre`): on `(κ, q)`, the trapdoor and `P` (as `matVals P`), it outputs the columns
  of `K`.

Both are strict PPT (`IsPPTOn`). There is a negligible `err` such that, for all large `κ` and every
`P ∈ Z_q^{n×k}`, the pair `(B, K)` they produce is within statistical distance `err κ` of
`Trapdoor.ideal P (τ κ)`. `Trapdoor.Exists n m k q τ` says that a sampler exists.

**What is proved.** Only one family so far: `n = κ + 1`, `w = 8(κ + 1)`, a prime
`q ∈ (2^w, 2^{w+1}]`, `m = 2n(w + 1)`, `k = m + 1` and `τ = 2^{κ+3}` (`Trapdoor/Family/Params.lean`).
For it, `Trapdoor.Family.exists_sampler : Trapdoor.Exists n m k q τ τ_pos`. Other parameters are
later work.

## The proof for the family


`Trapdoor/Family.lean` and `Trapdoor/Family/*.lean` (file names below are in that directory):

```lean
theorem Trapdoor.Family.trapdoor_sampling :
    IsPPTOn encPub (encPair (encList encNat) (encPair (encList encNat) (encList encNat))) genAlg ∧
    IsPPTOn encInp (encList (encList encIntBin)) preAlg ∧
    Negligible errAll ∧
    ∀ᶠ κ in Filter.atTop, ∀ P, CloseTo (ProbComp.eval (trapPipe κ P))
      ((idealJ κ P).map (encBK κ)) (errAll κ)
```

`idealJ κ P` is `Trapdoor.ideal P τ` (`idealJ_eq`).
`trapPipe κ P` runs `GenTrap` on `(κ, q)` and `SamplePre` on the trapdoor and `P`. `errAll κ` is
`200 (m + 1)^4 / 2^κ + m² / 2^κ`.

**GenTrap** (`genAlg`, [MP12] Section 5). Draw `Ā ∈ Z_q^{n×mb}` entry by entry with
`sampleModNat`, with `mb = n(w + 1)` and `m = 2mb`. Draw `R ∈ {−1, 0, 1}^{mb×mb}` from two fair bits
per entry, with `P(0) = 1/2` and `P(±1) = 1/4`. Output `B = [Ā | G − ĀR]` with the gadget
`G = I_n ⊗ (1, 2, …, 2^w)` (`Gadget.lean`).

* `G` is inverted by binary decomposition because `q ≤ 2^{w+1}`.
* `xPre R v = [R z; z]` with `z = G⁻¹(v)` satisfies `B · xPre R v = v`, and its entries are at
  most `mb` in absolute value.
* `B` is within `ε_LHL = mb·√(q^n (3/8)^{mb})/2` of uniform (`LHL.lean`, `Gen.lean`). This is
  a leftover hash lemma per column of `R`, through the collision probability of `Ā r`.

**SamplePre** (`preAlg`). For each column `u` of `P`, draw `y ← D_{Z^m,τ}` and output
`x = y + xPre R (u − B y)`. Then `B x = u`, and the mass at `x` is `Σ_v D_{Z^m,τ}(x − xPre R v)`
(`Law.lean`). This is a randomized sampler of GPV type, with the trapdoor used only to shift
into the coset. Because `τ = 2^{κ+3}` is far above the trapdoor's short vectors, it is close to
the coset Gaussian:

* Smoothing (`Smooth.lean`): `Λ^⊥(B)` has `m` independent vectors of norm at most
  `√(m)·(2mb + 2)`, built from `R` and the gadget kernel. So the dual mass is at most `1/2` for
  all large `κ` (`smoothCond_eventually`), and every coset has nearly the same `ρ_τ` mass.
* On the box `|x_j| < τm`, shifting by `xPre` changes `ρ_τ` by a factor `e^{±θ}` with
  `θ ≤ 1.5 m³/2^κ` (`Close.lean`, `Close2.lean`: `colLawOf_close`, for any base law within
  factors `a` and `b` of `D_{Z^m,τ}`).

**The 1D sampler** (`samp1`, `Samp1.lean`). One attempt draws a proposal
`z ∈ [−2^A, 2^A)` and `u < 2^T`, and accepts when `u · s^E < 2^T` in exact integer arithmetic. Here
`s = Σ_{i<N} (y/E)^i/i!` is a Taylor sum for `e^{y/E}`, `y = π̂ z²/τ²`, and `π̂` comes from Machin's
formula with certified error (`Pi.lean`). The bracket `s^E ≤ e^y ≤ (s + 2/N!)^E` is in
`Exp.lean`. The sampler retries at most `Rt` times and outputs `0` if every attempt fails.

* The acceptance probability is `e^{−πz²/τ²}` up to factors `e^{±δ_P}·η_N` and `2^{−T}`
  (`Pacc.lean`).
* The output law is within factors `a₁` and `b₁` of `D_{Z,τ}` (`Law1D.lean`). Across `m`
  coordinates, `μV` is within factors `a₁^m` and `b₁^m` (`Vec.lean`).
* Every constant is `1 ± O(2^{−κ})` (`Const.lean`), so `a₁^m/b₁^m ≥ 1 − 24 m 2^{−κ}`
  (`Negl.lean`).

**The error.** `joint_close` (`Joint.lean`) gives a bound of `k·colErr + ε_LHL`, with the
columns sampled independently. This is at most `200 (m + 1)^4 / 2^κ` (`err_le`). The draw of `Ā`
by `sampleModNat` adds `n·mb·q/2^{w+1+κ} ≤ m²/2^κ` (`closeTo_DA`).

**Strict PPT** (`PPT1.lean`, `AlgPPT.lean`). Every step is certified in cslib-frontier's
polynomial-time calculus:

* the parameters, which are unary in `κ` (`Nat.log` and powers bounded by `m`);
* `π̂`, through binary integer sums;
* the acceptance test, through binary powers, factorials and comparison;
* the retry loop (`IsPPTOn.retry`);
* the `m` draws (`IsPPTOn.replicate`);
* the list form of `B` and of `y ↦ y + [Rz; z]` (`Alg.lean`, proved equal to `Bmat` and
  `gsyn`);
* the loop over the columns (`IsPPTOn.mapM`).

The law of each program is computed in `AlgLaw.lean`.
