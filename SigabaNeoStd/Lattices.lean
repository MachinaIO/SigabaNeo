import SigabaNeoStd.Lattices.Basic
import SigabaNeoStd.Lattices.Gaussian
import SigabaNeoStd.Lattices.Encoding
import SigabaNeoStd.Lattices.Gadget
import SigabaNeoStd.Lattices.Gaussian.Facts
import SigabaNeoStd.Lattices.Stat
import SigabaNeoStd.Lattices.Hardness
import SigabaNeoStd.Lattices.Reduction.BKZ
import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.RingLWE
import SigabaNeoStd.Lattices.ModuleLWE
import SigabaNeoStd.Lattices.Estimator.Bound.Cbd
import SigabaNeoStd.Lattices.Trapdoor
import SigabaNeoStd.Lattices.Trapdoor.Family
import SigabaNeoStd.Lattices.Homomorphic
import SigabaNeoStd.Lattices.Decode
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Flood
import SigabaNeoStd.Lattices.RingLWEInst
import SigabaNeoStd.Lattices.CoinMaps
import SigabaNeoStd.Lattices.BitLaw
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Algo.Words
import SigabaNeoStd.Lattices.Algo.RingWords
import SigabaNeoStd.Lattices.Algo.MatWords
import SigabaNeoStd.Lattices.Algo.SLPWords
import SigabaNeoStd.Lattices.Algo.FhatLoop
import SigabaNeoStd.Lattices.Algo.FhatShadow
import SigabaNeoStd.Lattices.Algo.FhatGates
import SigabaNeoStd.Lattices.Algo.Coins
import SigabaNeoStd.Lattices.Algo.SimWords
import SigabaNeoStd.Lattices.Algo.BoxWords
import SigabaNeoStd.Lattices.ProgAlgo.Blocks
import SigabaNeoStd.Lattices.ProgAlgo.MulAlg
import SigabaNeoStd.Lattices.ProgAlgo.RingProgs
import SigabaNeoStd.Lattices.ProgAlgo.MulRW
import SigabaNeoStd.Lattices.ProgAlgo.Digits
import SigabaNeoStd.Lattices.ProgAlgo.MatAdd
import SigabaNeoStd.Lattices.ProgAlgo.MatMul
import SigabaNeoStd.Lattices.ProgAlgo.Transpose
import SigabaNeoStd.Lattices.ProgAlgo.Hash
import SigabaNeoStd.Lattices.ProgAlgo.Gadget
import SigabaNeoStd.Lattices.ProgAlgo.Nand
import SigabaNeoStd.Lattices.ProgAlgo.Spec
import SigabaNeoStd.Lattices.ProgAlgo.SLPTape
import SigabaNeoStd.Lattices.ProgAlgo.SLPPK
import SigabaNeoStd.Lattices.ProgAlgo.SpecT
import SigabaNeoStd.Lattices.ProgAlgo.SpecZ
import SigabaNeoStd.Lattices.ProgAlgo.SimSLP
import SigabaNeoStd.Lattices.ProgAlgo.GateListLayout
import SigabaNeoStd.Machines.Prog.Lookup
import SigabaNeoStd.Lattices.ProgAlgo.BoxProgs
import SigabaNeoStd.Lattices.ProgAlgo.SimTmpl
import SigabaNeoStd.Lattices.ProgAlgo.KeySum
import SigabaNeoStd.Lattices.ProgAlgo.KeySumT
import SigabaNeoStd.Lattices.ProgAlgo.SimStepT
import SigabaNeoStd.Lattices.ProgAlgo.ValArith
import SigabaNeoStd.Lattices.ProgAlgo.ValLeaves
import SigabaNeoStd.Lattices.ProgAlgo.ValRounds
import SigabaNeoStd.Lattices.ProgAlgo.ValCoef
import SigabaNeoStd.Lattices.ProgAlgo.ValCoefFull
import SigabaNeoStd.Lattices.ProgAlgo.FhatGenTape

/-!
# Lattice library

Definitions and facts shared by claims and solutions (`SigabaNeo.Lattices`):

* `Basic`: `Z^m ⊂ R^m`, `Λ^⊥(B)`, independent draws.
* `Gaussian`: the discrete Gaussians `D_{Z,s}` (`gaussZ`) and `D_{Λ^⊥(B)+c,τ}` (`cosetGauss`);
  `Gaussian/*`: their sums, smoothing, tails and point masses.
* `Encoding`: matrices over `Z_q` as numbers and bit strings.
* `Gadget`: the gadget matrix and binary decomposition.
* `LWE`, `RingLWE`, `ModuleLWE`: the assumptions, concrete (`SigabaNeo.Trusted.Assumption`:
  parameters, problem, security function) and asymptotic (cslib-frontier).
* `Reduction/`: lattice reduction and SVP tools shared by the attacks — `LLL`, `BKZ` (GSA-free bound on the first
  vector of a BKZ-reduced basis, `docs/PROOF_GAP.md`), `Hermite2`, `AvgBKZ`, `Slide`, `Sieve`, `SieveWide`,
  `QArySieve`, `Search`, `Rogers`.
* `Attacks/` (entry point `Attacks.lean`): proofs of LWE attacks — `Primal`, `Dual`, `Bkw`, `Guess`, `AroraGe`, `Mitm`
  (`docs/ATTACK_PROOFS.md`).
* `Research/`: the open walls and recorded obstructions — `Wall1`, `Wall2`, `Wall1Rej`, `PolyQ`, `Rerand`, `RevMink`.
* `Estimator/`: the lattice estimator's attack cost models; `estimatorBits` is the `H` of the
  concrete assumptions (`docs/LWE_ESTIMATOR.md`).
* `Hardness`: an earlier conservative bound, kept as a cross-check (`docs/LWE_HARDNESS.md`).
* `Trapdoor`: the ideal preimage distribution and trapdoor samplers (`Trapdoor.Exists`);
  `Trapdoor/Family`: a sampler for one parameter family (`Trapdoor.Family.exists_sampler`).
* `Prob`, `Stat`: expectations and statistical distance.
* `Homomorphic/` (entry point `Homomorphic.lean`): gadget matrices over a ring and the binary digits
  of `ℤ_q[X]/(X^N + 1)` (cslib-frontier's `Cslib.Negacyclic`), NAND circuits, and their homomorphic evaluation on BGG+ encodings and
  Ring-GSW ciphertexts (the key relation and the Ring-GSW invariant).
* `LeftoverHash`: the leftover hash lemma for `x ↦ A · x` with a uniform matrix over any finite ring
  and binary inputs (`isTwoUniversal_binaryHash`, `closeTo_binaryHash`).
* `BoxSampler`: one try of preimage sampling by box rejection (Lyubashevsky–Wichs); its law does
  not depend on the trapdoor (`boxSample_eq`).
* `Flood`: noise flooding over `ℤ_q[X]/(X^N + 1)`: wide uniform errors hide a fixed shift
  (`closeTo_floodLaw_add`).
* `RingLWEInst`: the registry's Ring-LWE laws as laws on ring elements (`ringReal`,
  `ringLWE_realLaw_eq`, `ringLWE_idealLaw_eq`).
* `CoinMaps`: samples from fair coins (`bitsToZMod`, `uniform_bitsToZMod`).
* `BitLaw`: laws that are images of `m` uniform bits, closed under `pure`, `map`, `bind` and
  independent products; uniform residues mod `2^K`.
* `Decode`: threshold decoding of a bit `M · ⌊q/2⌋ + e` in `ℤ_q` and in `ℤ_q[X]/(X^N + 1)`, exact when
  `4|e| + 2 < q`.
* `Algo/`: bit-level algorithms, first-order loops over words proven equal to the mathematical
  definitions, with step counts — `Words` (fixed-width arithmetic mod `2^K` on `zmodEnc` words),
  `RingWords` (negacyclic addition and schoolbook multiplication on `ringEnc` words), `MatWords`
  (matrix sums and products, the binary gadget `G̲` and `G̲⁻¹`, the BGG+ NAND `G̲ − A G̲⁻¹(B)`),
  `SLPWords` (`EvalF` of programs and the key-matrix sum on words), `FhatLoop` (the compiler of `f̂`
  with explicit orders and gadget coefficients, equal to `fhatSLP` at the chosen orders), `Coins`
  (one try of box rejection as a function of a fixed number of fair coins), `SimWords` (the
  simulated short matrices `slpSim`/`evalSim` of `KeyGen*` on words, both binary gadgets).
* `ProgAlgo/`: the word algorithms of `Algo/` as programs of the verified tape language
  (`SigabaNeo.Tape.Prog`, compiled to machines by `Prog.toMachine`), with their laws, length and
  time bounds and state counts; interface in `ProgAlgo/Spec` (laws placed on any distinct tapes,
  bounds `C · (L + 1) ^ d`, state counts) — `Blocks` (block-wise programs on ring words: `addRW`,
  `subRW`), `MulAlg` (the product by Horner's rule in `X⁻¹`), `RingProgs` and `MulRW` (`mulRW`),
  `Digits` (`digitRW`, `monoW`, `constW`), `MatAdd` (`matAddW`, `matSubW`), `MatMul` (`matMulW`),
  `Gadget` (`ginvW`, `gadW`), `Nand` (`nandPKW`), `SimTmpl` (the content templates `gadW`,
  `gswGadW`, `zeroW`, `oneW` of the simulation step), `KeySum` (the key-matrix sum `keySumMW` read
  from the final store of an SLP evaluator, and `W_f`: the sum plus one block; bounds, per tape by
  the abstract interpreter, in `KeySumT`).
-/
