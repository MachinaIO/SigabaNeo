import SigabaNeo.Lib.Lattices.Basic
import SigabaNeo.Lib.Lattices.Gaussian
import SigabaNeo.Lib.Lattices.Encoding
import SigabaNeo.Lib.Lattices.Gadget
import SigabaNeo.Lib.Lattices.Gaussian.Facts
import SigabaNeo.Lib.Lattices.Stat
import SigabaNeo.Lib.Lattices.Hardness
import SigabaNeo.Lib.Lattices.Reduction.BKZ
import SigabaNeo.Lib.Lattices.LWE
import SigabaNeo.Lib.Lattices.RingLWE
import SigabaNeo.Lib.Lattices.ModuleLWE
import SigabaNeo.Lib.Lattices.Trapdoor
import SigabaNeo.Lib.Lattices.Trapdoor.Family
import SigabaNeo.Lib.Lattices.Homomorphic
import SigabaNeo.Lib.Lattices.Decode
import SigabaNeo.Lib.Lattices.LeftoverHash
import SigabaNeo.Lib.Lattices.BoxSampler
import SigabaNeo.Lib.Lattices.Boxes
import SigabaNeo.Lib.Lattices.Flood
import SigabaNeo.Lib.Lattices.RingLWEInst
import SigabaNeo.Lib.Lattices.CoinMaps
import SigabaNeo.Lib.Lattices.BitLaw
import SigabaNeo.Lib.Lattices.SimNorm
import SigabaNeo.Lib.Lattices.Algo.Words
import SigabaNeo.Lib.Lattices.Algo.RingWords
import SigabaNeo.Lib.Lattices.Algo.MatWords
import SigabaNeo.Lib.Lattices.Algo.SLPWords
import SigabaNeo.Lib.Lattices.Algo.FhatLoop
import SigabaNeo.Lib.Lattices.Algo.FhatShadow
import SigabaNeo.Lib.Lattices.Algo.FhatGates
import SigabaNeo.Lib.Lattices.Algo.Coins
import SigabaNeo.Lib.Lattices.Algo.SimWords
import SigabaNeo.Lib.Lattices.Algo.BoxWords
import SigabaNeo.Lib.Lattices.ProgAlgo.Blocks
import SigabaNeo.Lib.Lattices.ProgAlgo.MulAlg
import SigabaNeo.Lib.Lattices.ProgAlgo.RingProgs
import SigabaNeo.Lib.Lattices.ProgAlgo.MulRW
import SigabaNeo.Lib.Lattices.ProgAlgo.Digits
import SigabaNeo.Lib.Lattices.ProgAlgo.MatAdd
import SigabaNeo.Lib.Lattices.ProgAlgo.MatMul
import SigabaNeo.Lib.Lattices.ProgAlgo.Transpose
import SigabaNeo.Lib.Lattices.ProgAlgo.Hash
import SigabaNeo.Lib.Lattices.ProgAlgo.Gadget
import SigabaNeo.Lib.Lattices.ProgAlgo.Nand
import SigabaNeo.Lib.Lattices.ProgAlgo.Spec
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPTape
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPPK
import SigabaNeo.Lib.Lattices.ProgAlgo.SpecT
import SigabaNeo.Lib.Lattices.ProgAlgo.SimSLP
import SigabaNeo.Lib.Lattices.ProgAlgo.GateListLayout
import SigabaNeo.Lib.Machines.Prog.Lookup
import SigabaNeo.Lib.Lattices.ProgAlgo.BoxProgs
import SigabaNeo.Lib.Lattices.ProgAlgo.SimTmpl
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySum
import SigabaNeo.Lib.Lattices.ProgAlgo.KeySumT
import SigabaNeo.Lib.Lattices.ProgAlgo.SimStepT
import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenTape

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
