import SigabaNeoStd.Lattices.Homomorphic.Gadget
import SigabaNeoStd.Lattices.Homomorphic.Circuit
import SigabaNeoStd.Lattices.Homomorphic.Eval
import SigabaNeoStd.Lattices.Homomorphic.BinaryDigits
import SigabaNeoStd.Lattices.Homomorphic.GTrapdoor
import SigabaNeoStd.Lattices.Homomorphic.RingGauss
import SigabaNeoStd.Lattices.Homomorphic.Norm
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import SigabaNeoStd.Lattices.Homomorphic.SLP
import SigabaNeoStd.Lattices.Homomorphic.SLPEval
import SigabaNeoStd.Lattices.Homomorphic.Depth
import SigabaNeoStd.Lattices.Homomorphic.NoiseGadgets
import SigabaNeoStd.Lattices.Homomorphic.GSWNoise
import SigabaNeoStd.Lattices.Homomorphic.SLPSim
import SigabaNeoStd.Lattices.Homomorphic.BoolBuild
import SigabaNeoStd.Lattices.Homomorphic.BoolArith
import SigabaNeoStd.Lattices.Homomorphic.BoolCompare
import SigabaNeoStd.Lattices.Homomorphic.GSWCircuit
import SigabaNeoStd.Lattices.Homomorphic.SLPShadow
import SigabaNeoStd.Lattices.Homomorphic.GSWGates

/-!
# Homomorphic evaluation over rings

* `Homomorphic/Gadget`: gadget digits over any commutative ring, gadget matrices `G = I ⊗ g` and
  `G · G⁻¹(A) = A`, the Ring-GSW gadget and its top row.
* `Homomorphic/BinaryDigits`: the binary gadget digits of `ℤ_q[X]/(X^N + 1)`, cslib-frontier's
  `Cslib.Negacyclic (ZMod q) N`, and the bits of the coefficients of a matrix (`coeffBits`).
* `Homomorphic/Circuit`: NAND circuits, evaluated in a ring; every Boolean function is one
  (`Circuit.ofFun`).
* `Homomorphic/GTrapdoor`: the gadget trapdoor `B = [A₀ | g − A₀ T]` over a ring and its exact
  preimages.
* `Homomorphic/RingGauss`: Gaussian preimages of a row over `ℤ_q[X]/(X^N + 1)`: the discrete
  Gaussian on the solutions of `∑_c L_c z_c = y`.
* `Homomorphic/Norm`, `Homomorphic/NoiseBound`: the coefficient norm of `ℤ_q[X]/(X^N + 1)`
  (`cnorm (a * b) ≤ N · cnorm a · cnorm b`) and the noise of homomorphic evaluation
  (`rnorm_evalErr_le`: at most `errBound (|W| N) E f` with binary digits).
* `Homomorphic/SLP`, `Homomorphic/SLPEval`: straight-line programs (shared NAND gates) and their
  homomorphic evaluation: the BGG+ key relation, the Ring-GSW invariant and the noise.
* `Homomorphic/BoolBuild`, `Homomorphic/BoolArith`: building Boolean programs: gates, adders,
  constants, and addition and subtraction modulo `q`, with their values.
* `Homomorphic/BoolCompare`: comparisons of wires with constants and Boolean combinations of
  them (`BExp`, `compile`).
* `Homomorphic/GSWCircuit`: the Ring-GSW evaluation of a circuit as a polynomial-size Boolean
  program on the bits of the ciphertexts (`fhatProgram`, `fhatProgram_spec`).
* `Homomorphic/Eval`: one evaluation for BGG+ public keys and Ring-GSW ciphertexts; the BGG+ key
  relation, the Ring-GSW invariant, and the evaluation of matrix-valued functions (`MatrixBits`).

The NAND step follows the algebra of mxx's `BggMultiplication` (`crates/khe/lean`,
`claude/dsl-simplification-arbitrary-compute-e010f1` at `2b71aef`, MIT License, Copyright (c) 2025
Machina iO).
-/
