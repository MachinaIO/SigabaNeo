import SigabaNeo.Lib.Lattices.Homomorphic.Gadget
import SigabaNeo.Lib.Lattices.Homomorphic.Circuit
import SigabaNeo.Lib.Lattices.Homomorphic.Eval
import SigabaNeo.Lib.Lattices.Homomorphic.BinaryDigits
import SigabaNeo.Lib.Lattices.Homomorphic.GTrapdoor
import SigabaNeo.Lib.Lattices.Homomorphic.RingGauss
import SigabaNeo.Lib.Lattices.Homomorphic.Norm
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseBound
import SigabaNeo.Lib.Lattices.Homomorphic.SLP
import SigabaNeo.Lib.Lattices.Homomorphic.SLPEval
import SigabaNeo.Lib.Lattices.Homomorphic.Depth
import SigabaNeo.Lib.Lattices.Homomorphic.SLPSim
import SigabaNeo.Lib.Lattices.Homomorphic.BoolBuild
import SigabaNeo.Lib.Lattices.Homomorphic.BoolArith
import SigabaNeo.Lib.Lattices.Homomorphic.BoolCompare
import SigabaNeo.Lib.Lattices.Homomorphic.GSWCircuit

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
