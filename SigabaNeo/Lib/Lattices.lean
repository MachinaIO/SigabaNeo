import SigabaNeo.Lib.Lattices.Basic
import SigabaNeo.Lib.Lattices.Gaussian
import SigabaNeo.Lib.Lattices.Encoding
import SigabaNeo.Lib.Lattices.Gadget
import SigabaNeo.Lib.Lattices.Gaussian.Facts
import SigabaNeo.Lib.Lattices.Stat
import SigabaNeo.Lib.Lattices.Hardness
import SigabaNeo.Lib.Lattices.LWE
import SigabaNeo.Lib.Lattices.RingLWE
import SigabaNeo.Lib.Lattices.ModuleLWE
import SigabaNeo.Lib.Lattices.Trapdoor
import SigabaNeo.Lib.Lattices.Trapdoor.Family

/-!
# Lattice library

Definitions and facts shared by claims and solutions (`SigabaNeo.Lattices`):

* `Basic`: `Z^m ⊂ R^m`, `Λ^⊥(B)`, independent draws.
* `Gaussian`: the discrete Gaussians `D_{Z,s}` (`gaussZ`) and `D_{Λ^⊥(B)+c,τ}` (`cosetGauss`);
  `Gaussian/*`: their sums, smoothing, tails and point masses.
* `Encoding`: matrices over `Z_q` as numbers and bit strings.
* `Gadget`: the gadget matrix and binary decomposition.
* `LWE`, `RingLWE`, `ModuleLWE`: the assumptions, concrete (`SigabaNeo.Assumption`: parameters,
  problem, security function) and asymptotic (cslib-frontier).
* `Hardness`: the security function of the concrete assumptions (`docs/LWE_HARDNESS.md`).
* `Trapdoor`: the ideal preimage distribution and trapdoor samplers (`Trapdoor.Exists`);
  `Trapdoor/Family`: a sampler for one parameter family (`Trapdoor.Family.exists_sampler`).
* `Prob`, `Stat`: expectations and statistical distance.
-/
