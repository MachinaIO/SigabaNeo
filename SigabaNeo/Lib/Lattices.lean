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
-/
