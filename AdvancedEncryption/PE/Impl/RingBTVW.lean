import PE.Impl.RingBTVW.Scheme
import PE.Impl.RingBTVW.Laws

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

* `Scheme`: the algorithms, correctness, and the algebra of the security proof.
* `Laws`: the distributions of the coins.

The lattice tools it uses are in `SigabaNeo.Lib.Lattices.Homomorphic` and
`SigabaNeo.Lib.Lattices.Decode`.
-/
