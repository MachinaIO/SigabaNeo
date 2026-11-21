import PE.Impl.RingBTVW.Scheme
import PE.Impl.RingBTVW.Laws
import PE.Impl.RingBTVW.Security

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

* `Scheme`: the algorithms, correctness, and the algebra of the security proof.
* `Laws`: the distributions of the coins.
* `Security`: the attribute-hiding game, the hybrids, and the reduction to Ring-LWE
  (`attributeHiding`).

The lattice tools it uses are in `SigabaNeo.Lib.Lattices.Homomorphic` and
`SigabaNeo.Lib.Lattices.Decode`.
-/
