import PE.Impl.RingBTVW.Scheme
import PE.Impl.RingBTVW.Laws
import PE.Impl.RingBTVW.Noise
import PE.Impl.RingBTVW.Security

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

* `Scheme`: the algorithms, correctness, and the algebra of the security proof.
* `Laws`: the distributions of the coins.
* `Noise`: the noise of decryption bounded by the errors and the key, and correctness when
  `4 · noiseBound + 2 < q` (`decrypt_correct_of_bounds`).
* `Security`: the attribute-hiding game and its reduction to Ring-LWE: the advantage of any
  adversary is the sum of the Ring-LWE advantages of two explicit distinguishers
  (`attributeHiding`).

The lattice tools it uses are in `SigabaNeo.Lib.Lattices.Homomorphic` and
`SigabaNeo.Lib.Lattices.Decode`.
-/
