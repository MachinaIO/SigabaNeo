import PE.Impl.RingBTVW.Fresh.Scheme
import PE.Impl.RingBTVW.Fresh.Laws
import PE.Impl.RingBTVW.Fresh.Noise
import PE.Impl.RingBTVW.Fresh.Security
import PE.Impl.RingBTVW.Fresh.Simulation

/-!
# The ring variant of the BTVW17 §4.2 predicate encryption

* `Scheme`: the algorithms, correctness, and the algebra of the security proof.
* `Laws`: the distributions of the coins.
* `Noise`: the noise of decryption bounded by the errors and the key, and correctness when
  `4 · noiseBound + 2 < q` (`decrypt_correct_of_bounds`).
* `Security`: the attribute-hiding game and its reduction to Ring-LWE: the advantage of any
  adversary is the sum of the Ring-LWE advantages of two explicit distinguishers
  (`attributeHiding`; its distinguishers sample keys from the ideal law, so they are not yet
  efficient).
* `Simulation`: with the paper's Ring-GSW ciphertexts `Ψᵢ = A Rᵢ + xᵢ G` and simulated public keys
  `B_j = B₀ W_j + ψ_j G̲`, the key matrix is `B₀ W_f + f(x) G̲` (`keyMatrix_sim`): keys for
  unauthorized predicates have the gadget trapdoor `W_f`.

The lattice tools it uses are in `SigabaNeoStd.Lattices.Homomorphic` and
`SigabaNeoStd.Lattices.Decode`.
-/
