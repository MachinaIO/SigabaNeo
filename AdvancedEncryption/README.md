# AdvancedEncryption

Advanced encryption primitives defined in the form of Sigaba Neo primitives
(`SigabaNeo.Trusted.Primitive`, [../docs/PRIMITIVES.md](../docs/PRIMITIVES.md)). The
implementation-agnostic definitions are the problem author's; implementations go in `PE/Impl/`,
apart from the definitions to review.

| Module | Primitive |
| --- | --- |
| `PE` (`PE.lean`) | predicate encryption, weakly attribute-hiding (ePrint 2017/795, Section 3.2), concrete: correctness `≥ 1 − 2^{-κ}`, attribute hiding `cost / advantage² ≥ 2^λ`; predicates are the implementation's (any representation, meaning given by its `Eval`), and must express the universe's required predicates; cost: steps of one `Setup`, `q_k` `KeyGen`, `q` `Enc` and `Dec`, plus each machine's description length |
| `PE.BranchingProgram` (`PE/BranchingProgram.lean`) | predicate encryption for arbitrary branching programs: a 128-bit attribute read as 16 symbols of 8 bits, programs of 16 steps over 2^32 states (step `i` reads symbol `i`, `z₀ = 0`), authorized iff the last output bit is `0`; one-bit messages; `λ = κ = 128`, one run of each algorithm. The algorithms' inputs stay generic: an implementation proves that its predicates express every branching program |

| Implementation | Contents |
| --- | --- |
| `PE.Impl.RingBTVW` (`PE/Impl/RingBTVW/`) | the ring variant of the BTVW17 §4.2 scheme (Ring-GSW and BGG+ under one secret, over `ℤ_q[X]/(X^N + 1)`, with fresh Ring-LWE samples for the attribute ciphertexts as in mxx's PE): algorithms, the laws of their coins, correctness (`scheme_correct`; `decrypt_correct_of_bounds`: correct when `4 · noiseBound + 2 < q`, the noise bounded by the errors and the key; `decryption_error_le`: with bounded errors and Gaussian keys, a decryption error has probability at most `3 · 2^{−m}`), and an exact reduction of attribute hiding to Ring-LWE (`attributeHiding`: the advantage is the sum of the Ring-LWE advantages of two distinguishers; they answer key queries from the ideal key law, without a trapdoor, so they are not yet efficient and do not yet give computational security). The key sampler `gaussKeySampler` draws keys from the discrete Gaussian on their coset. Predicates are wires of straight-line programs; `f̂` is a polynomial-size Boolean program compiled gate by gate (Lib `fhatSLP`). Not yet: its efficient trapdoor realization, and Turing machines for `Setup`, `Enc`, `KeyGen`, `Dec` |
| `PE.Impl.DualUse` (`PE/Impl/DualUse/`, design in `DESIGN.md`, branching-program plan and status in `BP_PLAN.md`) | the ring BTVW17 §4.2 scheme with the paper's dual-use attribute ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` and an efficient security reduction: correctness over `R_q` (`decrypt_correct_of_bounds`), keys by box rejection whose law does not depend on the trapdoor (`keyLaw_real_eq_sim`), and attribute hiding (`attributeHiding`) by the leftover hash lemma (hybrids 1, 6), noise flooding (hybrid 4) and two Ring-LWE reductions (hybrids 3, 5, the main one in normal form). Final result (`Submission.lean`): `spec_submission : Spec BranchingProgram.primitive registry submission` and `valid_submission`, from decision Ring-LWE alone at 965 bits (ring degree 2^36, `log₂ q = 2^27`, certified 2650), with cost `N = 2^818` (clocks Setup 2^387, KeyGen 2^629, Enc 2^452, Dec 2^629; description lengths 2^300, 2^817, 2^300, 2^689) |
| `PE.Impl.Gates` (`PE/Impl/Gates/`) | predicates as NAND straight-line programs; for branching programs the mux-tree register program `bpRP` (`BPCircuit`: value `evalBool_bpPred`, depth ≤ 1054, `1443·2^39 − 770` instructions, < 312 slots, all proved without enumeration) and the program word (`BPWord`: `bpLen = 481·2^40`, `tablesOf`, `expressive_bp`) |

The project requires the core at `..` and shares its packages (`packagesDir = "../.lake/packages"`),
so build the core first:

```bash
lake build                          # at the repository root
cd AdvancedEncryption && lake build
```
