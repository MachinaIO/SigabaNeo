# AdvancedEncryption

Advanced encryption primitives defined in the form of Sigaba Neo primitives
(`SigabaNeo.Trusted.Primitive`, [../docs/PRIMITIVES.md](../docs/PRIMITIVES.md)). The
implementation-agnostic definitions are the problem author's; implementations go in `PE/Impl/`,
apart from the definitions to review.

| Module | Primitive |
| --- | --- |
| `PE` (`PE.lean`) | predicate encryption, weakly attribute-hiding (ePrint 2017/795, Section 3.2), concrete: correctness `≥ 1 − 2^{-κ}`, attribute hiding `cost / advantage² ≥ 2^λ`; predicates are the implementation's (any representation, meaning given by its `Eval`), and must express the universe's required predicates; cost: steps of one `Setup`, `q_k` `KeyGen`, `q` `Enc` and `Dec`, plus each machine's description length |
| `PE.DateWindow` (`PE/DateWindow.lean`) | the measured case of ePrint 2026/2539 (Section 7.1, Table 1): a date window, a range and a format (regular-expression) check, on a 10-bit attribute, one-bit messages; `λ = κ = 128`, one run of each algorithm. The algorithms' inputs stay generic: an implementation proves that its predicates (circuits, branching programs, …) express every date window |

| Implementation | Contents |
| --- | --- |
| `PE.Impl.RingBTVW` (`PE/Impl/RingBTVW/`) | the ring variant of the BTVW17 §4.2 scheme (Ring-GSW and BGG+ under one secret, over `ℤ_q[X]/(X^N + 1)`, with fresh Ring-LWE samples for the attribute ciphertexts as in mxx's PE): algorithms, the laws of their coins, correctness (`scheme_correct`; `decrypt_correct_of_bounds`: correct when `4 · noiseBound + 2 < q`, the noise bounded by the errors and the key; `decryption_error_le`: with bounded errors and Gaussian keys, a decryption error has probability at most `3 · 2^{−m}`), and security under Ring-LWE alone (`attributeHiding`: the advantage is the sum of the Ring-LWE advantages of two explicit reductions). The key sampler `gaussKeySampler` draws keys from the discrete Gaussian on their coset. Predicates are wires of straight-line programs; `f̂` is a polynomial-size Boolean program compiled gate by gate (Lib `fhatSLP`). Not yet: its efficient trapdoor realization, and Turing machines for `Setup`, `Enc`, `KeyGen`, `Dec` |
| `PE.Impl.Gates` (`PE/Impl/Gates/`) | predicates as NAND gate lists (the word format `SigabaNeo.unparse`): the machine of `Eval` (`evalMachine L`, constant outside the inputs of length at most `L`; `authorized_iff`), and for `PE.DateWindow` the window predicates (`winWord`, from comparisons with constants) and `expressive`: an implementation with this `Eval` and `L ≥ dateBound` expresses every date window |

The project requires the core at `..` and shares its packages (`packagesDir = "../.lake/packages"`),
so build the core first:

```bash
lake build                          # at the repository root
cd AdvancedEncryption && lake build
```
