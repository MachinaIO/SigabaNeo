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
| `PE.Impl.RingBTVW` (`PE/Impl/RingBTVW/`) | the ring variant of the BTVW17 §4.2 scheme (Ring-GSW and BGG+ under one secret, over `ℤ_q[X]/(X^N + 1)`): algorithms, the laws of their coins, correctness (`scheme_correct`, under a bound on the noise), and the algebra of the simulation of its security proof (`keyMatrix_sim`, `simKey_valid`). Not yet: the statistical and Ring-LWE steps of security, a noise bound, polynomial-size `f̂`, and Turing machines for `PE`'s `Impl` |

The project requires the core at `..` and shares its packages (`packagesDir = "../.lake/packages"`),
so build the core first:

```bash
lake build                          # at the repository root
cd AdvancedEncryption && lake build
```
