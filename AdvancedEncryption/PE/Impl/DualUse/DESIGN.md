# Ring BTVW17 §4.2 with dual use and an efficient reduction

The scheme in `PE/Impl/RingBTVW` encrypts the attribute with fresh Ring-LWE samples (as mxx's
PE). Its security proof reduces the game laws exactly to Ring-LWE, but the reduction samples keys
from their ideal law with no trapdoor, so it is not efficient. This directory rebuilds the scheme
with the paper's dual-use ciphertexts, so that keys are simulated with the gadget trapdoor `W_f`
(BTVW17 `KeyGen*`), and every statistical step is the leftover hash lemma for binary inputs.

## Scheme (over `R_q = ℤ_q[X]/(X^N + 1)`, `q = 2^K`, binary gadget)

* `Setup`: `B = [B₀ | B₁]`, `B₀ ∈ R^{1×m}` uniform, `B₁ = [1 | ā | g − (t ā + e)]` with trapdoor
  `T = [e; t I; I]` (`B₁ T = g`); `B_j ∈ R^{1×W}` uniform for every bit `j` of the attribute
  ciphertexts; `p` uniform.
* `Enc(x, M)`: secret `s`, `c = s B + e₀` (so `c₀' = s B₀ + e₀'` is its `B₀` part),
  `A = [B₀; c₀']`, `Ψᵢ = A Rᵢ + xᵢ G` with binary integer `Rᵢ ∈ {0,1}^{m×W}`, `c_j = s(B_j − ψ_j G̲) + e_j`
  with flooding errors `e_j`, `κ = s p + e' + M ⌊q/2⌋`.
* `KeyGen(f)`: `B_f̂` as before; a key `[B | B_f̂] sk = p` by one try of box rejection
  (`SigabaNeo.Lattices.boxSample`) with the trapdoor of `B₁`.
* `Dec`: as before.

## Hybrids (selective; `x`, `M` fixed)

1. `B_j := B₀ W_j + ψ_j G̲` with binary `W_j` — LHL, seed `B₀` (`isTwoUniversal_binaryHash`), one
   column at a time; the rest of the view is a function of independent coins.
2. Keys with the trapdoor `W_f` of `[B₀ | B₀ W_f + G̲]` (`keyMatrix_sim`) instead of `T` — exact
   (`boxSample_eq`), given a public bound covering both trapdoors.
3. `B₁ := uniform` — Ring-LWE on `(ā, t ā + e)`; the reduction knows every `W`.
4. `c_j := c₀' W_j + e_j''` — noise flooding (`closeTo_shift_vec`).
5. `(c, s p + e')` uniform — Ring-LWE; the reduction computes `Ψ`, `B_j`, `c_j` from `c₀'` and keys
   from `W_f`: efficient.
6. Keys from their ideal law (exact), then `A Rᵢ` and `A W_j` uniform — LHL, seed `A = [B₀; c₀']`
   (two rows) — and `κ` a one-time pad: the view no longer depends on `(x, M)`.

## Done

* `SigabaNeo.Lattices.slp_sim_relation`, `RingBTVW.keyMatrix_sim` (hybrid 2's algebra).
* `SigabaNeo.Lattices.isTwoUniversal_binaryHash`, `closeTo_binaryHash` (hybrids 1, 6; Lib
  `Lattices/LeftoverHash`).
* `DualUse.decryptRaw_eq` (correctness, exactly); `DualUse.decrypt_correct_of_bounds` over `R_q`
  (the noise reduces to `PE.Impl.RingBTVW`'s with `aᵢ = B₀ Rᵢ`, `eΨᵢ = e₀ Rᵢ`).
* `DualUse.hybrid1` (hybrid 1, over any finite ring and coin laws: within
  `|J|·|W|·√(|R|·2^{−|Wd|})/2`).
* `DualUse.hybrid4`, `DualUse.viewW_real_eq` (hybrid 4: encodings `c₀ W_j + e_j`, under a
  flooding hypothesis; `SigabaNeo.Lattices.closeTo_floodLaw_add` gives it over `R_q`).
* `DualUse.real5_eq`, `DualUse.unif5_eq` (hybrid 5: the normal-form Ring-LWE reduction gives the
  view of hybrid 4 on a real instance and `h5View` on a uniform one).
* `DualUse.hybrid6`, `DualUse.finalView_indep` (hybrid 6 from the view `h5View`, and the final
  view does not depend on `(x, M)`).
* `DualUse.keyLaw_real_eq_sim` (hybrid 2: real and simulated keys have the same law),
  `DualUse.valid_of_mem_support` (keys are valid unless the try aborts).
* `SigabaNeo.Lattices.boxSample_eq` (hybrid 2's exactness).

* `DualUse.attributeHiding` (`Security.lean`): **the whole chain**: for any continuation `D` (the
  adversary with a key oracle depending on `mpk` only), the games for `(x₀, M₀)` and `(x₁, M₁)`
  are within `2 (δ₁ + ε + δ₆)` plus the Ring-LWE advantages of the reductions of hybrids 3
  (`reduction3`, secret `t`) and 5 (`reduction5`, normal form) for both challenges.

* `DualUse.attributeHiding_rlwe` (`Registry.lean`): the reductions' instance laws are the
  registry's Ring-LWE laws, through explicit word distinguishers.
* Coins: `BitLaws.lean`, `SetupLaw.lean` (every law of the scheme is an image of fair coins), and
  `SigabaNeo.Lattices.BitLaw.uniformOfFinset_map` (the big box).
* **Machines** (`Impl.lean`): `DualUse.impl hk c` for the date-window universe, from a
  configuration `Conf` (ring degree, `q = 2^K`, `|Wd|`, error law, flooding width, boxes,
  decomposition, `L`). `Setup`, `Enc`, `KeyGen` realize the scheme's laws exactly
  (`Machine.exists_finiteAlg`), `Dec` computes the decryption, and `Eval`
  (`Gates.DateWindow.winEvalMachine`) authorizes only window predicates, so correctness concerns
  finitely many circuits. `DualUse.expressive` for `L ≥ dateBound`.
* **Correctness** (`ImplCorrect.lean`): `DualUse.correct`: `PE.Correct` under conditions on the
  parameters (gadget inverse, box coverage by the real trapdoor, short coins, noise bound of every
  window predicate below `q/4`, abort probability of an inner box at most `2^{-κ}`).

## To do

* Concrete parameters: a `Conf` and proofs of the conditions of `DualUse.correct` (trapdoor norm
  from the error law's support, box sizes for abort `≤ 2^{-128}`, the noise bound of the window
  circuits).
* Machine-level attribute hiding: the math-level chain is done (`attributeHiding_rlwe`); the
  Trusted definition (`HardAt`: `cost / adv² ≥ 2^λ` with explicit cost) needs either reductions
  as machines with explicit step counts or a relaxed definition. Pending the user's decision.

## Relation to mxx's PE (`codes/mxx`, branch `claude/dsl-simplification-arbitrary-compute-e010f1`)

* **Attribute ciphertexts.** mxx's `crates/pe` encrypts `x_t` as `[a_t; −s̄ a_t + e_t] + X^(Bz x_t) G`
  with a fresh uniform `a_t` (`encryption`). `PE/Impl/RingBTVW` follows it; its security proof is
  exact but samples keys from their ideal law. This directory returns to the paper's
  `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G`, which gives the simulation trapdoor `W_f` and an efficient reduction.
* **Trapdoor.** mxx uses the statistical TrapGen `[ā | g − ā T]` (regularity by the leftover hash
  lemma, `budget`). Here `B₁ = [1 | a | G̲ − (t a + e)]` is pseudorandom under Ring-LWE (hybrid 3),
  and the leftover hash lemma is used for binary integer matrices only (`LeftoverHash`).
* **Predicates and noise.** mxx evaluates branching programs with exponent lookups, not a Ring-GSW
  circuit `f̂`; its date class (`PeClass::date()`) uses `n = 2^15` and `log₂ Q ≈ 355` with a
  worst-case phase error below `Q / 4` (`crates/pe/lean/average-w256-n32768-crt15x24-compact`).
  The noise of `f̂` here grows with the depth of the bit-level Ring-GSW evaluation, so concrete
  parameters for the date windows need a much larger modulus; they are not fixed yet.
* **Gadget algebra.** The NAND step of `Lib/Lattices/Homomorphic` follows mxx's
  `BggMultiplication` (`crates/khe/lean`).
