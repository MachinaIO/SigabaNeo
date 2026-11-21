# Ring BTVW17 §4.2 with dual use and an efficient reduction (in progress)

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
* `DualUse.decryptRaw_eq` (correctness, exactly).
* `SigabaNeo.Lattices.boxSample_eq` (hybrid 2's exactness).

## To do

Scheme with general widths; correctness (noise with `Rᵢ`, box keys); hybrids 1–6; then the
machines (`SigabaNeo.Lib.Machines.Randomized`, `Guarded`) and the machine-level propositions.
