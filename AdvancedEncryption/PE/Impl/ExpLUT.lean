import PE.Impl.ExpLUT.Basic
import PE.Impl.ExpLUT.Ops
import PE.Impl.ExpLUT.LUT
import PE.Impl.ExpLUT.Eval
import PE.Impl.ExpLUT.Noise
import PE.Impl.ExpLUT.Canonical
import PE.Impl.ExpLUT.NegacyclicNorm
import PE.Impl.ExpLUT.Scheme
import PE.Impl.ExpLUT.Correctness
import PE.Impl.ExpLUT.KeyGen
import PE.Impl.ExpLUT.CorrectBound
import PE.Impl.ExpLUT.Laws
import PE.Impl.ExpLUT.SimForm
import PE.Impl.ExpLUT.SimEval
import PE.Impl.ExpLUT.SimBound
import PE.Impl.ExpLUT.SimTrap
import PE.Impl.ExpLUT.SimKeys
import PE.Impl.ExpLUT.GameChain
import PE.Impl.ExpLUT.Params.Conf
import PE.Impl.ExpLUT.Params.Noise
import PE.Impl.ExpLUT.Params.Correct
import PE.Impl.ExpLUT.BPBridge

/-!
# Predicate encryption from lookup tables over exponents (ePrint 2026/2539 §4–§5)

The algebra of §4 and the scheme and correctness of §5, over an abstract ring with automorphisms
(`SigabaNeo.Lattices.ExpRing`); see `PE/Impl/ExpLUT/PLAN.md`.

* `Basic`: the setting (`Setting`), encodings (`Encodes`), gadget ciphertexts (`IsGC`).
* `Ops`: Add, SMul, Mul (eq. (1)), Aut_k (eq. (2)) with exact output equations.
* `LUT`: the rounds along the binary basis and the lookup tables (Lemma 8).
* `Eval`: branching programs over encodings (Lemma 9, exact).
* `Noise`: norm-level bounds (Lemma 9's `γ`, `Δ`).
* `Canonical`, `NegacyclicNorm`: the canonical setting `idx j = g^j` (Lemma 8 discharged) and the
  coefficient norm of `ℤ_q[X]/(X^{2^e} + 1)`.
* `Scheme`: Setup, Enc, KeyGen matrices (eq. (3)), Dec (§5.1).
* `Correctness`: eq. (4) and Theorem 1 exactly; `CorrectBound`: at the norm level.
* `KeyGen`: keys by box rejection, with a trapdoor-independent law.
* `Laws`: the laws of the coins; Theorem 1 in probability.

The proof of Theorem 2 (Appendix A):

* `SimForm`, `SimEval`, `SimBound`: simulation forms (Definition 3), Lemma 10, Corollary 1 and the
  coefficient bound `B_R̂`.
* `SimTrap`, `SimKeys`: Lemma 11 (the gadget trapdoor `X` and `T_sim`), the key laws.
* `HybLaws`, `HybView`, `Hybrid0`, `Hybrid12`, `Hybrid3`, `Reduction`, `Hybrid5`, `Hybrid5U`,
  `Hybrid6`: the hybrids H0–H6 and the reduction to circular Ring-LWE.
* `GameChain`: the chain over the generic attribute-hiding game.
* `Params/Conf`: the concrete configuration (`q = 2^{2^16} − 1`, `n = 2^24`, `W = 2^22`, `m̄`, laws,
  key boxes and their cover bound); `Params/Noise`: the noise certificate (Lemma 9, Lemma 11's
  shift, `corrBound < q/4`); `Params/Correct`: correctness at the concrete parameters.
* `BPBridge`: the universe's programs of width `w8` as branching programs; correctness for them.
-/
