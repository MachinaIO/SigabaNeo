import Solution.Pre1
import Solution.Pre2
import Solution.PostRefute
import Solution.Trapdoor

/-!
# A refutation of `TestCase.EvLWE.target` under LWE

The target is private-coin evasive LWE for the sampler of [DJMMV25], Construction 5.1: if Pre1
and Pre2 are computationally indistinguishable, so is Post. Under decision LWE with a public
modulus (`TestCase.EvLWE.lwe`, the hypothesis `h₀`):

* Pre1 holds outright, statistically (`pre1_holds`, `Solution/Pre1.lean`);
* Pre2 holds by a uniform strict PPT reduction to LWE (`pre2_of_lwe`, `Solution/Pre2.lean`);
* Post fails: a uniform strict PPT distinguisher has advantage at least `1/32` for all large `κ`
  (`not_post`, `Solution/PostRefute.lean`).

The definition of EvLWE samples `K` from the coset Gaussian and fixes no algorithm. Separately,
`trapdoor_sampling` (`Solution/Trapdoor.lean`, from the library's
`Trapdoor.Family.exists_sampler`) shows that `K` can be sampled in polynomial time with
a trapdoor for `B`: an MP12 gadget trapdoor (`GenTrap`) and randomized preimage sampling
(`SamplePre`) are strict PPT, and for all large `κ` and every `P` their `(B, K)` is within a
negligible distance of a uniform `B` with the coset Gaussian preimage of `P`. The refutation does
not use it.
-/

namespace TestCase.EvLWE

open TestCase

theorem refutation (h₀ : EvLWE.lwe) : ¬ EvLWE.target := fun h =>
  not_post (h pre1_holds (pre2_of_lwe h₀))

end TestCase.EvLWE
