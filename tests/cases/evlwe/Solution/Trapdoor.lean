import Definitions.Def_EvLWE
import SigabaNeo.Lib.Lattices.Trapdoor.Family

/-!
# `K` can be sampled with a trapdoor

The parameters of EvLWE are those of the library's proven trapdoor family
(`SigabaNeo.Lattices.Trapdoor.Family`), so its sampler applies: an MP12 gadget trapdoor (`GenTrap`)
and preimage sampling (`SamplePre`) are strict PPT, and their `(B, K)` is within a negligible
distance of a uniform `B` with `K ← preimage` (`Trapdoor.ideal`). The refutation does not use it.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

theorem trapdoor_sampling : Trapdoor.Exists n m k q τ τ_pos :=
  Trapdoor.Family.exists_sampler

/-- The ideal distribution of the trapdoor sampler is the one of the definition of EvLWE. -/
theorem preimage_eq_trapdoor (κ : ℕ) (d : Draw κ) :
    preimage d = Trapdoor.preimage d.B d.P (τ κ) (τ_pos κ) :=
  rfl

end TestCase.EvLWE
