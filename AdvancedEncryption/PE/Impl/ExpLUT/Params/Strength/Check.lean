import PE.Impl.ExpLUT.Params.Strength.Generic

/-! The per-block-size checks of `Params/Strength.lean`, at ExpLUT's parameters: `q = 2^K − 1`
with `K = 2^16` (`log₂ q = K · 2^P − 1` in fixed point), every sample count `≥ M₀ = N`, and

* `chkA`: ring degree `N = 2^24`, target `kb = 1155` bits, primal margin `W = 40`;
* `chkB`: ring degree `N = 2^23`, target `kb = 495` bits, primal margin `W = 18`.

Both targets are the largest at which every block size passes. -/

namespace AdvancedEncryption.ExpLUT.Params

open SigabaNeo.Lattices.Estimator Fx

/-- The check at `N = 2^24`. -/
abbrev chkA : ℕ → Bool :=
  cbdCheckQ (2 ^ 24) (((2 ^ 16 : ℕ) : ℤ) * ONE - 1) (2 ^ 24) 1155 40

/-- The check at `N = 2^23`. -/
abbrev chkB : ℕ → Bool :=
  cbdCheckQ (2 ^ 23) (((2 ^ 16 : ℕ) : ℤ) * ONE - 1) (2 ^ 23) 495 18

end AdvancedEncryption.ExpLUT.Params
