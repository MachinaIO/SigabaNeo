import SigabaNeo.Lib.Lattices.Estimator.Bound.Cbd

/-! The per-block-size checks of `Params/Strength.lean`, at `N = 2^34`, `q = 2^(2^25)`, `CBD(16)`,
`kb = 2650`. -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

/-- The LWE samples of hybrid 3: `N · 2k`. -/
abbrev M3 : ℕ := 2 ^ 34 * (2 ^ 26 + 2)

/-- The LWE samples of hybrid 5: `N · (|Wd| + 4k + 1)`. -/
abbrev M5 : ℕ := 2 ^ 34 * (2 ^ 61 + 2 ^ 27 + 5)

/-- The check at hybrid 3's instance. -/
abbrev chk3 : ℕ → Bool := cbdCheck (2 ^ 34 * 1) (2 ^ 25) M3 2650

/-- The check at hybrid 5's instance. -/
abbrev chk5 : ℕ → Bool := cbdCheck (2 ^ 34 * 1) (2 ^ 25) M5 2650

end AdvancedEncryption.DualUse.Params.Strength
