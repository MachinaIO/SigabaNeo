import SigabaNeo.Lib.Lattices.Estimator.Bound.Cbd

/-! The per-block-size checks of `Params/StrengthA.lean`, at the parameters of `confA`:
`N = 2^36`, `q = 2^(2^27)`, `k = 2^27 + 1`, `d = 2^65`, `CBD(16)`, `kb = 2650`. -/

namespace AdvancedEncryption.DualUse.Params.Strength

open SigabaNeo.Lattices.Estimator

/-- The LWE samples of hybrid 3 at `confA`: `N · 2k`. -/
abbrev MA3 : ℕ := 2 ^ 36 * (2 ^ 28 + 2)

/-- The LWE samples of hybrid 5 at `confA`: `N · (d + 4k + 1)`. -/
abbrev MA5 : ℕ := 2 ^ 36 * (2 ^ 65 + 2 ^ 29 + 5)

/-- The check at hybrid 3's instance at `confA`. -/
abbrev chkA3 : ℕ → Bool := cbdCheck (2 ^ 36 * 1) (2 ^ 27) MA3 2650

/-- The check at hybrid 5's instance at `confA`. -/
abbrev chkA5 : ℕ → Bool := cbdCheck (2 ^ 36 * 1) (2 ^ 27) MA5 2650

end AdvancedEncryption.DualUse.Params.Strength
