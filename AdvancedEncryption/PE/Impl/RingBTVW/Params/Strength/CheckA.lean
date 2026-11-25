import SigabaNeo.Lib.Lattices.Estimator.Bound.Cbd

/-! The per-block-size checks of `Params/StrengthA.lean`, at the parameters of `confA`:
`N = 2^34`, `q = 2^(2^26)`, `k = 2^26 + 1`, `d = 2^62`, `CBD(16)`, `kb = 1158`. -/

namespace AdvancedEncryption.RingBTVW.Params.Strength

open SigabaNeo.Lattices.Estimator

/-- The LWE samples of hybrid 3 at `confA`: `N · 2k`. -/
abbrev MA3 : ℕ := 2 ^ 34 * (2 ^ 27 + 2)

/-- The LWE samples of hybrid 5 at `confA`: `N · (d + 4k + 1)`. -/
abbrev MA5 : ℕ := 2 ^ 34 * (2 ^ 62 + 2 ^ 28 + 5)

/-- The check at hybrid 3's instance at `confA`. -/
abbrev chkA3 : ℕ → Bool := cbdCheck (2 ^ 34 * 1) (2 ^ 26) MA3 1158

/-- The check at hybrid 5's instance at `confA`. -/
abbrev chkA5 : ℕ → Bool := cbdCheck (2 ^ 34 * 1) (2 ^ 26) MA5 1158

end AdvancedEncryption.RingBTVW.Params.Strength
