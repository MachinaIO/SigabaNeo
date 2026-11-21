import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A quadratic loss in reductions

A reduction whose machines cost at most `C · a²`, where `a` is the cost of the adversary (at least
`1`), turns `k`-bit hardness with `2^k ≥ 2^(2λ+6) · C` into `λ` bits: if the advantage `g` is at
most a statistical term `s` (with `4 · 2^λ · s² ≤ 1`) plus three advantages `dᵢ` of the
reductions, each with `2^k dᵢ² ≤ C a²`, then `2^λ g² ≤ a` (`quad_loss`). When `a ≥ 2^λ` this is
trivial; otherwise the quadratic cost loses only a factor `a < 2^λ`.
-/

namespace SigabaNeo

/-- **The quadratic loss.** -/
theorem quad_loss (P Q C a s d₁ d₂ d₃ g : ℝ) (hP : 0 < P) (hQ : 64 * P ^ 2 * C ≤ Q)
    (hC : 0 < C) (ha : 1 ≤ a) (hs : 4 * P * s ^ 2 ≤ 1) (hs0 : 0 ≤ s)
    (h₁ : Q * d₁ ^ 2 ≤ C * a ^ 2) (h₂ : Q * d₂ ^ 2 ≤ C * a ^ 2) (h₃ : Q * d₃ ^ 2 ≤ C * a ^ 2)
    (hg : |g| ≤ s + |d₁| + |d₂| + |d₃|) (hg1 : g ^ 2 ≤ 1) : P * g ^ 2 ≤ a := by
  by_cases haP : P ≤ a
  · nlinarith
  · rw [not_le] at haP
    -- each advantage is at most `a / (8 P)`
    have hd : ∀ d : ℝ, Q * d ^ 2 ≤ C * a ^ 2 → |d| ≤ a / (8 * P) := by
      intro d hd
      have hQpos : 0 ≤ Q := le_trans (by positivity) hQ
      have h8 : 0 < 8 * P := by positivity
      have hsq : d ^ 2 ≤ (a / (8 * P)) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by positivity)]
        have : 64 * P ^ 2 * C * d ^ 2 ≤ Q * d ^ 2 := by nlinarith [sq_nonneg d]
        nlinarith [sq_nonneg d, sq_nonneg a]
      exact abs_le_of_sq_le_sq' hsq (by positivity) |> fun h => abs_le.mpr h
    have e₁ := hd d₁ h₁
    have e₂ := hd d₂ h₂
    have e₃ := hd d₃ h₃
    have hD : |g| ≤ s + 3 * (a / (8 * P)) := by linarith
    have hg0 : 0 ≤ |g| := abs_nonneg g
    have hsq : g ^ 2 ≤ (s + 3 * (a / (8 * P))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ hg0 hD 2
    have hx : 0 ≤ a / (8 * P) := by positivity
    have hbound : (s + 3 * (a / (8 * P))) ^ 2 ≤ 2 * s ^ 2 + 18 * (a / (8 * P)) ^ 2 := by
      nlinarith [sq_nonneg (s - 3 * (a / (8 * P)))]
    have h2 : P * (2 * s ^ 2) ≤ 1 / 2 := by nlinarith
    have h3 : P * (18 * (a / (8 * P)) ^ 2) ≤ 9 * a / 32 := by
      have : P * (18 * (a / (8 * P)) ^ 2) = 9 * a ^ 2 / (32 * P) := by
        field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith

end SigabaNeo
