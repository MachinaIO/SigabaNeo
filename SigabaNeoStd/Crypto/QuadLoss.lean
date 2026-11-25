import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A quadratic loss in reductions

A reduction whose machines cost at most `C · a²`, where `a` is the cost of the adversary (at least
`1`), turns `k`-bit hardness with `2^k ≥ 2^(2λ+6) · C` into `λ` bits: if the advantage `g` is at
most a statistical term `s` (with `4 · 2^λ · s² ≤ 1`) plus three advantages `dᵢ` of the
reductions, each with `2^k dᵢ² ≤ C a²`, then `2^λ g² ≤ a` (`quad_loss`). When `a ≥ 2^λ` this is
trivial; otherwise the quadratic cost loses only a factor `a < 2^λ`.

A reduction whose machines cost at most `C · a` loses no factor in `λ`: with `2^k ≥ 36 · 2^λ · C`
and each `2^k dᵢ² ≤ C a`, again `2^λ g² ≤ a` (`lin_loss`).
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

/-- **The linear loss.** -/
theorem lin_loss (P Q C a s d₁ d₂ d₃ g : ℝ) (hP : 0 < P) (hQ : 36 * P * C ≤ Q)
    (hC : 0 < C) (ha : 1 ≤ a) (hs : 4 * P * s ^ 2 ≤ 1) (hs0 : 0 ≤ s)
    (h₁ : Q * d₁ ^ 2 ≤ C * a) (h₂ : Q * d₂ ^ 2 ≤ C * a) (h₃ : Q * d₃ ^ 2 ≤ C * a)
    (hg : |g| ≤ s + |d₁| + |d₂| + |d₃|) : P * g ^ 2 ≤ a := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  -- `P dᵢ² ≤ a / 36`
  have hd : ∀ d : ℝ, Q * d ^ 2 ≤ C * a → P * d ^ 2 ≤ a / 36 := by
    intro d hd
    have h1 : 36 * P * C * d ^ 2 ≤ Q * d ^ 2 := by nlinarith [sq_nonneg d]
    have h2 : 36 * P * C * d ^ 2 ≤ C * a := h1.trans hd
    have h3 : C * (36 * P * d ^ 2) ≤ C * a := by linarith
    have := le_of_mul_le_mul_left h3 hC
    linarith
  have e₁ := hd d₁ h₁
  have e₂ := hd d₂ h₂
  have e₃ := hd d₃ h₃
  have hg0 : 0 ≤ |g| := abs_nonneg g
  have hsq : g ^ 2 ≤ (s + |d₁| + |d₂| + |d₃|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hg0 hg 2
  have hb : (s + |d₁| + |d₂| + |d₃|) ^ 2 ≤ 2 * s ^ 2 + 6 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by
    have a1 := sq_abs d₁; have a2 := sq_abs d₂; have a3 := sq_abs d₃
    nlinarith [sq_nonneg (s - |d₁| - |d₂| - |d₃|), sq_nonneg (|d₁| - |d₂|), sq_nonneg (|d₂| - |d₃|),
      sq_nonneg (|d₁| - |d₃|)]
  have : P * g ^ 2 ≤ P * (2 * s ^ 2 + 6 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2)) :=
    mul_le_mul_of_nonneg_left (hsq.trans hb) hP.le
  nlinarith

end SigabaNeo
