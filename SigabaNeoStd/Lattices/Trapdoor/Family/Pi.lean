import SigabaNeoStd.Lattices.Trapdoor.Family.Gen
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Trapdoor sampler: a certified approximation of `π`

`piInt P J = 16 · Σ_{j<J} (−1)^j ⌊2^P / ((2j+1) 5^{2j+1})⌋ − 4 · Σ_{j<J} (−1)^j ⌊2^P / ((2j+1) 239^{2j+1})⌋`
is within `20 J + 40 · 2^P · 25^{−J}` of `π · 2^P` (`piInt_err`): Machin's formula
`π = 16 arctan(1/5) − 4 arctan(1/239)` (Mathlib), the arctangent series with its geometric tail
(`arctan_sum_err`), and one unit of rounding per term (`fpSum_err`).
-/

namespace SigabaNeo.Lattices.Trapdoor.Family

open Real

/-- The partial arctangent series. -/
noncomputable def arctanSum (x : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1)

theorem hasSum_arctan_real {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1)) (Real.arctan x) := by
  have h := Complex.hasSum_arctan (z := (x : ℂ)) (by simpa using hx)
  rw [← Complex.ofReal_arctan] at h
  refine (Complex.hasSum_ofReal).mp ?_
  convert h using 1
  funext j
  push_cast
  ring

set_option maxHeartbeats 2000000 in
theorem arctan_sum_err {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (J : ℕ) :
    |Real.arctan x - arctanSum x J| ≤ 2 * x ^ (2 * J + 1) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have hs := hasSum_arctan_real hx
  have htail := (hs.summable.sum_add_tsum_nat_add J).symm
  rw [hs.tsum_eq] at htail
  unfold arctanSum
  rw [htail, add_sub_cancel_left]
  have hgeo : Summable fun i : ℕ => x ^ (2 * (i + J) + 1) := by
    have : (fun i : ℕ => x ^ (2 * (i + J) + 1)) = fun i => x ^ (2 * J + 1) * (x ^ 2) ^ i := by
      funext i; rw [← pow_mul, ← pow_add]; ring_nf
    rw [this]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have habs : ∀ i : ℕ, |(-1) ^ (i + J) * x ^ (2 * (i + J) + 1) / (2 * (i + J : ℕ) + 1)| ≤
      x ^ (2 * (i + J) + 1) := by
    intro i
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_nonneg h0]
    apply div_le_self (by positivity)
    rw [abs_of_nonneg (by positivity)]
    have : (0 : ℝ) ≤ (i + J : ℕ) := Nat.cast_nonneg _
    linarith
  calc |∑' i, (-1) ^ (i + J) * x ^ (2 * (i + J) + 1) / (2 * (i + J : ℕ) + 1)|
      ≤ ∑' i, x ^ (2 * (i + J) + 1) := by
        have hs1 : Summable fun i : ℕ =>
            ‖(-1) ^ (i + J) * x ^ (2 * (i + J) + 1) / (2 * (i + J : ℕ) + 1)‖ := by
          simp only [Real.norm_eq_abs]
          exact Summable.of_nonneg_of_le (fun i => abs_nonneg _) habs hgeo
        have := (norm_tsum_le_tsum_norm hs1).trans
          (hs1.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact habs i) hgeo)
        rwa [Real.norm_eq_abs] at this
    _ = x ^ (2 * J + 1) * (1 - x ^ 2)⁻¹ := by
        have : (fun i : ℕ => x ^ (2 * (i + J) + 1)) = fun i => x ^ (2 * J + 1) * (x ^ 2) ^ i := by
          funext i; rw [← pow_mul, ← pow_add]; ring_nf
        rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by nlinarith)]
    _ ≤ 2 * x ^ (2 * J + 1) := by
        have h : (1 - x ^ 2)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by nlinarith) (by norm_num)]
          nlinarith
        calc x ^ (2 * J + 1) * (1 - x ^ 2)⁻¹ ≤ x ^ (2 * J + 1) * 2 :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 2 * x ^ (2 * J + 1) := mul_comm _ _

/-! ### Fixed point -/

/-- `⌊2^P / ((2j+1) d^{2j+1})⌋`. -/
def fpTerm (d P j : ℕ) : ℕ := 2 ^ P / ((2 * j + 1) * d ^ (2 * j + 1))

/-- The fixed-point partial sum. -/
def fpSum (d P J : ℕ) : ℤ := ∑ j ∈ Finset.range J, (-1) ^ j * (fpTerm d P j : ℤ)

theorem fpTerm_err (d P j : ℕ) (hd : 0 < d) :
    |(fpTerm d P j : ℝ) - 2 ^ P * ((1 / (d : ℝ)) ^ (2 * j + 1) / (2 * j + 1))| ≤ 1 := by
  unfold fpTerm
  have hpos : (0 : ℝ) < (2 * j + 1) * (d : ℝ) ^ (2 * j + 1) := by positivity
  have hpos' : 0 < (2 * j + 1) * d ^ (2 * j + 1) := by positivity
  have h1 := Nat.div_mul_le_self (2 ^ P) ((2 * j + 1) * d ^ (2 * j + 1))
  have h2 := Nat.lt_div_mul_add (a := 2 ^ P) hpos'
  have e : 2 ^ P * ((1 / (d : ℝ)) ^ (2 * j + 1) / (2 * j + 1)) =
      (2 ^ P : ℕ) / ((2 * j + 1) * (d : ℝ) ^ (2 * j + 1)) := by
    rw [div_pow, one_pow]; push_cast; field_simp
  rw [e, abs_le]
  have hq : ((2 ^ P / ((2 * j + 1) * d ^ (2 * j + 1)) : ℕ) : ℝ) * ((2 * j + 1) * (d : ℝ) ^ (2 * j + 1))
      ≤ (2 ^ P : ℕ) := by exact_mod_cast h1
  have hq' : ((2 ^ P : ℕ) : ℝ) < ((2 ^ P / ((2 * j + 1) * d ^ (2 * j + 1)) : ℕ) : ℝ) *
      ((2 * j + 1) * (d : ℝ) ^ (2 * j + 1)) + (2 * j + 1) * (d : ℝ) ^ (2 * j + 1) := by
    exact_mod_cast h2
  have hQ1 := (le_div_iff₀ hpos).mpr hq
  have hQ2 : ((2 ^ P : ℕ) : ℝ) / ((2 * j + 1) * (d : ℝ) ^ (2 * j + 1)) <
      ((2 ^ P / ((2 * j + 1) * d ^ (2 * j + 1)) : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hpos).mpr (by linarith)
  constructor <;> linarith

theorem fpSum_err (d P J : ℕ) (hd : 0 < d) :
    |(fpSum d P J : ℝ) - 2 ^ P * arctanSum (1 / d) J| ≤ J := by
  unfold fpSum arctanSum
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range J, |(-1) ^ j * (fpTerm d P j : ℝ) -
        2 ^ P * ((-1) ^ j * (1 / (d : ℝ)) ^ (2 * j + 1) / (2 * j + 1))|
      ≤ ∑ _j ∈ Finset.range J, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        have : (-1 : ℝ) ^ j * (fpTerm d P j : ℝ) -
            2 ^ P * ((-1) ^ j * (1 / (d : ℝ)) ^ (2 * j + 1) / (2 * j + 1)) =
            (-1) ^ j * ((fpTerm d P j : ℝ) - 2 ^ P * ((1 / (d : ℝ)) ^ (2 * j + 1) / (2 * j + 1))) := by
          ring
        rw [this, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact fpTerm_err d P j hd
    _ = J := by simp

/-- `π · 2^P`, approximately. -/
def piInt (P J : ℕ) : ℤ := 16 * fpSum 5 P J - 4 * fpSum 239 P J

theorem piInt_err (P J : ℕ) :
    |(piInt P J : ℝ) - Real.pi * 2 ^ P| ≤ 20 * J + 40 * 2 ^ P * (1 / 5) ^ (2 * J + 1) := by
  have hM := four_mul_arctan_inv_5_sub_arctan_inv_239
  have e5 := fpSum_err 5 P J (by norm_num)
  have e239 := fpSum_err 239 P J (by norm_num)
  have a5 := arctan_sum_err (x := 1 / 5) (by norm_num) (by norm_num) J
  have a239 := arctan_sum_err (x := 1 / 239) (by norm_num) (by norm_num) J
  have h239 : (1 / 239 : ℝ) ^ (2 * J + 1) ≤ (1 / 5) ^ (2 * J + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hpi : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    rw [one_div, one_div]; linarith
  unfold piInt
  push_cast
  rw [hpi]
  have hP : (0 : ℝ) ≤ 2 ^ P := by positivity
  push_cast at e5 e239
  rw [abs_le] at e5 e239 a5 a239 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left a5.1 hP, mul_le_mul_of_nonneg_left a5.2 hP,
    mul_le_mul_of_nonneg_left a239.1 hP, mul_le_mul_of_nonneg_left a239.2 hP,
    mul_le_mul_of_nonneg_left h239 hP]

end SigabaNeo.Lattices.Trapdoor.Family
