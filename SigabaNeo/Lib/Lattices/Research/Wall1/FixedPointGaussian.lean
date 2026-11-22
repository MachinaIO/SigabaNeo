module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# Error of the fixed-point Gaussian recurrence (Part 141, Lemma 4)

The input constants approximate exp(−λ) and exp(−2λ). Every multiplication floors
the product to the binary grid, including the multiplication updating the weight.
-/

@[expose] public section

namespace SigabaNeo.Wall1

open Real

noncomputable section

/-- Multiply and round down on the grid with F fractional binary digits. -/
def fpMul (F : ℕ) (a b : ℝ) : ℝ := (⌊a * b * 2^F⌋ : ℤ) / (2 : ℝ)^F

private theorem fpMul_floor (F : ℕ) (a b : ℝ) :
    fpMul F a b ≤ a*b ∧ a*b - fpMul F a b ≤ 1 / 2^F := by
  have h : 0 < (2 : ℝ)^F := by positivity
  refine ⟨(div_le_iff₀ h).mpr (Int.floor_le _), ?_⟩
  unfold fpMul
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h]
  linarith [Int.lt_floor_add_one (a*b*2^F)]

private theorem fpMul_unit {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (F : ℕ) :
    fpMul F a b ∈ Set.Icc 0 1 := by
  refine ⟨div_nonneg ?_ (by positivity), (fpMul_floor F a b).1.trans ?_⟩
  · exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (mul_nonneg ha.1 hb.1) (by positivity))
  · exact (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa using hb.2)

private theorem fpMul_error {a b A B : ℝ} (F : ℕ)
    (hA : A ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    |fpMul F A B - a*b| ≤ |A-a| + |B-b| + 1 / 2^F := by
  have hf := fpMul_floor F A B
  have hr : |fpMul F A B - A*B| ≤ 1 / 2^F := by rw [abs_of_nonpos (by linarith)]; linarith
  have hAB : |A*B - a*b| ≤ |A-a| + |B-b| := by
    rw [show A*B-a*b = (A-a)*b + A*(B-b) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hA.1, abs_of_nonneg hb.1]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb.2)
      (mul_le_of_le_one_left (abs_nonneg _) hA.2)
  have htri := abs_add_le (fpMul F A B - A*B) (A*B - a*b)
  rw [sub_add_sub_cancel] at htri
  linarith

/-- (Approximate ratio, approximate weight) after x updates. -/
def fpGaussian (F : ℕ) (E₁ E₂ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (E₁, 1)
  | x + 1 =>
    let p := fpGaussian F E₁ E₂ x
    (fpMul F p.1 E₂, fpMul F p.2 p.1)

private theorem fpGaussian_unit (F : ℕ) {E₁ E₂ : ℝ}
    (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1) (x : ℕ) :
    (fpGaussian F E₁ E₂ x).1 ∈ Set.Icc 0 1 ∧ (fpGaussian F E₁ E₂ x).2 ∈ Set.Icc 0 1 := by
  induction x with
  | zero => exact ⟨h₁, zero_le_one, le_rfl⟩
  | succ x ih => exact ⟨fpMul_unit ih.1 h₂ F, fpMul_unit ih.2 ih.1 F⟩

/-- At index x the ratio error is at most (x+1)(δ+2⁻ᶠ) and the weight error is at most
x(x+3)(δ+2⁻ᶠ)/2. -/
theorem fpGaussian_errors (F : ℕ) {E₁ E₂ lam δ : ℝ} (hl : 0 ≤ lam)
    (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1)
    (hE₁ : |E₁ - exp (-lam)| ≤ δ) (hE₂ : |E₂ - exp (-2*lam)| ≤ δ) (x : ℕ) :
    |(fpGaussian F E₁ E₂ x).1 - exp (-lam*(2*x+1))| ≤ (x+1) * (δ + 1 / 2^F) ∧
    |(fpGaussian F E₁ E₂ x).2 - exp (-lam*(x:ℝ)^2)| ≤
      (x:ℝ)*(x+3)/2 * (δ + 1 / 2^F) := by
  have hd := (abs_nonneg _).trans hE₁
  have hf : 0 < 1 / (2 : ℝ)^F := by positivity
  induction x with
  | zero => simpa [fpGaussian] using (show |E₁ - exp (-lam)| ≤ δ + 1 / 2^F by linarith)
  | succ x ih =>
    let r := exp (-lam*(2*x+1))
    let v := exp (-lam*(x:ℝ)^2)
    have hr : r ∈ Set.Icc 0 1 := ⟨(exp_pos _).le, exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (by positivity))⟩
    have he : exp (-2*lam) ∈ Set.Icc 0 1 := ⟨(exp_pos _).le, exp_le_one_iff.mpr (by linarith)⟩
    have hunit := fpGaussian_unit F h₁ h₂ x
    have hstep₁ := fpMul_error (a := r) (B := E₂) F hunit.1 he
    have hstep₂ := fpMul_error (a := v) (B := (fpGaussian F E₁ E₂ x).1) F hunit.2 hr
    have er : exp (-lam * (2 * ((x:ℝ)+1) + 1)) = r * exp (-2*lam) := by
      dsimp [r]; rw [← exp_add]; congr 1; ring
    have ev : exp (-lam * ((x:ℝ)+1)^2) = v*r := by
      dsimp [r,v]; rw [← exp_add]; congr 1; ring
    simp only [Nat.cast_succ, er, ev, fpGaussian]
    change |_ - r| ≤ _ ∧ |_ - v| ≤ _ at ih
    constructor
    · linarith [ih.1]
    · nlinarith [ih.1, ih.2]

/-- Uniform radius-R version of Lemma 4. -/
theorem fpGaussian_weight_error (F : ℕ) {E₁ E₂ lam δ : ℝ} (hl : 0 ≤ lam)
    (h₁ : E₁ ∈ Set.Icc 0 1) (h₂ : E₂ ∈ Set.Icc 0 1)
    (hE₁ : |E₁ - exp (-lam)| ≤ δ) (hE₂ : |E₂ - exp (-2*lam)| ≤ δ)
    {x R : ℕ} (hx : x ≤ R) :
    |(fpGaussian F E₁ E₂ x).2 - exp (-lam*(x:ℝ)^2)| ≤
      ((R:ℝ)+2)^2 / 2 * (δ + 1 / 2^F) := by
  refine (fpGaussian_errors F hl h₁ h₂ hE₁ hE₂ x).2.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h : (x:ℝ) ≤ R := by exact_mod_cast hx
    have := mul_le_mul h (add_le_add_right h 3) (by positivity) (Nat.cast_nonneg R)
    nlinarith
  · exact add_nonneg ((abs_nonneg _).trans hE₁) (by positivity)

end
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.fpGaussian_errors
#print axioms SigabaNeo.Wall1.fpGaussian_weight_error
