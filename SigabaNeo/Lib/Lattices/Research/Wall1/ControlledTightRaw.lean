import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledTerminalCaps

/-! Inward-volume certificates for the radius-250 exit and the initial prefix at 2896. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open QaryMembership DualExit DualExit.Certificate Finset MeasureTheory Metric
open TerminalProjection TerminalProjection.Restart506
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem raw_numeric {n d k : ℕ} {r : ℝ} {b c p s : ℕ}
    (hd : Fintype.card (Coord 400 n) = d) (hk : d = 2*k+1) (hr : 0 ≤ r) (hq : r < 3329)
    (hc : 0 < c) (hs : 0 < s) (hb : r^2 + d/4 ≤ ((b:ℝ)/c)^2)
    (cert : 2*b^d*22^k*2^(k+1)*s < p*c^d*7^k*d.doubleFactorial*3329^400) :
    probability (fun A : Design 400 n 3329 ↦ rawShort A r) < (p : ℝ)/s := by
  have dim : Module.finrank ℝ (Space 400 n) = d := by simpa using hd
  have hV := InnerProductSpace.volume_ball_of_dim_odd (dim.trans hk) (0 : Space 400 n) 1
  have vol : volume.real (ball (0 : Space 400 n) 1) =
      Real.pi^k * 2^(k+1) / d.doubleFactorial := by
    rw [Measure.real, hV, dim, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hR := (Real.sqrt_le_left (show 0 ≤ (b:ℝ)/c by positivity)).mpr hb
  have hpi : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  have hD : (0:ℝ) < d.doubleFactorial := by positivity
  have hcert : 2*(b:ℝ)^d*22^k*2^(k+1)*s <
      p*(c:ℝ)^d*7^k*(d.doubleFactorial:ℝ)*3329^400 := by exact_mod_cast cert
  apply (rawShort_bound hr (by exact_mod_cast hq)).trans_lt
  unfold inwardVolume
  rw [hd, vol]
  have hv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ Real.pi_pos.le hpi k) (show 0 ≤ (2:ℝ)^(k+1) by positivity)) hD.le
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) hR _) hv
      (by positivity) (by positivity)) (by norm_num : (0:ℝ) ≤ 2)) (by positivity)) _
  simp only [div_pow]
  have hc' : 0 < (c:ℝ) := by exact_mod_cast hc
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  field_simp
  simpa only [Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hcert

set_option maxRecDepth 10000 in
theorem raw250_tight :
    probability (fun A : Design 400 511 3329 ↦ rawShort A 250) < 235454 / (10:ℝ)^17 := by
  simp only [← Nat.cast_ofNat (R := ℝ) (n := 10), ← Nat.cast_pow]
  apply raw_numeric (r := 250) (k := 455) (d := 911) (b := 501) (c := 2) (p := 235454) (s := 10^17)
    (by simp [Coord]) (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
  decide +kernel

set_option maxRecDepth 10000 in
theorem initial2896_numeric :
    probability (fun A : Design 400 105 3329 ↦ rawShort A 2896) < 7 / (10:ℝ)^34 := by
  simp only [← Nat.cast_ofNat (R := ℝ) (n := 10), ← Nat.cast_pow]
  apply raw_numeric (r := 2896) (k := 252) (d := 505) (b := 2897) (c := 1) (p := 7) (s := 10^34)
    (by simp [Coord]) (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
  decide +kernel

theorem probability_or_le (P Q : Sample → Prop) :
    probability (fun A ↦ P A ∨ Q A) ≤ probability P + probability Q := by
  have he : designs (fun A ↦ P A ∨ Q A) = designs P ∪ designs Q := by ext; simp [designs]
  simp only [probability, he, ← add_div, ← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_union_le _ _) (by positivity)

theorem bad_bound_tight_raw : probability (fun A ↦ ¬Good A) < 235454/(10:ℝ)^17 + 8147/(10:ℝ)^17 := by
  have hr : probability rawBad < 235454/(10:ℝ)^17 := by
    unfold rawBad
    rw [prefix_probability (by decide : 511 ≤ 512) (fun A ↦ rawShort A 250)]
    exact raw250_tight
  have hd : probability dualBad ≤ probability restartExit :=
    probability_mono (fun _ ⟨t,_,h⟩ ↦ ⟨t,h⟩)
  exact (probability_mono (P := fun A ↦ ¬Good A) (Q := fun A ↦ rawBad A ∨ dualBad A)
    (by intro A h; by_cases hr : rawBad A; exact Or.inl hr; exact Or.inr (by
      by_contra hd; exact h ⟨hr,hd⟩))).trans_lt
    ((probability_or_le _ _).trans_lt (add_lt_add hr (hd.trans_lt restart_exit_numeric)))

/-- Reassemble the first moment with the tighter raw exit before rounding. -/
theorem terminal_bound_with_prefix_tight_raw :
    probability terminalHit < probability residual₁ + probability residual₂ + probability Prefix
      + 4.613860465762 / (10 : ℝ)^12 := by
  have split := probability_mono (P := terminalHit)
    (Q := fun A ↦ (Good A ∧ terminalHit A) ∨ ¬Good A)
    (fun A h ↦ by by_cases hg : Good A <;> simp [hg,h])
  have h := split.trans (probability_or_le _ _)
  linarith only [h, bad_bound_tight_raw,
    good_first_moment (concrete_late HermiteWitness506.Sphere.laterDeterminantFloor),
    LateEnclosures.positive394_sum, LateEnclosures.positive30_sum, LateEnclosures.horizontal406_sum]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.raw250_tight
#print axioms SigabaNeo.Wall1.ControlledPlane.initial2896_numeric
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_with_prefix_tight_raw
