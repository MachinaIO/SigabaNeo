import SigabaNeo.Lib.Lattices.Research.Wall1.RawGraphWitness
import SigabaNeo.Lib.Lattices.Research.Wall1.RawGraphVoid

/-! Part 222's early winner tail reduced to a deterministic count of projective
directions in a Euclidean integer ball. All probabilities use the original sample. -/

noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Real Finset ControlledPlane TerminalProjection DualExit QaryMembership RawGraphVoid
open scoped Classical Matrix
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private abbrev cols (j : ℕ) := (105+j)+1
private abbrev lastCol (j : ℕ) : Fin (cols j) := Fin.last (105+j)
private abbrev height (j : ℕ) (z : Grid 400 (cols j)) : ZMod 3329 := z (.inr (lastCol j))

private def direction (j : ℕ) (z : Grid 400 (cols j)) : Direction 400 (cols j) 3329 :=
  ((height j z)⁻¹ • reduce 3329 (fun i ↦ z (.inl i)),
   (height j z)⁻¹ • reduce 3329 (fun i ↦ z (.inr i)))

/-- Normalize the last input to one and count each full projective direction only once. -/
def rawDirections (j : ℕ) (r : ℝ) : Finset (Direction 400 (cols j) 3329) :=
  ((SigabaNeo.Planted.integerBall (ι := Coord 400 (cols j)) r).filter
    (fun z ↦ height j z ≠ 0)).image (direction j)

/-- Unconditional physical upper tail in terms of an explicit finite integer-ball count. -/
theorem winner_tail_le_of_directions {j : ℕ} (hj : j < 406) {r : ℝ} (hr : 0 ≤ r) :
    probability (fun A ↦ r < s j A) ≤ (3329:ℝ)^400 / ((3329:ℝ)^400 + (rawDirections j r).card) := by
  let T := rawDirections j r
  have normed (w) (hw : w ∈ T) : w.2 (lastCol j) = 1 := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    exact inv_mul_cancel₀ (mem_filter.mp hz).2
  let miss (B : Design 400 (cols j) 3329) := ∀ w ∈ T, ¬ incident B w
  have hcols : cols j ≤ 512 := by dsimp [cols]; omega
  have cover (A : Sample) (hl : r < s j A) : miss (designPrefix hcols A) := by
    intro w hw hit
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    obtain ⟨hb,hheight⟩ := mem_filter.mp hz
    let o (i : Fin 400) := z (.inl i)
    let v (i : Fin (cols j)) := z (.inr i)
    have hnorm : sqLength o + sqLength v ≤ r^2 := by
      simpa only [sqLength, o, v, Fintype.sum_sum_type] using
        ((SigabaNeo.Planted.mem_integerBall hr z).mp hb).2
    have hinc : designPrefix hcols A *ᵥ reduce 3329 v = reduce 3329 o := by
      change designPrefix hcols A *ᵥ ((height j z)⁻¹ • reduce 3329 v) =
        (height j z)⁻¹ • reduce 3329 o at hit
      rw [Matrix.mulVec_smul] at hit
      exact (smul_right_injective _ (inv_ne_zero hheight)) hit
    have hv : v (lastCol j) ≠ 0 := fun he ↦ hheight (by
      change ((v (lastCol j):ℤ) : ZMod 3329) = 0
      rw [he,Int.cast_zero])
    exact hl.not_ge (winner_le_of_raw_vector A hj hr o v hv hinc hnorm)
  exact (probability_mono cover).trans ((prefix_probability hcols miss).le.trans
    (void_probability (lastCol j) T normed))

private lemma rawVol_pos (j : ℕ) : 0 < rawVolume j := by
  unfold rawVolume
  exact ENNReal.toReal_pos (Metric.measure_ball_pos MeasureTheory.volume _ zero_lt_one).ne'
    MeasureTheory.measure_ball_lt_top.ne

/-- The desired bound is automatic whenever the volume term is at most four determinants. -/
theorem raw_tail_of_volume_le {j : ℕ} {r : ℝ} (hr : 0 < r)
    (hv : rawVolume j * r^(506+j) ≤ 4*3329^400) :
    probability (fun A ↦ r < s j A) ≤ 4*3329^400 / (rawVolume j * r^(506+j)) := by
  apply le_trans (b := (1:ℝ)) _ ((le_div_iff₀ (mul_pos (rawVol_pos j) (pow_pos hr _))).2
    (by simpa using hv))
  unfold probability
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).2
  rw [one_mul]
  exact Nat.cast_le.mpr (card_le_univ _)

/-- Integer radii through which the desired tail is automatic, in draw order. -/
def certifiedRadius (j : Fin 53) : ℕ :=
  (#[3329, 3307, 3269, 3232, 3194, 3158, 3122, 3087, 3052, 3018, 2984, 2951, 2918, 2885,
     2854, 2822, 2792, 2761, 2731, 2702, 2673, 2644, 2616, 2588, 2561, 2534, 2507, 2481,
     2455, 2429, 2404, 2379, 2355, 2331, 2307, 2284, 2261, 2238, 2216, 2193, 2172, 2150,
     2129, 2108, 2087, 2067, 2047, 2027, 2007, 1988, 1969, 1950, 1932] : Array ℕ)[j.val]!

private def volUpper (n : ℕ) : ℚ :=
  let p : ℚ := 3.141592653589794
  if n % 2 = 0 then p^(n/2) / (n/2).factorial
  else p^(n/2) * 2^(n/2+1) / n.doubleFactorial

private lemma rawVolume_le (j : ℕ) : rawVolume j ≤ (volUpper (506+j):ℝ) := by
  let n := 506+j
  let k := n/2
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have : Nonempty (Fin n) := ⟨⟨0, by dsimp [n]; omega⟩⟩
  have hp : π ≤ 3.141592653589794 := pi_lt_d20.le.trans (by norm_num)
  change MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤ _
  unfold volUpper
  split_ifs with e
  · have h : n = 2*k := by dsimp [k,n]; omega
    rw [MeasureTheory.Measure.real, InnerProductSpace.volume_ball_of_dim_even (dim.trans h)]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k/(Nat.factorial k:ℝ))]
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ pi_pos.le hp k) (by positivity)
  · have h : n = 2*k+1 := by dsimp [k,n]; omega
    rw [MeasureTheory.Measure.real,InnerProductSpace.volume_ball_of_dim_odd (dim.trans h),dim]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k*2^(k+1)/(Nat.doubleFactorial n:ℝ))]
    push_cast
    gcongr

set_option maxRecDepth 10000 in
private lemma radius_certificate : ∀ j : Fin 53,
    volUpper (506+j.val) * (certifiedRadius j : ℚ)^(506+j.val) ≤ 4*3329^400 := by
  decide +kernel

/-- Unconditional, draw-specific coverage, including all radii through 3307 on draw 2
and all radii through 1932 on draw 53. -/
theorem raw_tail_through_radius (j : Fin 53) {r : ℝ} (hr : 0 < r)
    (hle : r ≤ certifiedRadius j) :
    probability (fun A ↦ r < s j A) ≤ 4*3329^400 / (rawVolume j * r^(506+j.val)) := by
  apply raw_tail_of_volume_le hr
  have cert := (Rat.cast_le (K := ℝ)).2 (radius_certificate j)
  push_cast only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] at cert
  exact (mul_le_mul (rawVolume_le j) (pow_le_pow_left₀ hr.le hle _) (pow_nonneg hr.le _)
    ((rawVol_pos j).le.trans (rawVolume_le j))).trans cert

/-- Draw one throughout the requested interval. -/
theorem raw_tail_draw_one {r : ℝ} (hr : 0 < r) (hq : r ≤ 3329) :
    probability (fun A ↦ r < s 0 A) ≤ 4*3329^400 / (rawVolume 0 * r^506) :=
  raw_tail_through_radius 0 hr (by exact_mod_cast hq)

/-- The remaining open radii are strictly below the period and strictly above the
radius at which the requested probability majorant drops below one. -/
def RemainingRawTail : Prop := ∀ j, 0 < j → j < 53 → ∀ r : ℝ, 1690 ≤ r → r < 3329 →
  4*3329^400 < rawVolume j * r^(506+j) →
  probability (fun A ↦ r < s j A) ≤ 4*3329^400 / (rawVolume j * r^(506+j))

theorem raw_tail_of_remaining (h : RemainingRawTail) : RawTailEstimate := by
  intro j hj r hlo hq
  have hr : 0 < r := by linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj'
  · exact raw_tail_draw_one hr hq
  rcases lt_or_eq_of_le hq with hlt | rfl
  · by_cases hv : 4*3329^400 < rawVolume j * r^(506+j)
    · exact h j hj' hj r hlo hlt hv
    · exact raw_tail_of_volume_le hr (le_of_not_gt hv)
  · have he (A : Sample) : ¬ (3329 < s j A) :=
      not_lt_of_ge (path_data (Restart506.path (history A)) j (by omega)).2.1
    have hp := rawVol_pos j
    simp only [probability, designs, he, filter_false, card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Part 222, equation (3), follows from the sole remaining deterministic ball-count
inequality. The count includes all eligible lifts and removes their projective aliases. -/
def RemainingDirectionCount : Prop := ∀ j, 0 < j → j < 53 → ∀ r : ℝ, 1690 ≤ r → r < 3329 →
  4*3329^400 < rawVolume j * r^(506+j) →
  rawVolume j * r^(506+j) ≤ 4 * ((3329:ℝ)^400 + (rawDirections j r).card)

theorem raw_tail_of_direction_count (h : RemainingDirectionCount) : RawTailEstimate := by
  apply raw_tail_of_remaining
  intro j hj hn r hlo hq hv
  have hcount := h j hj hn r hlo hq hv
  have hr : 0 < r := by linarith
  have hvol := mul_pos (rawVol_pos j) (pow_pos hr (506+j))
  have hc : 0 < (3329:ℝ)^400 + (rawDirections j r).card := by positivity
  apply (winner_tail_le_of_directions (by omega : j < 406) hr.le).trans
  apply (div_le_div_iff₀ hc hvol).2
  calc
    _ ≤ (3329:ℝ)^400 * (4 * ((3329:ℝ)^400 + (rawDirections j r).card)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by rw [← mul_assoc, mul_comm (3329^400:ℝ) 4]

theorem crossing_of_remaining_raw_tail (h : RemainingRawTail) (hc : Ceiling 53) :
    probability crosses < 2.4681 / (10:ℝ)^11 :=
  crossing_of_raw_tail (raw_tail_of_remaining h) hc

theorem crossing_of_direction_count (h : RemainingDirectionCount) (hc : Ceiling 53) :
    probability crosses < 2.4681 / (10:ℝ)^11 :=
  crossing_of_raw_tail (raw_tail_of_direction_count h) hc

end SigabaNeo.Wall1.LongWinner.FourthMoment

#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.raw_tail_through_radius
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.raw_tail_draw_one
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_remaining_raw_tail
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_direction_count
