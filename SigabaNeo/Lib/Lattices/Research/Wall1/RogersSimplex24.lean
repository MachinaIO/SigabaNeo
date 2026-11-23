import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixFamily

/-! Numeric part of the Rogers simplex bound in dimension 24.
For S = ∑ uᵢ² with uniform barycentric coordinates on the 23-simplex, the regular
simplex density is 25/4096 times the mean of (1+S)⁻¹². The analytic input below
is just the first six moments. The moment and geometric identities are derived
in the companion script. -/
noncomputable section
namespace SigabaNeo.Wall1.RogersSimplex24

open MeasureTheory Finset Real

/-- Raw moments of S up through degree six. -/
def simplexMoments : Fin 7 → ℚ := ![
    1, 2 / 25, 58 / 8775, 202 / 356265, 2006 / 39443625, 17551 / 3644590950, 1057327 /
    2168531615250]

private def lowerCoeffs : Fin 7 → ℚ := ![
    25798542415843419047854080, -307605566754015613902913536, 1940127916817939050228875264,
    -8104998005153116525493747712, 21853352059348795590432522240,
    -28936852382034267264572719104, 0]
private def upperCoeffs : Fin 7 → ℚ := ![
    25905599963261682486112888, -315313710168130581457547712, 2171372219241388076867900544,
    -11804906843928300951718152192, 55152531608325455426452162560,
    -188772914217122234477466992640, 319672123670175934425788547072]
private def denominator : ℚ := 25830003528617964966531072

private def eval (c : Fin 7 → ℚ) (x : ℝ) : ℝ := (∑ i, (c i : ℝ) * x^i.val) / denominator

private theorem pointwise {x : ℝ} (hx : 0 ≤ x) :
    eval lowerCoeffs x ≤ 1/(1+x)^12 ∧ 1/(1+x)^12 ≤ eval upperCoeffs x := by
  have hp : 0 < (1+x)^12 := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    have id : 1 - eval lowerCoeffs x*(1+x)^12 =
        (12*x-1)^6 * (10536263012308813 + 96536982000537000 * x + 413146492151217552 * x^2 +
          1082665242601173504 * x^3 + 1921410911196661248 * x^4 + 2416980846263832576 * x^5 +
          2193884091605606400 * x^6 + 1434448862002151424 * x^7 + 661202170006929408 * x^8 +
          204418000558227456 * x^9 + 38117258176757760 * x^10 + 3245460563165184 * x^11) /
          8650415919381337933 := by
      simp [eval, lowerCoeffs, denominator, Fin.sum_univ_succ]
      ring
    apply sub_nonneg.mp
    rw [id]
    positivity
  · apply (div_le_iff₀ hp).mpr
    have id : eval upperCoeffs x*(1+x)^12 - 1 =
        (12*x-1)^6 * (75596434643717519581816 + 996432685357269785697696 * x +
          5832149314385725734290160 * x^2 + 20319839340254733952769824 * x^3 +
          47256183733781750598161928 * x^4 + 77572511420014379250361152 * x^5 +
          92370271019086541930440992 * x^6 + 80506336204508010983334720 * x^7 +
          51019146871634430836692488 * x^8 + 22942271553039098164961056 * x^9 +
          6951980606565719081845488 * x^10 + 1274999675704919030324640 * x^11 +
          107057547418263438258808 * x^12) / 25830003528617964966531072 := by
      simp [eval, upperCoeffs, denominator, Fin.sum_univ_succ]
      ring
    apply sub_nonneg.mp
    rw [id]
    positivity

/-- Bounds for the simplex expectation, given integrability and its six rational moments. -/
theorem expectation_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → ℝ) (hm : Measurable S) (hn : ∀ w, 0 ≤ S w)
    (hi : ∀ i : Fin 7, Integrable (fun w ↦ S w ^ i.val) μ)
    (h : ∀ i : Fin 7, (∫ w, S w ^ i.val ∂μ) = (simplexMoments i : ℝ)) :
    0.402257 < (∫ w, 1/(1+S w)^12 ∂μ) ∧ (∫ w, 1/(1+S w)^12 ∂μ) < 0.402285 := by
  have hI (c : Fin 7 → ℚ) : Integrable (fun w ↦ eval c (S w)) μ :=
    (integrable_finsetSum _ (fun i _ ↦ (hi i).const_mul (c i : ℝ))).div_const _
  have hp (c : Fin 7 → ℚ) : (∫ w, eval c (S w) ∂μ) =
      (((∑ i, c i * simplexMoments i) / denominator : ℚ) : ℝ) := by
    simp only [eval, integral_div, integral_finsetSum _ (fun i _ ↦ (hi i).const_mul (c i : ℝ)),
      integral_const_mul, h, Rat.cast_div, Rat.cast_sum, Rat.cast_mul]
  have hmid : Integrable (fun w ↦ 1/(1+S w)^12) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_const.div ((measurable_const.add hm).pow_const 12)).aestronglyMeasurable
    filter_upwards with w
    change ‖1/(1+S w)^12‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [hn w])]
    rw [div_le_iff₀ (by positivity [hn w]), one_mul]
    exact one_le_pow₀ (by linarith [hn w])
  have low := integral_mono (hI lowerCoeffs) hmid (fun w ↦ (pointwise (hn w)).1)
  have upp := integral_mono hmid (hI upperCoeffs) (fun w ↦ (pointwise (hn w)).2)
  rw [hp] at low upp
  have l : (0.402257 : ℚ) < (∑ i, lowerCoeffs i * simplexMoments i) / denominator :=
    by decide +kernel
  have u : (∑ i, upperCoeffs i * simplexMoments i) / denominator < (0.402285 : ℚ) :=
    by decide +kernel
  exact ⟨lt_of_lt_of_le (by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).2 l) low,
    lt_of_le_of_lt upp (by simpa only [Rat.cast_ofScientific] using (Rat.cast_lt (K := ℝ)).2 u)⟩

/-- Compare the regular-simplex volume fraction expressed in Hermite units. -/
theorem hermite_units {E g : ℝ} (hE : 0.402257 < E ∧ E < 0.402285)
    (hg : 0 ≤ g) (convert : (π*g)^12 = 25 * Nat.factorial 12 * E * 4096) :
    4.0811 < g ∧ g < 4.08114 := by
  constructor
  · by_contra! hh
    have h := pow_le_pow_left₀ (mul_nonneg pi_pos.le hg)
      (mul_le_mul Real.pi_lt_d20.le hh hg (by norm_num : (0:ℝ) ≤ 3.14159265358979323847)) 12
    norm_num at h convert
    linarith [hE.1]
  · by_contra! hh
    have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (3.14159265358979323846:ℝ)*4.08114)
      (mul_le_mul Real.pi_gt_d20.le hh (by norm_num) pi_pos.le) 12
    norm_num at h convert
    linarith [hE.2]

open ControlledPlane TerminalProjection Metric

/-- Geometric input of the Rogers route, in volume-density units: the packing ball
of each lattice occupies at most the proposed fraction of a fundamental cell. -/
def PackingBound (density : ℝ) : Prop :=
  ∀ (L : Submodule ℤ (CoordSpace 24)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : CoordSpace 24), DecoupledDecoder.IsShortest L v →
      volume.real (ball (0 : CoordSpace 24) (‖v‖/2)) ≤ density * ZLattice.covolume L

/-- It suffices to prove Rogers' simplex comparison with the enclosed expectation. -/
theorem intrinsic_of_simplex_comparison {E : ℝ} (upper : E < 0.402285)
    (packing : PackingBound (25*E/4096)) : IntrinsicHermite 24 4.08114 := by
  intro L _ _
  have hn : L ≠ ⊥ := by
    intro he
    have hs := IsZLattice.span_top (K := ℝ) (L := L)
    simp [he] at hs
  obtain ⟨v,hv,_⟩ := exists_orderedShortest L (fun _ ↦ (0:ℕ)) hn
  refine ⟨⟨v,hv.1⟩, fun h ↦ hv.2.1 (congrArg Subtype.val h), ?_⟩
  let D := ZLattice.covolume L
  have hD : 0 < D := ZLattice.covolume_pos L volume
  let root := D^((12:ℝ)⁻¹)
  have hroot : root^12 = D := Real.rpow_inv_natCast_pow hD.le (by decide)
  change ‖v‖^2 ≤ 4.08114 * D^(2/(24:ℝ))
  rw [show (2/(24:ℝ)) = (12:ℝ)⁻¹ by norm_num]
  have h := packing L v hv
  have dim : Module.finrank ℝ (CoordSpace 24) = 2*12 := by simp [CoordSpace]
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even dim,dim, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at h
  change (‖v‖/2)^24 * (π^12 / (Nat.factorial 12:ℝ)) ≤ 25*E/4096*D at h
  have hc : 25*(Nat.factorial 12:ℝ)*E*4096 ≤ (π*4.08114)^12 := by
    apply le_trans _ (pow_le_pow_left₀ (by norm_num : 0 ≤ (3.14159265358979323846:ℝ)*4.08114)
      (mul_le_mul_of_nonneg_right pi_gt_d20.le (by norm_num)) 12)
    norm_num
    linarith
  have hh : (π*‖v‖^2)^12 ≤ (π*(4.08114*root))^12 := by
    rw [← mul_assoc,mul_pow (π*4.08114),hroot]
    apply le_trans _ (mul_le_mul_of_nonneg_right hc hD.le)
    norm_num [div_pow] at h ⊢
    linarith [h]
  exact (le_of_mul_le_mul_left (le_of_pow_le_pow_left₀ (by decide : 12 ≠ 0)
    (by positivity [Real.rpow_nonneg hD.le ((12:ℝ)⁻¹)] : 0 ≤ π*(4.08114*root)) hh) pi_pos)

end SigabaNeo.Wall1.RogersSimplex24

#print axioms SigabaNeo.Wall1.RogersSimplex24.expectation_bounds
#print axioms SigabaNeo.Wall1.RogersSimplex24.hermite_units
#print axioms SigabaNeo.Wall1.RogersSimplex24.intrinsic_of_simplex_comparison
