import SigabaNeo.Lib.Lattices.Research.Wall1.RawDirectionCountBounds
import SigabaNeo.Lib.Lattices.Research.Wall1.RawScalarWeights

/-! Part 222's deterministic projective count and the resulting crossing theorem.

Product interpolation in the radius-`r - 7/5` ball gives a lower bound for integer lifts.
After deleting coordinate caps and the zero newest-coordinate slice, `eligible_lower` retains
at least 0.506 times the ball volume. For each nontrivial field scalar the coordinate weight
depends on the combined squared norm of the two centered lifts. Its product bounds their
ordered collisions via `tilted_pairs`. The nine radius bins below put the total collision
charge below 0.001 times the ball volume. Each remaining direction has at most two signs. -/
noncomputable section
namespace SigabaNeo.Wall1.LongWinner.FourthMoment
open Finset RawBallRounding RawCount RawScalarWeights
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private def lowerRadius (i : Fin 9) := 1690 + 200*i.val
private def upperRadius (i : Fin 9) := min 3329 (lowerRadius i + 200)
private def exponentBound (i : Fin 9) := (2*(upperRadius i)^2+3071)/3072

private lemma radius_bin {r : ℝ} (hr : 1690 ≤ r) (hq : r ≤ 3329) :
    ∃ i, (lowerRadius i : ℝ) ≤ r ∧ 2*r^2 ≤ (exponentBound i : ℝ)*3072 := by
  let t := ⌊r⌋₊
  have hfloor : (t:ℝ) ≤ r := Nat.floor_le (by linarith)
  have hceil : r < (t:ℝ)+1 := Nat.lt_floor_add_one r
  have hlo : 1690 ≤ t := (Nat.le_floor_iff (by linarith : 0 ≤ r)).2 (by exact_mod_cast hr)
  have hhi : t ≤ 3329 := by exact_mod_cast hfloor.trans hq
  let i : Fin 9 := ⟨(t-1690)/200, by omega⟩
  have lo : lowerRadius i ≤ t := by dsimp [i,lowerRadius]; omega
  have hi : t+1 ≤ lowerRadius i + 200 := by dsimp [i,lowerRadius]; omega
  have ub : r ≤ upperRadius i := by
    unfold upperRadius
    push_cast
    apply le_min hq
    exact hceil.le.trans (by exact_mod_cast hi)
  have hnum : 2*upperRadius i^2 ≤ exponentBound i * 3072 := by unfold exponentBound; omega
  exact ⟨i,(Nat.cast_le.mpr lo).trans hfloor,(mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) ub 2) (by norm_num : (0:ℝ) ≤ 2)).trans (by exact_mod_cast hnum)⟩

-- Nine rational comparisons, each at the minimum dimension. Raising the radius-to-weight
-- ratio to any larger dimension only improves them.
set_option maxRecDepth 10000 in
private lemma alias_certificate : ∀ i : Fin 9,
    1000 * 3329 * (190:ℚ)^507 ≤ (15/16 : ℚ)^(exponentBound i) *
      ((17/100 : ℚ) * lowerRadius i)^507 := by decide +kernel

private lemma alias_loss {j : ℕ} (hj : 0 < j) (hj' : j < 53) {r : ℝ}
    (hr : 1690 ≤ r) (hq : r ≤ 3329) :
    (∑ a ∈ scalars, ((scalarPairs (eligible j r) a).card : ℝ)) ≤
      (1/1000) * (rawVolume j * r^(506+j)) := by
  obtain ⟨i,hlo,hM⟩ := radius_bin hr hq
  let M := exponentBound i
  let b := (15/16:ℝ)^M
  let N := 506+j
  let u : ℝ := (17/100)*lowerRadius i
  have bp : 0 < b := by dsimp [b]; positivity
  have hu : (190:ℝ) ≤ u := by dsimp [u,lowerRadius]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) i.val]
  have step : 1000*3329*(190:ℝ)^507 ≤ b * u^507 := by
    have cert := (Rat.cast_le (K := ℝ)).2 (alias_certificate i)
    push_cast only [Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast] at cert
    exact cert
  have dim : 507 + (j-1) = N := by dsimp [N]; omega
  have grow : 1000*3329*(190:ℝ)^N ≤ b*u^N := by
    rw [← dim,pow_add,pow_add,← mul_assoc,← mul_assoc]
    exact mul_le_mul step (pow_le_pow_left₀ (by norm_num) hu _) (by positivity) (by positivity)
  have vlow : (17/100:ℝ)^N ≤ rawVolume j := by
    have hh := (dim_bounds (505+j) (by omega) (by omega)).2
    change (17/100:ℝ)^N ≤ unitVolume N
    simpa only [show 505+j+1 = N by dsimp [N]; omega] using hh
  have uv : u^N ≤ rawVolume j * r^N := by
    dsimp [u]
    rw [mul_pow]
    exact mul_le_mul vlow (pow_le_pow_left₀ (by positivity) hlo _) (by positivity)
      (le_trans (by positivity) vlow)
  have hb := sum_le_sum (s := scalars) (fun a ha ↦ tilted_pairs (j := j) (by linarith : 0 ≤ r)
    hM a ha smallRow_le)
  rw [← sum_mul,sum_const,nsmul_eq_mul] at hb
  have hs : (scalars.card:ℝ) ≤ 3329 := by
    exact_mod_cast (card_le_univ scalars).trans_eq (ZMod.card _)
  have sumB := hb.trans (mul_le_mul_of_nonneg_right hs (by positivity))
  change (∑ a ∈ scalars, ((scalarPairs (eligible j r) a).card:ℝ)) * b ≤ 3329 * 190^N at sumB
  change _ ≤ 1/1000*(rawVolume j*r^N)
  apply (mul_le_mul_iff_left₀ bp).mp
  have g := grow.trans (mul_le_mul_of_nonneg_left uv bp.le)
  linarith only [sumB,g]

/-- At every nontrivial early draw the normalized raw directions alone cover a quarter
of the Euclidean ball volume throughout the radius interval. -/
theorem rawVolume_le_four_directions {j : ℕ} (hj : 0 < j) (hj' : j < 53) {r : ℝ}
    (hr : 1690 ≤ r) (hq : r ≤ 3329) :
    rawVolume j * r^(506+j) ≤ 4 * (rawDirections j r).card := by
  have count := eligible_card_le j r
  have count' : ((eligible j r).card:ℝ) ≤ 2*(rawDirections j r).card +
      ∑ a ∈ scalars, ((scalarPairs (eligible j r) a).card:ℝ) := by exact_mod_cast count
  have vol : 0 ≤ rawVolume j * r^(506+j) := mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by linarith) _)
  linarith only [eligible_lower hj hj' hr hq,alias_loss hj hj' hr hq,count',vol]

theorem remainingDirectionCount : RemainingDirectionCount := by
  intro j hj hn r hr hq _
  exact (rawVolume_le_four_directions hj hn hr hq.le).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by norm_num))

/-- The conditional fourth-moment ceiling on draws 54–405 suffices on the original sample. -/
theorem crossing_of_suffix_ceiling (hc : Ceiling 53) :
    DualExit.probability crosses < 2.4681 / (10:ℝ)^11 :=
  crossing_of_direction_count remainingDirectionCount hc

end SigabaNeo.Wall1.LongWinner.FourthMoment
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.rawVolume_le_four_directions
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.remainingDirectionCount
#print axioms SigabaNeo.Wall1.LongWinner.FourthMoment.crossing_of_suffix_ceiling
