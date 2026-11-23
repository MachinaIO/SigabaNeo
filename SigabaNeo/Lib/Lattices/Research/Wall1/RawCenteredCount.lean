import SigabaNeo.Lib.Lattices.Research.Wall1.RawBallCount
import SigabaNeo.Lib.Lattices.Research.Wall1.RawDirectionMultiplicity

/-! A uniform lower bound for centered lifts with the newest coordinate nonzero. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset Real MeasureTheory Metric
open scoped Classical
set_option exponentiation.threshold 1000

private def volumeQ (p : ℚ) (n : ℕ) : ℚ :=
  if n % 2 = 0 then p^(n/2) / (n/2).factorial
  else p^(n/2) * 2^(n/2+1) / n.doubleFactorial

private lemma volume_bounds (n : ℕ) (hn : 0 < n) :
    (volumeQ 3.14159 n : ℝ) ≤ unitVolume n ∧ unitVolume n ≤ (volumeQ 3.14160 n : ℝ) := by
  let k := n/2
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hlo : (3.14159:ℝ) ≤ π := by linarith [pi_gt_d6]
  have hhi : π ≤ (3.14160:ℝ) := by linarith [pi_lt_d6]
  unfold volumeQ unitVolume
  split_ifs with he
  · have h : n = 2*k := by dsimp [k]; omega
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (dim.trans h)]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k / (k.factorial:ℝ))]
    push_cast
    constructor <;> gcongr
  · have h : n = 2*k+1 := by dsimp [k]; omega
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd (dim.trans h),dim]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ π^k * 2^(k+1) / (n.doubleFactorial:ℝ))]
    push_cast
    constructor <;> gcongr

set_option maxRecDepth 10000 in
private theorem certificates : ∀ i : Fin 52,
    volumeQ 3.14160 (506+i.val) ≤ 10 * volumeQ 3.14159 (507+i.val) ∧
    (17/100 : ℚ)^(507+i.val) ≤ volumeQ 3.14159 (507+i.val) := by decide +kernel

theorem dim_bounds (n : ℕ) (hlo : 506 ≤ n) (hhi : n ≤ 557) :
    unitVolume n ≤ 10 * unitVolume (n+1) ∧ (17/100:ℝ)^(n+1) ≤ unitVolume (n+1) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 52, n = 506+i.val := ⟨⟨n-506,by omega⟩,by simp; omega⟩
  obtain ⟨a,b⟩ := certificates i
  have va := (volume_bounds (506+i.val) (by omega)).2
  have vb := (volume_bounds (507+i.val) (by omega)).1
  rw [show 506+i.val+1 = 507+i.val by omega]
  constructor
  · refine va.trans ((le_trans ?_ (mul_le_mul_of_nonneg_left vb (by norm_num : (0:ℝ) ≤ 10))))
    exact_mod_cast a
  · apply le_trans _ vb
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 b

def allowed (p : Fin n) (r : ℝ) : Finset (Fin n → ℤ) :=
  (closedLifts n r).filter fun z ↦ (∀ i, |z i| ≤ 1664) ∧ z p ≠ 0

/-- More than one half of the continuous volume is available before modular scalar collisions. -/
theorem allowed_lower (n : ℕ) (hn : 506 ≤ n) (hn' : n ≤ 557) (p : Fin (n+1))
    {r : ℝ} (hr : 1690 ≤ r) (hq : r ≤ 3329) :
    (506/1000:ℝ) * (r^(n+1) * unitVolume (n+1)) ≤ (allowed p r).card := by
  let N := n+1
  let V := unitVolume N
  let W := r^N * V
  let T := closedLifts N r
  let Z := T.filter fun z ↦ z p = 0
  let C (k : Fin N × Bool) := T.filter fun z ↦ 1664 ≤ (if k.2 then z k.1 else -z k.1)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have rp : 0 ≤ r := by linarith
  have rn : 0 ≤ r^n := pow_nonneg rp _
  have hw : 0 ≤ W := mul_nonneg (pow_nonneg rp _) hV
  have hi : N ≤ 558 := by dsimp [N]; omega
  have lower : 52/100 * W ≤ T.card := by
    have l := closedLifts_lower hi hr
    have hp : (8443/8450:ℝ)^558 ≤ (8443/8450:ℝ)^N := pow_le_pow_of_le_one
      (by norm_num) (by norm_num) hi
    have hmul : (8443/8450:ℝ)^N * r^N ≤ (r-7/5)^N := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity) (by linarith)
    have cert : (52/100:ℝ) ≤ (8443/8450:ℝ)^558 * (119/144) := by norm_num
    change 52/100 * (r^N * V) ≤ _
    change (r-7/5)^N * V * (119/144) ≤ (T.card:ℝ) at l
    refine le_trans ?_ l
    calc
      _ ≤ (((8443/8450:ℝ)^N * (119/144)) * (r^N * V)) := by
        gcongr
        exact cert.trans (mul_le_mul_of_nonneg_right hp (by norm_num))
      _ = ((8443/8450:ℝ)^N * r^N) * V * (119/144) := by ring
      _ ≤ _ := by gcongr
  have zero : (Z.card:ℝ) ≤ 13/1000*W := by
    apply (zero_slice_upper p rp).trans
    have ns : (n:ℝ) ≤ 557 := by exact_mod_cast hn'
    have rad : sqrt (r^2+n/4) ≤ (40001/40000:ℝ)*r := by
      apply (sqrt_le_left (by positivity)).2
      nlinarith [sq_nonneg (r-1690)]
    have pw := pow_le_pow_left₀ (sqrt_nonneg _) rad n
    rw [mul_pow] at pw
    have c : (40001/40000:ℝ)^n ≤ (40001/40000:ℝ)^557 :=
      pow_le_pow_right₀ (by norm_num) hn'
    have v := (dim_bounds n hn hn').1
    change _ ≤ 13/1000*(r^(n+1)*V)
    calc
      _ ≤ 2 * ((40001/40000:ℝ)^557 * r^n) * (10*V) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (pw.trans
          (mul_le_mul_of_nonneg_right c rn)) (by norm_num)) v ENNReal.toReal_nonneg (by positivity)
      _ = (20*(40001/40000:ℝ)^557) * (r^n*V) := by ring
      _ ≤ ((13/1000)*r)*(r^n*V) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg rn hV)
        linarith only [hr, show 20*(40001/40000:ℝ)^557 ≤ 13/1000*1690 by norm_num]
      _ = _ := by rw [pow_succ]; ring
  have cap (k : Fin N × Bool) : ((C k).card:ℝ) ≤ 2*(9/10:ℝ)^507*W := by
    apply (cap_upper k.1 k.2 hr).trans
    have ns : (N:ℝ) ≤ 558 := by exact_mod_cast hi
    have rad : sqrt (r^2-1664^2+N/4) ≤ (9/10:ℝ)*r := by
      apply (sqrt_le_left (by positivity)).2
      nlinarith [mul_self_le_mul_self rp hq]
    have pw := pow_le_pow_left₀ (sqrt_nonneg _) rad N
    rw [mul_pow] at pw
    have c : (9/10:ℝ)^N ≤ (9/10:ℝ)^507 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by dsimp [N]; omega)
    change _ ≤ 2*(9/10:ℝ)^507*(r^N*V)
    calc
      _ ≤ 2*((9/10:ℝ)^507*r^N)*V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pw.trans
          (mul_le_mul_of_nonneg_right c (pow_nonneg rp _))) (by norm_num)) hV
      _ = _ := by ring
  have sub : T ⊆ (allowed p r ∪ Z) ∪ univ.biUnion C := by
    intro z hz
    by_cases h : z p = 0
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hz,h⟩))
    by_cases hc : ∀ i, |z i| ≤ 1664
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hz,hc,h⟩))
    push Not at hc
    obtain ⟨i,hi'⟩ := hc
    apply mem_union_right
    by_cases hp : 0 ≤ z i
    · exact mem_biUnion.mpr ⟨(i,true),mem_univ _,mem_filter.mpr ⟨hz,by
        simpa [abs_of_nonneg hp] using hi'.le⟩⟩
    · exact mem_biUnion.mpr ⟨(i,false),mem_univ _,mem_filter.mpr ⟨hz,by
        simpa [abs_of_neg (lt_of_not_ge hp)] using hi'.le⟩⟩
  have count : T.card ≤ (allowed p r).card + Z.card + ∑ k, (C k).card :=
    (card_le_card sub).trans ((card_union_le ..).trans
      (Nat.add_le_add (card_union_le ..) card_biUnion_le))
  have count' : (T.card:ℝ) ≤ (allowed p r).card + Z.card + ∑ k, ((C k).card:ℝ) := by
    exact_mod_cast count
  have loss := sum_le_sum (s := univ) fun k _ ↦ cap k
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at loss
  have tiny : (N:ℝ)*2*(2*(9/10:ℝ)^507*W) ≤ (1/1000)*W := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hw
    have h : (N:ℝ) ≤ 558 := by exact_mod_cast hi
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by norm_num)) (by positivity)).trans
      (by norm_num)
  change 506/1000 * W ≤ _
  linarith only [lower,zero,count',loss.trans tiny]

end SigabaNeo.Wall1.RawBallRounding
