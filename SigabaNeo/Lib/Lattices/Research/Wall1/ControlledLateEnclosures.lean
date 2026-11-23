import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledPlaneCharges

/-! Finite enclosures for the late sums. Use twelve successive determinant decrements
at each endpoint and charge every earlier draw at the twelfth discount. -/
noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.LateEnclosures
open Real Finset TerminalProjection TerminalInterval DualExit

private def floors : Fin 26 → ℚ := ![
    891.7863650383000, 895.5708526060746, 899.3628342086369,
    903.1623246856597, 906.9693389062013, 910.7838917687638,
    914.6059982013512, 918.4356731615279, 922.2729316364772,
    926.1177886430601, 929.9702592278738, 933.8303584673109,
    937.6981014676182, 941.5735033649558, 945.4565793254564,
    949.3473445452848, 953.2458142506970, 957.1520036981001,
    961.0659281741119, 964.9876029956208, 968.9170435098455,
    972.8542650943954, 976.7992831573306, 980.7521131372221,
    984.7127705032124, 988.6812707550759]

private def lower (j : ℕ) := floors ⟨min j 25, by omega⟩

private theorem floor_le (i : ℕ) (hi : i ≤ 406) : (lower (406-i) : ℝ) ≤ terminalLogFloor i := by
  have cap : (4.02916939402331 : ℝ) ≤ log 56.2142 := by
    apply (le_log_iff_exp_le (by norm_num)).2
    have h := exp_upper (4.02916939402331/8) 1.654743768613785
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rw [show (4.02916939402331 : ℝ) = (8:ℕ)*((4.02916939402331/8:ℚ):ℝ) by norm_num,
      exp_nat_mul]
    exact (pow_le_pow_left₀ (exp_pos _).le h 8).trans (by norm_num)
  have mod : (4:ℝ) ≤ log 3329 := (le_trans (by norm_num) cap).trans
    (log_le_log (by norm_num) (by norm_num))
  have next : ∀ k : Fin 26, lower (k.val+1) ≤ lower k + 4 ∧
      lower (k.val+1)*505 ≤ (lower k + 4.02916939402331/2)*506 := by decide +kernel
  refine Nat.decreasingInduction' (motive := fun k ↦ (lower (406-k) : ℝ) ≤ terminalLogFloor k)
    ?_ hi ?_
  · intro k hk _ ih
    let j := 406-(k+1)
    have eq : lower (406-k) = lower ((min j 25)+1) := by
      unfold lower; congr 2; dsimp [j]; omega
    have eq' : lower (406-(k+1)) = lower (min j 25) := by simp [lower,j]
    rw [eq', terminalLogFloor] at ih
    rw [eq]
    obtain ⟨m,h⟩ := next ⟨min j 25, by omega⟩
    have h1 := (Rat.cast_le (K := ℝ)).mpr m
    have h2 := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h1 h2
    change (lower (min j 25 + 1) : ℝ) ≤ _ at h1
    change (lower (min j 25 + 1) : ℝ)*505 ≤ _ at h2
    rcases le_max_iff.mp ih with ih | ih <;> linarith
  · exact le_trans (by norm_num [lower,floors]) terminalLogFloor_406

private def discount394 : Fin 13 → ℚ := ![
    1.000000000000000000000000000000, 0.020587401653289914000071436875, 0.000420594580337541344064029614,
    0.000008526676598026337613013260, 0.000000171531256527098414278870, 0.000000003424108095711287615960,
    0.000000000067824364260165330263, 0.000000000001333065225075468011, 0.000000000000025997871400827795,
    0.000000000000000503081347420623, 0.000000000000000009659306952727, 0.000000000000000000184015467140,
    0.000000000000000000003478216154]
private def discount406 : Fin 13 → ℚ := ![
    1.000000000000000000000000000000, 0.022550870682933056648091725777, 0.000504737493048702541272844609,
    0.000011212444279088899711401719, 0.000000247207156215713548145340, 0.000000005409302959977969678480,
    0.000000000117472064980926338738, 0.000000000002531829301464060853, 0.000000000000054154461303262300,
    0.000000000000001149549093768337, 0.000000000000000024216296428348, 0.000000000000000000506253783176,
    0.000000000000000000010502740195]
private def idx (j : ℕ) : Fin 13 := ⟨min j 12, by omega⟩

/-- Check an endpoint and its twelve relative discounts once for a whole horizon. -/
private theorem charge_sum {N b : ℕ} {r f : ℝ} (U F a p : ℚ) (ws : Fin 13 → ℚ)
    (hN : N ≤ 405) (hf : 0 < f) (hF : f ≤ F)
    (hz : 3.3 ≤ r*√(2*π/b)) (hU : r*√(2*π/b) ≤ U)
    (ha : 0 < a) (hbase : 0 ≤ (lower (406-N)-b/2)/1024)
    (base : a ≤ taylor ((lower (406-N)-b/2)/1024) 20)
    (discount : ∀ j : Fin 26,
      let x := (lower j - lower (406-N))/64
      406-N ≤ j.val → 0 ≤ x ∧ 0 < ws (idx (j.val-(406-N))) ∧
        1 ≤ ws (idx (j.val-(406-N))) * (taylor x 20)^64)
    (hclip : 406-N+12 ≤ 25)
    (num : U^b * (1.00000000000001:ℚ)^(b-1) * F *
        (∑ i : Fin (N+1), ws (idx (N-i.val))) / (2*a^1024) < p) :
    (∑ i : Fin (N+1), ballCharge b r (terminalLogFloor i.val-log f)) < (p:ℝ) := by
  let z := r*√(2*π/b)
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have harg : 34 ≤ π*z^2 := by
    have hπ := Real.pi_gt_d2
    nlinarith [sq_nonneg (z-3.3), mul_nonneg (sub_nonneg.mpr hπ.le) (sq_nonneg z),
      show 3.3 ≤ z from hz]
  have h34 : (5*10^14 : ℝ) ≤ exp 34 := by
    have h := exp_lower (34/64) 1.7 (by decide +kernel) (by decide +kernel)
    rw [show (34:ℝ) = (64:ℕ)*((34/64:ℚ):ℝ) by norm_num, exp_nat_mul]
    apply le_trans _ (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (1.7:ℚ)) h 64)
    norm_num
  have he : exp (-π*z^2) ≤ 1/(5*10^14) := by
    rw [neg_mul,exp_neg,inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (h34.trans (exp_le_exp.mpr harg))
  have he3 : exp (-3*π*z^2) ≤ 1/(5*10^14) := (exp_le_exp.mpr (by linarith :
    -3*π*z^2 ≤ -π*z^2)).trans he
  have hd : 0 < 1-exp (-3*π*z^2) := by linarith
  have th0 : 0 ≤ terminalTheta z := by unfold terminalTheta; positivity
  have th : terminalTheta z ≤ 1.00000000000001 := by
    unfold terminalTheta
    apply (le_sub_iff_add_le').mp
    apply (div_le_iff₀ hd).mpr
    linarith
  let L := lower (406-N)
  have hp := exp_lower _ _ hbase base
  have hpow := pow_le_pow_left₀ (by exact_mod_cast ha.le) hp 1024
  have base' : (a:ℝ)^1024 ≤ exp ((L:ℝ)-b/2) := by
    rw [show (L:ℝ)-b/2 = (1024:ℕ)*(((L-b/2)/1024:ℚ):ℝ) by push_cast; ring,exp_nat_mul]
    exact hpow
  have term (i : Fin (N+1)) :
      ballCharge b r (terminalLogFloor i.val-log f) ≤
        (U:ℝ)^b * (1.00000000000001:ℝ)^(b-1)*F / (2*(a:ℝ)^1024) * ws (idx (N-i.val)) := by
    let j : Fin 26 := ⟨min (406-i.val) 25, by omega⟩
    obtain ⟨hx, hw, ht⟩ := discount j (by dsimp [j]; omega)
    have eq : idx (j.val-(406-N)) = idx (N-i.val) := by
      ext; dsimp [j,idx]; omega
    rw [eq] at hw ht
    have hl := floor_le i.val (by omega)
    have hj : lower (406-i.val) = lower j := by simp [j,lower]
    rw [hj] at hl
    let x := (lower j - L)/64
    have ht0 : 0 ≤ taylor x 20 := sum_nonneg fun k _ ↦ div_nonneg (pow_nonneg hx _) (by positivity)
    have ex := pow_le_pow_left₀ (by exact_mod_cast ht0) (exp_lower _ _ hx le_rfl) 64
    have ex' : (taylor x 20 : ℝ)^64 ≤ exp (terminalLogFloor i.val-(L:ℝ)) := by
      apply le_trans _ (exp_le_exp.mpr (sub_le_sub_right hl (L:ℝ)))
      rw [show (lower j : ℝ)-(L:ℝ) = (64:ℕ)*(x:ℝ) by dsimp [x]; push_cast; ring,exp_nat_mul]
      exact ex
    have hw' : (0:ℝ) < ws (idx (N-i.val)) := by exact_mod_cast hw
    have ht' := (Rat.cast_le (K := ℝ)).mpr ht
    push_cast at ht'
    have discount' : 1 ≤ (ws (idx (N-i.val)):ℝ) * exp (terminalLogFloor i.val-(L:ℝ)) :=
      le_trans ht' (mul_le_mul_of_nonneg_left ex' hw'.le)
    have br : exp ((b:ℝ)/2-terminalLogFloor i.val) ≤ ws (idx (N-i.val))/(a:ℝ)^1024 := by
      apply (le_div_iff₀ (pow_pos (by exact_mod_cast ha) _)).mpr
      apply (mul_le_mul_of_nonneg_left base' (exp_pos _).le).trans
      rw [← exp_add, show (b:ℝ)/2-terminalLogFloor i.val+((L:ℝ)-b/2) =
        -(terminalLogFloor i.val-(L:ℝ)) by ring, exp_neg, inv_eq_one_div]
      exact (div_le_iff₀ (exp_pos _)).mpr discount'
    unfold ballCharge
    rw [show (b:ℝ)/2-(terminalLogFloor i.val-log f) =
      ((b:ℝ)/2-terminalLogFloor i.val)+log f by ring,exp_add,exp_log hf]
    change exp _ * f / 2 * z^b * terminalTheta z^(b-1) ≤ _
    calc
      _ ≤ (ws (idx (N-i.val))/(a:ℝ)^1024) * (F:ℝ)/2 * (U:ℝ)^b *
            (1.00000000000001:ℝ)^(b-1) := by
              gcongr <;> positivity [hw', hf.le.trans hF, hz0.trans hU]
      _ = _ := by ring
  refine (sum_le_sum (fun i _ ↦ term i)).trans_lt ?_
  rw [← mul_sum]
  have hh := (Rat.cast_lt (K := ℝ)).mpr num
  push_cast at hh
  convert hh using 1
  ring

private theorem widths :
    3.3 ≤ winnerRadius * √(2*π/506) ∧ winnerRadius * √(2*π/506) ≤ 3.70237331252365 ∧
    3.3 ≤ 30 * √(2*π/506) ∧ 30 * √(2*π/506) ≤ 3.34299656602247 ∧
    3.3 ≤ planeRadius * √(2*π/505) ∧ planeRadius * √(2*π/505) ≤ 3.34878265361178 ∧
    0 < winnerRadius ∧ winnerRadius ≤ 33.22504142080618 := by
  have s2 : √(2:ℝ) ≤ 1.414213562373095049 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  have s3 : 1.732050807568877293 ≤ √(3:ℝ) := le_sqrt_of_sq_le (by norm_num)
  have p3 : 0 < √(3:ℝ) := by positivity
  have radius : 33 ≤ winnerRadius ∧ winnerRadius ≤ 33.225041420806169 := by
    unfold winnerRadius areaCut
    rw [mul_div_assoc']
    constructor
    · apply le_sqrt_of_sq_le
      apply (le_div_iff₀ p3).mpr
      have a : (1.414:ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
      have b : √(3:ℝ) ≤ 1.733 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
      linarith
    · apply (sqrt_le_left (by norm_num)).mpr
      apply (div_le_iff₀ p3).mpr
      linarith
  have plane : 30 ≤ planeRadius ∧ planeRadius ≤ 30.022213997860540 := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    constructor
    · apply le_sqrt_of_sq_le; norm_num
    · apply (sqrt_le_left (by norm_num)).mpr; norm_num
  have s506 : 0.11 ≤ √(2*π/506) ∧ √(2*π/506) ≤ 0.111433218867415533 := by
    exact ⟨le_sqrt_of_sq_le (by linarith [Real.pi_gt_d2]),
      (sqrt_le_left (by norm_num)).mpr (by linarith [Real.pi_lt_d20])⟩
  have s505 : 0.11 ≤ √(2*π/505) ∧ √(2*π/505) ≤ 0.111543494222325284 := by
    exact ⟨le_sqrt_of_sq_le (by linarith [Real.pi_gt_d2]),
      (sqrt_le_left (by norm_num)).mpr (by linarith [Real.pi_lt_d20])⟩
  have pair {a b l u L U : ℝ} (h : l ≤ a ∧ a ≤ u) (h' : L ≤ b ∧ b ≤ U)
      (hl : 0 ≤ l) (hL : 0 ≤ L) : l*L ≤ a*b ∧ a*b ≤ u*U :=
    ⟨mul_le_mul h.1 h'.1 hL (hl.trans h.1),
      mul_le_mul h.2 h'.2 (hL.trans h'.1) (hl.trans (h.1.trans h.2))⟩
  obtain ⟨w1,w2⟩ := pair radius s506 (by norm_num) (by norm_num)
  obtain ⟨p1,p2⟩ := pair plane s505 (by norm_num) (by norm_num)
  obtain ⟨t1,t2⟩ := s506
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith [radius.1], by linarith [radius.2]⟩

theorem positive394_sum :
    (∑ i : Fin 394, ballCharge 506 winnerRadius (terminalLogFloor i.val)) <
      2.066876811/(10:ℝ)^12 := by
  have h := charge_sum (N := 393) (b := 506) (r := winnerRadius) (f := 1)
    3.70237331252365 1 1.9590018079960913 (2.066876811/10^12) discount394
    (by decide) (by norm_num) (by norm_num) (widths.1) (by simpa using widths.2.1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [log_one,sub_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_ofScientific] using h

theorem positive30_sum :
    (∑ i : Fin 406, ballCharge 506 30 (terminalLogFloor i.val)) <
      7.189180962/(10:ℝ)^15 := by
  have h := charge_sum (N := 405) (b := 506) (r := 30) (f := 1)
    3.34299656602247 1 1.8729422652643405 (7.189180962/10^15) discount406
    (by decide) (by norm_num) (by norm_num) (widths.2.2.1) (by simpa using widths.2.2.2.1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [log_one,sub_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_ofScientific] using h

theorem horizontal406_sum :
    (∑ i : Fin 406, ballCharge 505 planeRadius (terminalLogFloor i.val - log winnerRadius)) <
      1.037844738/(10:ℝ)^13 := by
  have h := charge_sum (N := 405) (b := 505) (r := planeRadius) (f := winnerRadius)
    3.34878265361178 33.22504142080618 1.8738570111632627 (1.037844738/10^13) discount406
    (by decide) (widths.2.2.2.2.2.2.1) (by simpa using widths.2.2.2.2.2.2.2) (widths.2.2.2.2.1) (by simpa using widths.2.2.2.2.2.1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_ofScientific] using h

end SigabaNeo.Wall1.ControlledPlane.LateEnclosures

#print axioms SigabaNeo.Wall1.ControlledPlane.LateEnclosures.positive394_sum
#print axioms SigabaNeo.Wall1.ControlledPlane.LateEnclosures.positive30_sum
#print axioms SigabaNeo.Wall1.ControlledPlane.LateEnclosures.horizontal406_sum
