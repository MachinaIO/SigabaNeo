import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledPrefixCap31
import SigabaNeo.Lib.Lattices.Research.Wall1.HermiteSphereCertificate506

/-! The sharp physical determinant floor, direct prefix descent, and the remaining
case of an inherited projected line after a horizontal draw. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open TerminalProjection TerminalProjection.Restart506 TerminalProjection.ChainState
open DualExit Real Finset BKZ

local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem retained_floor_all (h : History) (i : ℕ) (hi : i < 406) :
    exp (terminalLogFloor i) ≤ ZLattice.covolume (retained h i).M := by
  by_cases early : i ≤ 20
  · exact retained_floor_first20 h i early
  · exact HermiteWitness506.Sphere.laterDeterminantFloor h ⟨i,hi⟩ (show 20 < i by omega)

theorem coverage_first31 (A : Sample) (t : ℕ) (ht : t ≤ 31)
    (hs : ‖(retained (history A) t).winner‖ ≤ planeRadius) :
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
      ∃ u, flagTest flagRadius flagFloor u (history A) := by
  apply coverage_of_descent_caps A t (by omega) _ (fun _ hi ↦ retained_floor_all _ _ (by omega)) hs
  exact fun _ hi ↦ PrefixCap.descent_cap ht hi

private theorem two_cap {k : ℕ} (hk : 2 ≤ k) : 2 / √3 ≤ flagCap k := by
  have mono : Monotone flagCap := monotone_nat_of_le_succ fun _ ↦ le_max_left ..
  apply le_trans _ (mono hk)
  apply le_trans _ (le_max_right ..)
  have g : flagGamma 2 = 2 / √3 := by
    norm_num [flagGamma,auditedGamma,hermitePower]
    rw [div_eq_mul_inv,← rpow_def_of_pos (by norm_num : (0:ℝ)<4/3),← one_div,← sqrt_eq_rpow,
      sqrt_div (by norm_num)]
    norm_num
  rw [show Icc 2 (1+1) = {2} by decide,prod_singleton]
  norm_num only [Nat.cast_ofNat,show 1/(2*((2:ℝ)-1))=1/2 by norm_num]
  rw [← sqrt_eq_rpow,← sq,sq_sqrt (g ▸ by positivity),g]

/-- Every draw through 154 with a short retained winner already triggers its original
zero-skip flag unless the draw is horizontal and the old projection is short. -/
theorem flag_or_inherited (h : History) (i : ℕ) (hi : i < 154)
    (hs : ‖(retained h (i+1)).winner‖ ≤ planeRadius) :
    flagTest flagRadius flagFloor ⟨⟨i,hi⟩,⟨0,by omega⟩⟩ h ∨
      horizontalWinner h i ∧
        ShortProjection (retained h i).M (retained h i).winner planeRadius := by
  let s := retained h i
  let c := past h (105+i)
  let w := (s.append c).winner
  let u : FlagIndex := ⟨⟨i,hi⟩,⟨0,by omega⟩⟩
  have sh := (retained h (i+1)).shortest
  have hx : ∃ y ∈ (incoming s c).freeze.M, y ≠ 0 ∧ ‖y‖ ≤ planeRadius := ⟨_,sh.1,sh.2.1,hs⟩
  rw [freeze_test,incoming,reframe_winner,reframe_shortProjection] at hx
  have hit (hp : PositiveHit s.M (columnLift s.g c) (2*planeRadius/√3)) :
      flagTest flagRadius flagFloor u h := by
    refine flagTest_of_lengths u h ((le_log_iff_exp_le (ZLattice.covolume_pos _ _)).2
      (retained_floor_all h i (by omega))) trivial ?_
    obtain ⟨z,hz,hp,hl⟩ := hp
    exact ⟨z,hz,hp,hl.trans (by
      change 2*planeRadius/√3 ≤ planeRadius * flagCap (155-i-0)
      rw [mul_comm 2, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (two_cap (by omega)) (sqrt_nonneg _))⟩
  by_cases hor : w.snd = 0
  · by_cases old : ShortProjection s.M s.winner planeRadius
    · right
      exact ⟨by simpa [horizontalWinner,window,incoming,reframe_winner,w,s,c] using hor,old⟩
    · left
      apply hit
      have tie : HorizontalAgreement s.winner w :=
        agreement_of_order (s.append c).key (s.append c).key_injective s.shortest (s.append c).shortest
          (fun a ha ↦ s.key_horizontal_le c ((chosen_spec s.key s.M s.nonbot).2 a ha))
          (chosen_spec (s.append c).key (s.append c).M (s.append c).nonbot).2
      exact discrepancy s.shortest (s.append c).shortest tie (fun hc ↦ old (hc.mp hx))
  · left
    apply hit
    obtain ⟨z,hz,hn,hr⟩ := (shortProjection_iff ..).mp hx
    obtain ⟨_,_,_,_,hw,_⟩ := rounded_witness (s.append c).shortest hz hn hr
    rcases lt_or_gt_of_ne hor with neg | pos
    · exact ⟨-w,(s.append c).M.neg_mem (s.append c).shortest.1,neg_pos.mpr neg,by simpa using hw⟩
    · exact ⟨w,(s.append c).shortest.1,pos,hw⟩

/-- The remaining case has two old directions in the last window: the horizontal
winner and a nonzero short vector in its old quotient. Here draw i+1 is one-based. -/
def InheritedPrefixCoverage : Prop :=
  ∀ (A : Sample) (i : ℕ), 31 ≤ i → i < 154 →
    ‖(retained (history A) (i+1)).winner‖ ≤ planeRadius →
    horizontalWinner (history A) i →
    ShortProjection (retained (history A) i).M (retained (history A) i).winner planeRadius →
    rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
      ∃ u, flagTest flagRadius flagFloor u (history A)

theorem coverage_iff_inherited : LastCoordinateCoverage ↔ InheritedPrefixCoverage := by
  constructor
  · exact fun full A i _ hi hs _ _ ↦ full A (i+1) (by omega) (by omega) hs
  · intro rest A t ht top hs
    by_cases early : t ≤ 31
    · exact coverage_first31 A t early hs
    · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      rcases flag_or_inherited _ i (by omega) hs with flag | ⟨hor,old⟩
      · exact .inr ⟨_,flag⟩
      · exact rest A i (by omega) (by omega) hs hor old

theorem terminal_bound_of_inherited (lift : InheritedPrefixCoverage) :
    probability terminalHit < probability residual₁ + probability residual₂ + 6.515/(10:ℝ)^12 :=
  terminal_bound_of_coverage_floor (coverage_iff_inherited.mpr lift)
    HermiteWitness506.Sphere.laterDeterminantFloor

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.retained_floor_all
#print axioms SigabaNeo.Wall1.ControlledPlane.coverage_first31
#print axioms SigabaNeo.Wall1.ControlledPlane.flag_or_inherited
#print axioms SigabaNeo.Wall1.ControlledPlane.coverage_iff_inherited
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_bound_of_inherited
