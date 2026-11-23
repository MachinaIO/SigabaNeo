import SigabaNeo.Lib.Lattices.Research.Wall1.MordellBlichfeldtProfile

/-! Rational enclosures for the unconditional Hermite bounds through rank 24. -/
noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt
open Real BKZ

private def piLo : ℚ := 3.14159265358979323846
private def piHi : ℚ := 3.14159265358979323847

/-- Squared half-integral gamma values with the occurrence of π replaced by p. -/
private def gammaSq (p : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 9*p/16
  | n+2 => ((n:ℚ)/2+2)^2 * gammaSq p n

private theorem gammaSq_bounds (k : ℕ) :
    (gammaSq piLo k:ℝ) ≤ Gamma ((k:ℝ)/2+2)^2 ∧
    Gamma ((k:ℝ)/2+2)^2 ≤ (gammaSq piHi k:ℝ) := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [gammaSq,Gamma_two]
  | one =>
    have a := Gamma_add_one (show (3/2:ℝ) ≠ 0 by norm_num)
    have b := Gamma_add_one (show (1/2:ℝ) ≠ 0 by norm_num)
    norm_num at a b ⊢
    rw [a,b,Gamma_one_half_eq,mul_pow,mul_pow,sq_sqrt pi_pos.le]
    norm_num [gammaSq,piLo,piHi]
    constructor <;> linarith [pi_lt_d20,pi_gt_d20]
  | more k ih _ =>
    rw [show ((k+2:ℕ):ℝ)/2+2 = ((k:ℝ)/2+2)+1 by push_cast; ring,
      Gamma_add_one (by positivity), mul_pow]
    simpa [gammaSq] using And.intro (mul_le_mul_of_nonneg_left ih.1 (sq_nonneg ((k:ℝ)/2+2)))
      (mul_le_mul_of_nonneg_left ih.2 (sq_nonneg ((k:ℝ)/2+2)))

private theorem scaled_blichfeldt (k : ℕ) (hk : 0 < k) :
    (blichfeldtConstant k * π / 2)^k = Gamma ((k:ℝ)/2+2)^2 := by
  have h : (0:ℝ) < k := by exact_mod_cast hk
  rw [blichfeldtConstant,show 2/π * Gamma ((k:ℝ)/2+2)^(2/(k:ℝ)) * π/2 =
      Gamma ((k:ℝ)/2+2)^(2/(k:ℝ)) by field_simp,← rpow_mul_natCast (Gamma_pos_of_pos (by positivity)).le,
      div_mul_cancel₀ _ h.ne',rpow_two]

private def rows : Array (ℕ × ℕ) := #[
  (14142134,14142137), (15874006,15874015), (17817964,17817985), (19723411,19723414),
  (21070527,21070530), (22406463,22406466), (23732670,23732673), (25050323,25050326),
  (26360391,26360394), (27663680,27663683), (28960870,28960873), (30252539,30252542),
  (31539186,31539189), (32821241,32821244), (34099080,34099083), (35373033,35373036),
  (36643393,36643396), (37910417,37910420), (39174336,39174339), (40435359,40435362),
  (41693671,41693674)]

private def lo (k : ℕ) : ℚ := (rows[k-4]!.1:ℚ)/10^7
private def hi (k : ℕ) : ℚ := (rows[k-4]!.2:ℚ)/10^7

private theorem cert : ∀ n : Fin 20,
    let k := n.val + 5
    0 ≤ lo k ∧ 0 ≤ hi k ∧
    (lo k*piHi/2)^k ≤ gammaSq piLo k ∧ (lo k)^(n.val+3) ≤ (lo (k-1))^(n.val+4) ∧
    (gammaSq piHi k ≤ (hi k*piLo/2)^k ∨ (hi (k-1))^(n.val+4) ≤ (hi k)^(n.val+3)) := by
  decide +kernel

private theorem bounds (n : ℕ) (hn : n ≤ 20) :
    (lo (n+4):ℝ) ≤ gamma (n+4) ∧ gamma (n+4) ≤ (hi (n+4):ℝ) := by
  induction n with
  | zero =>
    have hp : gamma 4 ^ 4 = 4 := by
      change (exp (log 4/4))^4 = 4
      rw [← exp_nat_mul, show (4:ℕ)*(log 4 / 4) = log 4 by push_cast; ring, exp_log (by norm_num)]
    have hl : (lo 4)^4 ≤ 4 := by decide +kernel
    have hu : 4 ≤ (hi 4)^4 := by decide +kernel
    constructor
    · apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (gamma_pos _).le
      rw [hp]; exact_mod_cast hl
    · apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by norm_num [hi,rows])
      rw [hp]; exact_mod_cast hu
  | succ n ih =>
    let k := n+5
    obtain ⟨oldLo,oldHi⟩ := ih (by omega)
    obtain ⟨hl,hu,bl,ml,upper⟩ := cert ⟨n,by omega⟩
    change 0 ≤ lo k at hl
    change 0 ≤ hi k at hu
    have hl' : 0 ≤ (lo k:ℝ) := by exact_mod_cast hl
    have hu' : 0 ≤ (hi k:ℝ) := by exact_mod_cast hu
    have Bl : (lo k:ℝ) ≤ blichfeldtConstant k := by
      have cmp : ((lo k:ℝ)*π/2)^k ≤ (blichfeldtConstant k*π/2)^k := by
        rw [scaled_blichfeldt k (by dsimp [k]; omega)]
        apply le_trans _ (gammaSq_bounds k).1
        have H := (Rat.cast_le (K:=ℝ)).2 bl
        push_cast at H
        apply le_trans _ H
        apply pow_le_pow_left₀ (by positivity)
        gcongr
        exact pi_lt_d20.le
      have H := le_of_pow_le_pow_left₀ (show k ≠ 0 by dsimp [k]; omega)
        (by positivity [blichfeldtConstant_pos k]) cmp
      linarith only [le_of_mul_le_mul_right (by linarith only [H] :
        (lo k:ℝ)*π ≤ blichfeldtConstant k * π) pi_pos]
    let M := gamma (n+4)^(((n:ℝ)+4)/(n+3))
    have mp : 0 < M := rpow_pos_of_pos (gamma_pos _) _
    have power : M^(n+3) = gamma (n+4)^(n+4) := by
      dsimp [M]; rw [← rpow_mul_natCast (gamma_pos _).le]
      push_cast
      rw [div_mul_cancel₀ _ (by positivity),← Nat.cast_ofNat (R:=ℝ) (n:=4),← Nat.cast_add,rpow_natCast]
    change (lo k:ℝ) ≤ min (blichfeldtConstant k) M ∧ min _ M ≤ (hi k:ℝ)
    refine ⟨le_min Bl (le_of_pow_le_pow_left₀ (by omega : n+3 ≠ 0) mp.le ?_),?_⟩
    · rw [power]
      have oldNonneg : 0 ≤ (lo (n+4):ℝ) := by
        unfold lo; positivity
      apply le_trans _ (pow_le_pow_left₀ oldNonneg oldLo (n+4))
      exact_mod_cast ml
    · rcases upper with bu | mu
      · apply (min_le_left ..).trans
        have cmp : (blichfeldtConstant k*π/2)^k ≤ ((hi k:ℝ)*π/2)^k := by
          rw [scaled_blichfeldt k (by dsimp [k]; omega)]
          apply (gammaSq_bounds k).2.trans
          have H := (Rat.cast_le (K:=ℝ)).2 bu
          push_cast at H
          apply H.trans
          apply pow_le_pow_left₀ (by positivity [show (0:ℝ) ≤ (piLo:ℝ) by norm_num [piLo]])
          gcongr
          exact pi_gt_d20.le
        have H := le_of_pow_le_pow_left₀ (show k ≠ 0 by dsimp [k]; omega) (by positivity) cmp
        exact le_of_mul_le_mul_right (by linarith only [H] : blichfeldtConstant k * π ≤ (hi k:ℝ) * π) pi_pos
      · apply (min_le_right ..).trans
        apply le_of_pow_le_pow_left₀ (by omega : n+3 ≠ 0) hu'
        rw [power]
        apply (pow_le_pow_left₀ (gamma_pos _).le oldHi _).trans
        exact_mod_cast mu

/-- Rigorous rational intervals for the two Mordell steps and the three direct
Blichfeldt bounds used in the exceptional range (rank eight included). -/
theorem exceptional_enclosures :
    1.5874006 ≤ gamma 5 ∧ gamma 5 ≤ 1.5874015 ∧
    1.7817964 ≤ gamma 6 ∧ gamma 6 ≤ 1.7817985 ∧
    1.9723411 ≤ gamma 7 ∧ gamma 7 ≤ 1.9723414 ∧
    2.1070527 ≤ gamma 8 ∧ gamma 8 ≤ 2.1070530 ∧
    4.1693671 ≤ gamma 24 ∧ gamma 24 ≤ 4.1693674 := by
  have h5 := bounds 1 (by decide)
  have h6 := bounds 2 (by decide)
  have h7 := bounds 3 (by decide)
  have h8 := bounds 4 (by decide)
  have h24 := bounds 20 (by decide)
  norm_num [lo,hi,rows] at h5 h6 h7 h8 h24 ⊢
  exact ⟨h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2,h24⟩

open TerminalProjection.TerminalInterval Finset

/-- At rank five the radius from unconditional peeling already exceeds the old
running maximum. This compares majorants and does not assert sharpness of either. -/
theorem rank_five_radius_gap :
    log (flagCap 5) ≤ 0.448 ∧ 0.47 < log (gamma 5)/2 + penalty 5 := by
  constructor
  · apply (FlagEnvelope.log_flagCap 5 (by decide)).trans
    have H := (Rat.cast_le (K:=ℝ)).2 (show FlagEnvelope.logCap 5 ≤ (0.448:ℚ) by decide +kernel)
    norm_num at H ⊢
    exact H
  have b₂ : 0.28 ≤ log (4/3) := by
    apply (le_log_iff_exp_le (by norm_num)).2
    have H := exp_upper 0.28 (4/3) (by norm_num) (by norm_num) (by decide +kernel)
    norm_num at H ⊢
    exact H
  have b₅ : 0.46 ≤ log (gamma 5) := by
    apply (le_log_iff_exp_le (gamma_pos 5)).2
    have H := exp_upper 0.46 1.585 (by norm_num) (by norm_num) (by decide +kernel)
    norm_num at H ⊢
    linarith [exceptional_enclosures.1]
  have h₂ : log (gamma 2) = log (4/3)/2 := log_exp _
  have h₃ : log (gamma 3) = log 2/3 := log_exp _
  have h₄ : log (gamma 4) = log 4/4 := log_exp _
  rw [show (4:ℝ) = 2^2 by norm_num,log_pow] at h₄
  have hI : Icc 2 5 = ({2,3,4,5}:Finset ℕ) := by decide
  simp [penalty,hI,h₂,h₃,h₄]
  norm_num at *
  linarith [log_two_gt_d9]

end SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt

#print axioms SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt.exceptional_enclosures
#print axioms SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt.rank_five_radius_gap
