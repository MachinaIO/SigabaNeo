import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixMordell

/-! Hermite peeling with unconditional rank-by-rank constants. -/

noncomputable section

namespace SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt
open Real Finset BKZ TerminalProjection

/-- Use the proved binary, ternary, and quaternary bounds. At each higher rank
choose the smaller of the direct Blichfeldt bound and the preceding Mordell step. -/
def gamma : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => flagGamma 2
  | 3 => flagGamma 3
  | 4 => flagGamma 4
  | n+5 => min (blichfeldtConstant (n+5)) (gamma (n+4) ^ (((n:ℝ)+4)/(n+3)))

theorem gamma_pos (k : ℕ) : 0 < gamma k := by
  match k with
  | 0 | 1 => exact zero_lt_one
  | 2 | 3 | 4 => norm_num [gamma,flagGamma,auditedGamma]; positivity
  | n+5 => exact lt_min (blichfeldtConstant_pos _) (rpow_pos_of_pos (gamma_pos (n+4)) _)

/-- The selected bound controls every independent family, in any ambient dimension. -/
theorem family (k : ℕ) (hk : 2 ≤ k) : FamilyHermite k (gamma k) := by
  match k with
  | 0 | 1 => omega
  | 2 => rw [gamma]; exact @familyHermite_two
  | 3 => rw [gamma]; exact @familyHermite_three
  | 4 => rw [gamma]; exact @familyHermite_four
  | n+5 =>
    let : NeZero (n+5) := ⟨by omega⟩
    have H : FamilyHermite (n+5) (gamma (n+4) ^ (((n+4:ℕ):ℝ)/(((n+4:ℕ):ℝ)-1))) := familyHermite_of_intrinsic
      (intrinsic_mordell (k := n+4) (by omega) (gamma_pos _) (family (n+4) (by omega)))
    have E : ((n+4:ℕ):ℝ)/(((n+4:ℕ):ℝ)-1) = ((n:ℝ)+4)/(n+3) := by push_cast; ring_nf
    rw [E] at H
    change FamilyHermite (n+5) (min _ _)
    rcases le_total (blichfeldtConstant (n+5)) (gamma (n+4) ^ (((n:ℝ)+4)/(n+3))) with h | h
    · rw [min_eq_left h]; exact @familyHermite_blichfeldt (n+5) _
    · rw [min_eq_right h]; exact @H

/-- Accumulated log penalty in the normalized geometric mean. -/
def penalty (l : ℕ) : ℝ := ∑ r ∈ Icc 2 l, log (gamma r) / (2*((r:ℝ)-1))

/-- Peeling for an arbitrary sequence satisfying the log Hermite inequalities.
The reference length is the terminal length itself. -/
theorem peel {a : ℕ → ℝ} {m : ℕ} (cap : ∀ k, 2 ≤ k → k ≤ m →
    a k ≤ log (gamma k)/2 + (∑ r ∈ Icc 1 k, a r)/(k:ℝ)) {l : ℕ}
    (hl : 1 ≤ l) (hm : l ≤ m) :
    a l ≤ a 1 + log (gamma l)/2 + penalty l := by
  have mean (k : ℕ) (lo : 1 ≤ k) (hi : k ≤ m) :
      (∑ r ∈ Icc 1 k, a r)/(k:ℝ) ≤ a 1 + penalty k := by
    induction k with
    | zero => omega
    | succ n ih =>
      by_cases h : n = 0
      · subst n; simp [penalty]
      have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0 < (n:ℝ)+1 := by positivity
      have old := ih (by omega) (by omega)
      have next := cap (n+1) (by omega) hi
      rw [sum_Icc_succ_top (by omega),Nat.cast_succ] at next ⊢
      have hpen : penalty (n+1) = penalty n + log (gamma (n+1))/(2*(n:ℝ)) := by
        unfold penalty; rw [sum_Icc_succ_top (by omega),Nat.cast_succ]; ring_nf
      rw [hpen,← add_assoc]
      apply le_trans _ (add_le_add_left old _)
      field_simp [hn.ne',hp.ne'] at next ⊢
      nlinarith
  by_cases h : l = 1
  · subst l; simp [gamma,penalty]
  linarith [cap l (by omega) hm, mean l hl hm]

/-- Absolute radius bound, relative to the observed terminal length, for every
successive-shortest-vector quotient flag. No exceptional-rank input is needed. -/
theorem suffix_length {n d : ℕ} (m : ℕ) (s : ChainState n (CoordSpace (d+1+m)))
    {l : ℕ} (hl : 1 ≤ l) (hm : l ≤ m+1) :
    suffixLength m s l ≤ suffixLength m s 1 * exp (log (gamma l)/2 + penalty l) := by
  let a (r : ℕ) := log (suffixLength m s r)
  have cap (k : ℕ) (lo : 2 ≤ k) (hi : k ≤ m+1) :
      a k ≤ log (gamma k)/2 + (∑ r ∈ Icc 1 k, a r)/(k:ℝ) := by
    have h := suffix_hermite m s k lo hi (family k lo)
    have pos := suffixLength_pos m s
    have pp := prod_pos (s := Icc 1 k) (fun i _ ↦ pos i)
    have H := log_le_log (sq_pos_of_pos (pos k)) h
    rw [log_pow,log_mul (gamma_pos _).ne' (rpow_pos_of_pos pp _).ne',log_rpow pp,
      log_prod (fun i _ ↦ (pos i).ne')] at H
    have hk : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    dsimp only [a]
    field_simp [hk.ne'] at H ⊢
    norm_num at H
    linarith
  have H := exp_le_exp.mpr (peel cap hl hm)
  rw [add_assoc,exp_add] at H
  simpa only [a,exp_log (suffixLength_pos ..)] using H

end SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt

#print axioms SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt.family
#print axioms SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt.peel
#print axioms SigabaNeo.Wall1.ControlledPlane.MordellBlichfeldt.suffix_length
